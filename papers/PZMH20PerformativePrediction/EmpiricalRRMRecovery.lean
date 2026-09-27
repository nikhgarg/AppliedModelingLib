import PZMH20PerformativePrediction.EmpiricalMinimizerPerturbation
import PZMH20PerformativePrediction.LogarithmicBurnIn

/-!
# Empirical repeated risk minimization under Wasserstein error

For a realized heterogeneous empirical-RRM trajectory, an empirical `W₁`
error contributes linearly to the next-iterate error.  Combining that
perturbation estimate with distributional sensitivity gives the recurrence

`dₜ₊₁ ≤ (ε β / γ) dₜ + (β / γ) W₁(\hat Dₜ, D(θₜ))`.

On the event where every empirical error is at most `ε δ`, this is the
two-region recurrence used in the source proof: outside the `δ`-ball the
distance contracts by `2 ε β / γ`, while inside that ball it remains there.
The proof uses only constrained empirical minimization, the on-domain A1/A2
conditions, loss integrability, and finite first-moment transport witnesses.
It does not differentiate an expected loss.
-/

namespace PZMH20PerformativePrediction.EmpiricalRRMRecovery

open AppliedModelingLib MeasureTheory
open scoped InnerProductSpace

variable {Parameter Data : Type*}
variable [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
variable [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
variable [OpensMeasurableSpace Data] [SecondCountableTopology Data]

/-- One realized empirical-RRM step obeys the source's linear Wasserstein
perturbation recurrence.  The first transport compares the empirical law with
the current population law; the second compares the current and stable
population laws. -/
theorem dist_next_le_contraction_add_empiricalWasserstein
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hsmoothness : smoothness ≠ 0)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong :
      EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
        model.loss gradient domain modulus)
    (sampleCount : ℕ → ℕ) (hcountPositive : ∀ iteration, 0 < sampleCount iteration)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (sampleCount round)) Data iteration → Parameter)
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn
      model domain sampleCount hcountPositive deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable)
    {sensitivity : ℝ} (hsensitive :
      AppliedModelingLib.IsMeasureWassersteinSensitiveOn model domain sensitivity)
    (iteration : ℕ)
    (history : HeterogeneousBatchTrace
      (fun round => Fin (sampleCount round)) Data iteration)
    (batch : Fin (sampleCount iteration) → Data)
    (hcurrent : deployedOfHistory iteration history ∈ domain)
    (hempiricalIntegrable : ∀ candidate ∈ domain,
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos
          (hcountPositive iteration) batch : Measure Data))
    {wassersteinError : ℝ} (herrorNonneg : 0 ≤ wassersteinError)
    (hWasserstein : ProbabilityCoupling.wassersteinOne
      (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch)
      (model.dataLaw (deployedOfHistory iteration history)) ≤
        ENNReal.ofReal wassersteinError) :
    dist
        (deployedOfHistory (iteration + 1)
          (heterogeneousBatchTraceSnoc history batch)) stable ≤
      (sensitivity * (smoothness : ℝ) / modulus) *
          dist (deployedOfHistory iteration history) stable +
        (smoothness : ℝ) / modulus * wassersteinError := by
  let current := deployedOfHistory iteration history
  let next := deployedOfHistory (iteration + 1) (heterogeneousBatchTraceSnoc history batch)
  have hempiricalMin := hempirical iteration history batch
  have hpopulationMin := hpopulation current hcurrent
  have hnextPopulation : ‖next - populationUpdate current‖ ≤
      (smoothness : ℝ) / modulus * wassersteinError := by
    apply EmpiricalMinimizerPerturbation.norm_empiricalMinimizer_sub_populationMinimizer_le_of_wassersteinOne
      (hcountPositive iteration) batch (model.dataLaw current) model.loss gradient
      domain hconvex smoothness hsmoothness hgradient hdata hmodulus hstrong
      hempiricalIntegrable (fun candidate _ => model.loss_integrable current candidate)
      next (populationUpdate current)
    · exact hempiricalMin.1
    · exact hpopulationMin.1
    · intro candidate hcandidate
      simpa [EmpiricalMinimizerPerturbation.expectedRisk,
        measureEmpiricalDecoupledPerformativeRisk] using
        hempiricalMin.2 candidate hcandidate
    · intro candidate hcandidate
      simpa [EmpiricalMinimizerPerturbation.expectedRisk,
        measureDecoupledPerformativeRisk] using
        hpopulationMin.2 candidate hcandidate
    · exact herrorNonneg
    · exact hWasserstein
  rcases hsensitive current hcurrent stable hstable.1 with
    ⟨hfinitePopulation, hpopulationWasserstein⟩
  have hpopulationStable : ‖populationUpdate current - stable‖ ≤
      (smoothness : ℝ) / modulus *
        ProbabilityCoupling.wassersteinOneReal
          (model.dataLaw current) (model.dataLaw stable) hfinitePopulation := by
    apply EmpiricalMinimizerPerturbation.norm_minimizers_sub_le_wasserstein
      (model.dataLaw current) (model.dataLaw stable) model.loss gradient
      domain hconvex smoothness hgradient hdata hmodulus hstrong
      (fun candidate _ => model.loss_integrable current candidate)
      (fun candidate _ => model.loss_integrable stable candidate)
      (populationUpdate current) stable hpopulationMin.1 hstable.1
    · intro candidate hcandidate
      simpa [EmpiricalMinimizerPerturbation.expectedRisk,
        measureDecoupledPerformativeRisk] using
        hpopulationMin.2 candidate hcandidate
    · intro candidate hcandidate
      simpa [EmpiricalMinimizerPerturbation.expectedRisk,
        measureDecoupledPerformativeRisk] using hstable.2 candidate hcandidate
  have hpopulationStable' : ‖populationUpdate current - stable‖ ≤
      (smoothness : ℝ) / modulus *
        (sensitivity * dist current stable) :=
    hpopulationStable.trans
      (mul_le_mul_of_nonneg_left hpopulationWasserstein (by positivity))
  change dist next stable ≤
    (sensitivity * (smoothness : ℝ) / modulus) * dist current stable +
      (smoothness : ℝ) / modulus * wassersteinError
  rw [dist_eq_norm]
  calc
    ‖next - stable‖ ≤ ‖next - populationUpdate current‖ +
        ‖populationUpdate current - stable‖ := by
      rw [show next - stable =
        (next - populationUpdate current) + (populationUpdate current - stable) by abel]
      exact norm_add_le _ _
    _ ≤ (smoothness : ℝ) / modulus * wassersteinError +
        (smoothness : ℝ) / modulus * (sensitivity * dist current stable) :=
      add_le_add hnextPopulation hpopulationStable'
    _ = _ := by ring

/-- The deterministic Appendix-E.4 recovery on a fixed infinite adaptive
trace.  If every realized empirical law is within `ε δ` in extended `W₁` of its
current population law and `ε < γ / (2 β)`, the trajectory enters the
`δ`-ball by the source logarithmic threshold and never leaves it. -/
theorem dist_heterogeneousMeasureRERMState_le_radius_after_of_wassersteinOne_goodTrace
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong :
      EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
        model.loss gradient domain modulus)
    (sampleCount : ℕ → ℕ) (hcountPositive : ∀ iteration, 0 < sampleCount iteration)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (sampleCount round)) Data iteration → Parameter)
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn
      model domain sampleCount hcountPositive deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable)
    {sensitivity radius : ℝ} (hsensitivityNonneg : 0 ≤ sensitivity)
    (hsmoothnessPos : 0 < (smoothness : ℝ))
    (hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ)))
    (hsensitive : AppliedModelingLib.IsMeasureWassersteinSensitiveOn
      model domain sensitivity)
    (hradius : 0 < radius)
    (hinitial : ∀ history :
      HeterogeneousBatchTrace (fun round => Fin (sampleCount round)) Data 0,
      deployedOfHistory 0 history ∈ domain)
    (hempiricalIntegrable : ∀ iteration
      (batch : Fin (sampleCount iteration) → Data) candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos
          (hcountPositive iteration) batch : Measure Data))
    (bad : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (sampleCount round)) Data iteration →
      (Fin (sampleCount iteration) → Data) → Prop)
    (hgood : ∀ iteration history batch, ¬ bad iteration history batch →
      ProbabilityCoupling.wassersteinOne
          (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch)
          (model.dataLaw (deployedOfHistory iteration history)) ≤
        ENNReal.ofReal (sensitivity * radius))
    (trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
      (fun round => Fin (sampleCount round)) Data i)
    (hgoodTrace : trace ∉ ⋃ round,
      adaptiveFreshHeterogeneousInfiniteTraceBadEvent
        (fun round => Fin (sampleCount round)) bad round)
    (entryIteration : ℕ)
    (hentry : Real.log
        (dist (deployedOfHistory 0
          (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / radius) /
        (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
          (entryIteration : ℝ)) :
    ∀ iteration, entryIteration ≤ iteration →
      dist (deployedOfHistory iteration
        (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ radius := by
  let factor : ℝ := sensitivity * (smoothness : ℝ) / modulus
  let distance : ℕ → ℝ := fun round =>
    dist (deployedOfHistory round
      (heterogeneousBatchTraceOfInfiniteTrace round trace)) stable
  have hfactor :=
    AppliedModelingLib.Optimization.contraction_ratio_nonneg_lt_half_of_lt_modulus_div_two_smoothness
        hsensitivityNonneg hsmoothnessPos hmodulus hsensitivitySmall
  have hfactorNonneg : 0 ≤ factor := by simpa only [factor] using hfactor.1
  have hfactorHalf : factor < 1 / 2 := by simpa only [factor] using hfactor.2
  have hdomain : ∀ round
      (history : HeterogeneousBatchTrace
        (fun index => Fin (sampleCount index)) Data round),
      deployedOfHistory round history ∈ domain := by
    intro round history
    induction round with
    | zero => exact hinitial history
    | succ round _ =>
        have hminimizer := hempirical round
          (heterogeneousBatchTraceInit
            (BatchIndex := fun index => Fin (sampleCount index)) history)
          (heterogeneousBatchTraceLast
            (BatchIndex := fun index => Fin (sampleCount index)) history)
        simpa only [heterogeneousBatchTraceSnoc_init_last] using hminimizer.1
  have hrecurrence : ∀ round,
      distance (round + 1) ≤ factor * distance round + factor * radius := by
    intro round
    let history : HeterogeneousBatchTrace
        (fun index => Fin (sampleCount index)) Data round :=
      heterogeneousBatchTraceOfInfiniteTrace round trace
    let batch : Fin (sampleCount round) → Data := trace (round + 1)
    have hbatch : ¬ bad round history batch := by
      simpa only [history, batch] using
        (not_adaptiveFreshHeterogeneousInfiniteTraceBadEvent_of_not_iUnion
          bad trace round hgoodTrace)
    have hsnoc : heterogeneousBatchTraceSnoc history batch =
        heterogeneousBatchTraceOfInfiniteTrace (round + 1) trace := by
      rw [← heterogeneousBatchTraceSnoc_init_last
        (heterogeneousBatchTraceOfInfiniteTrace (round + 1) trace)]
      congr
    have hstep := dist_next_le_contraction_add_empiricalWasserstein
      model gradient domain hconvex smoothness (ne_of_gt hsmoothnessPos) hgradient hdata
      hmodulus hstrong
      sampleCount hcountPositive deployedOfHistory hempirical populationUpdate hpopulation
      stable hstable hsensitive round history batch (hdomain round history)
      (hempiricalIntegrable round batch)
      (mul_nonneg hsensitivityNonneg hradius.le)
      (hgood round history batch hbatch)
    rw [hsnoc] at hstep
    change distance (round + 1) ≤ factor * distance round + factor * radius
    change dist (deployedOfHistory (round + 1)
        (heterogeneousBatchTraceOfInfiniteTrace (round + 1) trace)) stable ≤
      factor * dist (deployedOfHistory round history) stable + factor * radius
    calc
      dist (deployedOfHistory (round + 1)
          (heterogeneousBatchTraceOfInfiniteTrace (round + 1) trace)) stable ≤
          (sensitivity * (smoothness : ℝ) / modulus) *
              dist (deployedOfHistory round history) stable +
            (smoothness : ℝ) / modulus *
              (sensitivity * radius) := hstep
      _ = factor * dist (deployedOfHistory round history) stable + factor * radius := by
        dsimp only [factor]
        ring
  have houtside : ∀ round, radius < distance round →
      distance (round + 1) ≤ (2 * factor) * distance round := by
    intro round hout
    calc
      distance (round + 1) ≤ factor * distance round + factor * radius :=
        hrecurrence round
      _ ≤ factor * distance round + factor * distance round := by
        gcongr
      _ = (2 * factor) * distance round := by ring
  have hinside : ∀ round, distance round ≤ radius →
      distance (round + 1) ≤ radius := by
    intro round hin
    calc
      distance (round + 1) ≤ factor * distance round + factor * radius :=
        hrecurrence round
      _ ≤ factor * radius + factor * radius := by gcongr
      _ = (2 * factor) * radius := by ring
      _ ≤ 1 * radius := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact hradius.le
      _ = radius := one_mul radius
  apply PZMH20PerformativePrediction.two_phase_contraction_enters_and_stays_of_log_bound
      (distance := distance) (contraction := 2 * factor) (radius := radius)
  · positivity
  · linarith
  · exact dist_nonneg
  · exact hradius
  · exact houtside
  · exact hinside
  · simpa only [distance, factor] using hentry

end PZMH20PerformativePrediction.EmpiricalRRMRecovery
