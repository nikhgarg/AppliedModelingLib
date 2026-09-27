import PZMH20PerformativePrediction.EmpiricalRRMAllDimensionalRecovery
import PZMH20PerformativePrediction.CriticalDimensionSampleCountRates

/-!
# Raw Wasserstein premises for the sharp critical schedule

The dimension-two selected-shell certificate is converted to the raw empirical
`W₁` event used by empirical RRM.  This is a concentration-to-recurrence
bridge: it does not assume a loss-Lipschitz transport argument.
-/

namespace PZMH20PerformativePrediction.EmpiricalRRMCriticalDimensionRecovery

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

/-- The sharp critical schedule with the decay exponent written in the form
used by the selected-shell certificate. -/
noncomputable def criticalDimensionRawRateCountSchedule
    (eta alpha gamma tailBound radius p : ℝ) : ℕ → ℕ := fun round =>
  criticalDimensionAllShellEffectiveCount
    (Probability.pOneFournierGuillinHeadCutoff eta radius)
    eta alpha gamma tailBound
    (radius / Real.rpow 2 (-eta - 1)) radius
    (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
    radius (theorem310FailureBudget p round / 2)

theorem criticalDimensionRawRateCountSchedule_pos
    (eta alpha gamma tailBound radius p : ℝ) (round : ℕ) :
    0 < criticalDimensionRawRateCountSchedule eta alpha gamma tailBound radius p round := by
  unfold criticalDimensionRawRateCountSchedule
  exact lt_of_lt_of_le zero_lt_one
    (one_le_criticalDimensionAllShellEffectiveCount
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound (radius / Real.rpow 2 (-eta - 1)) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2))

theorem criticalDimensionRawRateCountSchedule_eq_rate
    (eta alpha gamma tailBound radius p : ℝ) (round : ℕ) :
    criticalDimensionRawRateCountSchedule eta alpha gamma tailBound radius p round =
      criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round := by
  have hneg : -(1 + eta) = -eta - 1 := by ring
  unfold criticalDimensionRawRateCountSchedule criticalDimensionRateCountSchedule
  rw [hneg]

/-- The sharp raw schedule inherits the checked critical-dimensional rate. -/
theorem criticalDimensionRawRateCountSchedule_le
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    (criticalDimensionRawRateCountSchedule eta alpha gamma tailBound radius p round : ℝ) ≤
      2 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          theorem310ShiftedRoundLog p round := by
  rw [criticalDimensionRawRateCountSchedule_eq_rate]
  exact criticalDimensionRateCountSchedule_le heta halphaGap hgamma htailBound
    hradius hradius_le_one hsmall hp hp_le_one round

/- The local route uses the certificate-normalized spelling of the same sharp
schedule, while `criticalDimensionRawRateCountSchedule_eq_rate` preserves its
connection to the published rate declaration above. -/
noncomputable def criticalDimensionRateCountSchedule
    (eta alpha gamma tailBound radius p : ℝ) : ℕ → ℕ :=
  criticalDimensionRawRateCountSchedule eta alpha gamma tailBound radius p

theorem criticalDimensionRateCountSchedule_pos
    (eta alpha gamma tailBound radius p : ℝ) (round : ℕ) :
    0 < criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round :=
  criticalDimensionRawRateCountSchedule_pos eta alpha gamma tailBound radius p round

/-- The sharp dimension-two count supplies the roundwise raw-`W₁` failure
budget and deterministic threshold needed by the direct empirical-RRM
recurrence.  Its raw deviation is the source scaled radius divided by the
fixed dyadic decay factor. -/
theorem exists_pOneFournierGuillinAdaptiveEuclideanWassersteinOnePremises_criticalDimensionRateCountSchedule
    {eta alpha gamma momentBound tailBound radius : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hradius_pos : 0 < radius) (hradius_le_one : radius ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p : ℝ) (hp : 0 < p)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (htailBound_moment :
      tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    {wassersteinBound : ℝ}
    (hbudget : Real.sqrt 2 * (radius / Real.rpow 2 (-eta - 1)) +
      (2 * Real.sqrt 2) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^
          Probability.pOneFournierGuillinHeadCutoff eta radius) + radius ≤
          wassersteinBound)
    (law : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound
          radius p round))
        (EuclideanSpace ℝ (Fin 2)) iteration → ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)))
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment (law iteration history)
        alpha gamma momentBound) :
    ∃ gateScale : ℕ,
      radius ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
        (∀ iteration history,
          (Probability.finiteIIDSampleLaw
            (law iteration history : Measure (EuclideanSpace ℝ (Fin 2)))
            (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p iteration)).real
            {batch |
              pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
                2 (Probability.pOneFournierGuillinHeadCutoff eta radius)
                alpha gamma momentBound (radius / Real.rpow 2 (-eta - 1))
                (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
                (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
                (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p)
                law iteration history batch} ≤ theorem310FailureBudget p iteration) ∧
        ∀ iteration history,
          pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold
            2 (Probability.pOneFournierGuillinHeadCutoff eta radius)
            alpha gamma momentBound (radius / Real.rpow 2 (-eta - 1))
            (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
            (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
            law iteration history ≤ ENNReal.ofReal wassersteinBound := by
  let decay : ℝ := Real.rpow 2 (-eta - 1)
  have hdecay_pos : 0 < decay := Real.rpow_pos_of_pos (by norm_num) _
  have hdeviation_pos : 0 < radius / decay := div_pos hradius_pos hdecay_pos
  have hneg_exponent : -(1 + eta) = -eta - 1 := by ring
  have hdecay_eq : Real.rpow 2 (-(1 + eta)) = Real.rpow 2 (-eta - 1) :=
    congrArg (Real.rpow 2) hneg_exponent
  have hscaled : radius = (radius / decay) * decay := by field_simp [hdecay_pos.ne']
  have hconfidence_pos : ∀ round, 0 < theorem310FailureBudget p round := by
    intro round
    unfold theorem310FailureBudget
    positivity
  obtain ⟨gateScale, hcertificate⟩ :=
    exists_pOneFournierGuillin_uniformSelectedShellPartitionCertificate_criticalDimensionConcreteCountSchedule
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap
      (by simpa [decay] using hscaled) hradius_pos hradius_le_one
      htailBound_pos htailEnvelope (theorem310FailureBudget p) (fun _ => radius)
      hconfidence_pos (fun _ => hradius_pos) (fun _ => hsmall)
  refine ⟨gateScale, fun hgate => ⟨?_, ?_⟩⟩
  · intro iteration history
    obtain ⟨_hcompact, hselected⟩ :=
      hcertificate hgate iteration (law iteration history) (hmoment iteration history)
    refine _root_.PZMH20PerformativePrediction.EmpiricalRRMAllDimensionalRecovery.measureReal_pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent_le_of_selectedShellPartitionCertificate
      2 (Probability.pOneFournierGuillinHeadCutoff eta radius) eta alpha gamma momentBound
        (radius / Real.rpow 2 (-eta - 1))
        (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
        (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
        (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p)
        law iteration history (by norm_num)
        (Math.expConfidenceForHalfBudget_nonneg _) heta_pos hdeviation_pos.le
        (by linarith [heta_pos, halpha_gap]) hgamma_pos
        (hmoment iteration history).hasExponentialRadialMoment ?_ ?_
    · apply Probability.selectedShellGeometricCompactHeadBudget_le_headSchedule_byDimension_of_boundedMoment
        2 (Probability.pOneFournierGuillinHeadCutoff eta radius)
        (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p iteration)
        (by norm_num) (law iteration history)
        (alpha := alpha) (gamma := gamma)
        (confidence := Math.expConfidenceForHalfBudget (theorem310FailureBudget p iteration))
        (momentBound := momentBound)
      · exact criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p iteration
      · exact Math.expConfidenceForHalfBudget_nonneg _
      · linarith [heta_pos, halpha_gap]
      · exact hgamma_pos
      · exact hmoment iteration history
    · simpa only [criticalDimensionRateCountSchedule,
        criticalDimensionRawRateCountSchedule,
        criticalDimensionAllShellConcreteCountSchedule,
        pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule,
        pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent] using hselected
  · intro iteration history
    apply pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold_le_of_tail_headBudget
      2 (Probability.pOneFournierGuillinHeadCutoff eta radius)
      alpha gamma momentBound (radius / decay)
      (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
      (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
      law iteration history tailBound radius wassersteinBound hdeviation_pos.le
    · exact (Probability.fifthOrderExponentialRadialTailConstant_pos
        (law iteration history) hgamma_pos
        (hmoment iteration history).hasExponentialRadialMoment).le
    · exact htailEnvelope _ (hmoment iteration history)
    · exact hradius_pos.le
    · simpa [Probability.selectedShellGeometricHeadSchedule_byDimension,
        criticalDimensionRateCountSchedule,
        pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule,
        htailBound_moment, decay] using
        (selectedShellGeometricHeadSchedule_dimensionTwo_le_of_criticalAllShellCount
          (Probability.pOneFournierGuillinHeadCutoff eta radius)
          (eta := eta) (alpha := alpha) (gamma := gamma)
          (deviation := radius / decay) (scaledDeviation := radius)
          (confidence := Math.expConfidenceForHalfBudget (theorem310FailureBudget p iteration))
          (tolerance := theorem310FailureBudget p iteration / 2)
          hradius_pos hsmall)
    · simpa [decay] using hbudget

/-- The sharp critical count composes with the direct raw-`W₁` empirical-RRM
recurrence.  Thus the dimension-two logarithmic rate is attached to the
actual adaptive RERM trajectory, not merely to a selected-shell certificate. -/
theorem one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanRERMState_le_radius_after_of_criticalDimensionRateCountSchedule
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter]
    {eta alpha gamma momentBound tailBound radius : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hradius_pos : 0 < radius) (hradius_le_one : radius ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p : ℝ) (hp : 0 < p)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (htailBound_moment :
      tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin 2)))
    (sampling : MeasurePerformativeSamplingKernel model)
    (gradient : EuclideanSpace ℝ (Fin 2) → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
      model.loss gradient domain modulus)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound
          radius p round))
        (EuclideanSpace ℝ (Fin 2)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn
      model domain (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
      (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p)
      deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable)
    {sensitivity targetRadius : ℝ} (hsensitivityNonneg : 0 ≤ sensitivity)
    (hsmoothnessPos : 0 < (smoothness : ℝ))
    (hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ)))
    (hsensitive : IsMeasureWassersteinSensitiveOn model domain sensitivity)
    (htargetRadius : 0 < targetRadius)
    (hinitial : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round))
      (EuclideanSpace ℝ (Fin 2)) 0,
      deployedOfHistory 0 history ∈ domain)
    (hempiricalIntegrable : ∀ iteration
      (batch : Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p iteration) →
        EuclideanSpace ℝ (Fin 2))
      candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos
          (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p iteration)
          batch : Measure (EuclideanSpace ℝ (Fin 2))))
    (entryIteration : ℕ)
    (hentry : ∀ trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
      (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round))
      (EuclideanSpace ℝ (Fin 2)) i,
      Real.log
          (dist (deployedOfHistory 0
            (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / targetRadius) /
        (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
          (entryIteration : ℝ))
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hbudget : Real.sqrt 2 * (radius / Real.rpow 2 (-eta - 1)) +
      (2 * Real.sqrt 2) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^
          Probability.pOneFournierGuillinHeadCutoff eta radius) + radius ≤
          sensitivity * targetRadius)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round))
        (pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
          2 (Probability.pOneFournierGuillinHeadCutoff eta radius)
          alpha gamma momentBound (radius / Real.rpow 2 (-eta - 1))
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
          (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p)
          (measurePerformativeDeployedLaw model
            (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round))
            deployedOfHistory)) iteration)) :
    ∃ gateScale : ℕ,
      radius ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw model sampling
        (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
        deployedOfHistory hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ targetRadius} ≥
        1 - p := by
  obtain ⟨gateScale, hpremises⟩ :=
    exists_pOneFournierGuillinAdaptiveEuclideanWassersteinOnePremises_criticalDimensionRateCountSchedule
      heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap hradius_pos hradius_le_one
      htailBound_pos htailEnvelope p hp hsmall htailBound_moment hbudget
      (measurePerformativeDeployedLaw model
        (fun round => Fin (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round))
        deployedOfHistory)
      (by simpa [measurePerformativeDeployedLaw] using hmoment)
  refine ⟨gateScale, fun hgate => ?_⟩
  obtain ⟨hfiniteIID, hthreshold⟩ := hpremises hgate
  exact _root_.PZMH20PerformativePrediction.EmpiricalRRMSamplingRecovery.one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanRERMState_le_radius_after_of_samplingKernel
      2 (Probability.pOneFournierGuillinHeadCutoff eta radius) alpha gamma momentBound
      (radius / Real.rpow 2 (-eta - 1)) model sampling gradient domain hconvex smoothness
      hgradient hdata hmodulus hstrong
      (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
      (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p)
      (criticalDimensionRateCountSchedule_pos eta alpha gamma tailBound radius p)
      deployedOfHistory hmeasurableDeployed hempirical populationUpdate hpopulation stable hstable
      hsensitivityNonneg hsmoothnessPos hsensitivitySmall hsensitive htargetRadius hinitial
      hempiricalIntegrable entryIteration hentry hp.le hevent hfiniteIID hthreshold

end PZMH20PerformativePrediction.EmpiricalRRMCriticalDimensionRecovery
