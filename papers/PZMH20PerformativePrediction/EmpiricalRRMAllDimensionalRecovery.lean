import PZMH20PerformativePrediction.EmpiricalRRMSamplingRecovery

/-!
# All-dimensional sampling recovery for empirical RRM

The selected-shell partition certificate controls the raw empirical-`W₁`
failure event: outside the certificate, the dyadic-shell transport estimate is
at most the displayed `W₁` threshold.  Consequently, the finite-IID
probability bound proved for the measurable certificate also bounds the raw
event.

The all-dimensional count schedule supplies this finite-IID bound and its
deterministic `W₁` threshold.  Combining those facts with the direct
empirical-RRM sampling theorem gives the source two-phase recovery conclusion
without a loss-Lipschitz uniform-risk reduction.
-/

namespace PZMH20PerformativePrediction.EmpiricalRRMAllDimensionalRecovery

open AppliedModelingLib MeasureTheory ProbabilityTheory
open scoped InnerProductSpace ENNReal

/-- A selected-shell certificate probability bound transfers to the raw
empirical-`W₁` bad event, because the complement of the certificate implies
the defining `W₁` threshold. -/
theorem measureReal_pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent_le_of_selectedShellPartitionCertificate
    (dimension cutoff : ℕ) (eta alpha gamma momentBound deviation : ℝ)
    (confidence : ℕ → ℝ) (countSchedule : ℕ → ℕ)
    (hcountPositive : ∀ round, 0 < countSchedule round)
    (law : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (countSchedule round))
        (EuclideanSpace ℝ (Fin dimension)) iteration →
        ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (iteration : ℕ)
    (history : HeterogeneousBatchTrace (fun round => Fin (countSchedule round))
      (EuclideanSpace ℝ (Fin dimension)) iteration)
    (hdimension : 0 < dimension) (hconfidence : 0 ≤ confidence iteration)
    (heta : 0 < eta) (hdeviation : 0 ≤ deviation)
    (halpha : 1 ≤ alpha) (hgamma : 0 < gamma)
    (hmoment : Probability.HasExponentialRadialMoment (law iteration history) alpha gamma)
    (hhead : Probability.selectedShellGeometricCompactHeadBudget dimension cutoff
      (countSchedule iteration) (law iteration history)
      (Probability.selectedShellGeometricEffectiveHeadDepth dimension cutoff
        (countSchedule iteration) (law iteration history) (confidence iteration))
      (confidence iteration) ≤
        Probability.selectedShellGeometricHeadSchedule_byDimension dimension cutoff
          (countSchedule iteration) (confidence iteration)
          ((Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound))
    {failureBudget : ℝ}
    (hcertificate :
      (Probability.finiteIIDSampleLaw
        (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
        (countSchedule iteration)).real
        {batch |
          pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
            dimension cutoff eta deviation confidence countSchedule law iteration history batch} ≤
        failureBudget) :
    (Probability.finiteIIDSampleLaw
      (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
      (countSchedule iteration)).real
      {batch |
        pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
          dimension cutoff alpha gamma momentBound deviation confidence countSchedule
          hcountPositive law iteration history batch} ≤ failureBudget := by
  classical
  letI : Nonempty (Fin (countSchedule iteration)) :=
    Fin.pos_iff_nonempty.mp (hcountPositive iteration)
  letI : IsProbabilityMeasure
      (Probability.finiteIIDSampleLaw
        (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
        (countSchedule iteration)) := by
    dsimp [Probability.finiteIIDSampleLaw]
    infer_instance
  refine (measureReal_mono (μ := Probability.finiteIIDSampleLaw
    (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
    (countSchedule iteration)) ?_ (measure_ne_top _ _)).trans hcertificate
  intro batch hraw
  by_contra hgood
  have hWasserstein :=
    empiricalWassersteinOne_le_of_not_pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificate
      dimension cutoff eta alpha gamma momentBound deviation confidence countSchedule
      hcountPositive law iteration history batch hdimension hconfidence heta hdeviation halpha
      hgamma hmoment hhead hgood
  have hraw' :
      pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold dimension cutoff
        alpha gamma momentBound deviation confidence countSchedule law iteration history <
      ProbabilityCoupling.wassersteinOne
        (law iteration history)
        (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch) := by
    simpa only [pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent] using hraw
  rw [ProbabilityCoupling.wassersteinOne_comm] at hraw'
  exact (not_lt_of_ge hWasserstein) hraw'

/-- The actual all-dimensional selected-shell schedule supplies both analytic
premises of the direct raw-`W₁` sampling theorem: its roundwise finite-IID bad
event budget and its deterministic transport threshold. -/
theorem exists_pOneFournierGuillinAdaptiveEuclideanWassersteinOnePremises_allDimensionalConcreteSchedule
    (dimension cutoff : ℕ) (hdimension : 0 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment :
      tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    {wassersteinBound : ℝ}
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤
          wassersteinBound)
    (law : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration →
        ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)))
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment (law iteration history)
        alpha gamma momentBound) :
    ∃ gateScale : ℕ,
      scaledDeviation ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
        (∀ iteration history,
          (Probability.finiteIIDSampleLaw
            (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
            (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
              eta alpha gamma tailBound deviation scaledDeviation p headTolerance iteration)).real
            {batch |
              pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
                dimension cutoff alpha gamma momentBound deviation
                (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
                (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension
                  cutoff eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
                (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos
                  dimension cutoff eta alpha gamma tailBound deviation scaledDeviation p
                  headTolerance)
                law iteration history batch} ≤ theorem310FailureBudget p iteration) ∧
        ∀ iteration history,
          pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold dimension cutoff
            alpha gamma momentBound deviation
            (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
            (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
              eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
            law iteration history ≤ ENNReal.ofReal wassersteinBound := by
  have halpha : 1 ≤ alpha := by linarith
  have hdeviation : 0 ≤ deviation := by
    have hscale_pos : 0 < Real.rpow 2 (-(1 + eta)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hproduct : 0 < deviation * Real.rpow 2 (-(1 + eta)) := by
      simpa [hscaled] using hscaled_pos
    exact (pos_of_mul_pos_left hproduct hscale_pos.le).le
  have hfailureBudget : ∀ round, 0 < theorem310FailureBudget p round := by
    intro round
    unfold theorem310FailureBudget
    positivity
  obtain ⟨gateScale, hcertificate⟩ :=
    Probability.exists_pOneFournierGuillin_uniformSelectedShellPartitionCertificate_allDimensionalConcreteCountSchedule
      dimension cutoff hdimension heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap hscaled
      hscaled_pos hscaled_le_one htailBound_pos htailEnvelope
      (theorem310FailureBudget p) (fun _ => headTolerance) hfailureBudget
  refine ⟨gateScale, fun hgate => ⟨?_, ?_⟩⟩
  · intro iteration history
    have hselected :
        (Probability.finiteIIDSampleLaw
          (law iteration history : Measure (EuclideanSpace ℝ (Fin dimension)))
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance iteration)).real
          {batch |
            pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
              dimension cutoff eta deviation
              (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
              (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
                eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
              law iteration history batch} ≤ theorem310FailureBudget p iteration := by
      simpa [pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent,
        pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule,
        pOneFournierGuillinTheorem310AllDimensionalConcreteCountSchedule,
        pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule] using
        hcertificate hgate iteration (law iteration history) (hmoment iteration history)
    apply
      measureReal_pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent_le_of_selectedShellPartitionCertificate
        dimension cutoff eta alpha gamma momentBound deviation
        (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance)
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance)
        law iteration history hdimension (Math.expConfidenceForHalfBudget_nonneg _) heta_pos
        hdeviation halpha hgamma_pos (hmoment iteration history).hasExponentialRadialMoment
    · exact selectedShellGeometricCompactHeadBudget_le_allDimensionalConcreteSchedule
        dimension cutoff hdimension halpha hgamma_pos (law iteration history)
        (hmoment iteration history) iteration
    · exact hselected
  · intro iteration history
    exact pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold_le_allDimensionalConcreteSchedule
      dimension cutoff hdimension hdeviation hgamma_pos htailBound_moment htailEnvelope
      hheadTolerance hbudget law hmoment iteration history

/-- Under the all-dimensional selected-shell count schedule, the direct
empirical-RRM perturbation theorem gives logarithmic entry into, and permanent
retention in, the target ball. -/
theorem one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanRERMState_le_radius_after_of_allDimensionalConcreteSchedule
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter]
    (dimension cutoff : ℕ) (hdimension : 0 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment :
      tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
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
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance)
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance)
      deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable)
    {sensitivity radius : ℝ} (hsensitivityNonneg : 0 ≤ sensitivity)
    (hsmoothnessPos : 0 < (smoothness : ℝ))
    (hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ)))
    (hsensitive : IsMeasureWassersteinSensitiveOn model domain sensitivity)
    (hradius : 0 < radius)
    (hinitial : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      deployedOfHistory 0 history ∈ domain)
    (hempiricalIntegrable : ∀ iteration
      (batch : Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension))
      candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance iteration)
          batch : Measure (EuclideanSpace ℝ (Fin dimension))))
    (entryIteration : ℕ)
    (hentry : ∀ trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) i,
      Real.log
          (dist (deployedOfHistory 0
            (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / radius) /
        (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
          (entryIteration : ℝ))
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤
          sensitivity * radius)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
          dimension cutoff alpha gamma momentBound deviation
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
            alpha gamma tailBound deviation scaledDeviation p headTolerance)
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin
              (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
                eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration)) :
    ∃ gateScale : ℕ,
      scaledDeviation ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw model sampling
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance)
        deployedOfHistory hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ radius} ≥
        1 - p := by
  obtain ⟨gateScale, hpremises⟩ :=
    exists_pOneFournierGuillinAdaptiveEuclideanWassersteinOnePremises_allDimensionalConcreteSchedule
      dimension cutoff hdimension heta_pos heta_le_one halpha_pos hgamma_pos halpha_gap hscaled
      hscaled_pos hscaled_le_one htailBound_pos htailEnvelope p headTolerance hp hheadTolerance
      htailBound_moment hbudget
      (measurePerformativeDeployedLaw model
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
            alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        deployedOfHistory)
      (by simpa [measurePerformativeDeployedLaw] using hmoment)
  refine ⟨gateScale, fun hgate => ?_⟩
  obtain ⟨hfiniteIID, hthreshold⟩ := hpremises hgate
  exact EmpiricalRRMSamplingRecovery.one_sub_le_measureReal_pOneFournierGuillinAdaptiveEuclideanRERMState_le_radius_after_of_samplingKernel
    dimension cutoff alpha gamma momentBound deviation model sampling gradient domain hconvex
    smoothness hgradient hdata hmodulus hstrong
    (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
    (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta alpha
      gamma tailBound deviation scaledDeviation p headTolerance)
    (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff eta
      alpha gamma tailBound deviation scaledDeviation p headTolerance)
    deployedOfHistory hmeasurableDeployed hempirical populationUpdate hpopulation stable hstable
    hsensitivityNonneg hsmoothnessPos hsensitivitySmall hsensitive hradius hinitial
    hempiricalIntegrable entryIteration hentry hp.le hevent hfiniteIID hthreshold

end PZMH20PerformativePrediction.EmpiricalRRMAllDimensionalRecovery
