import LBG24SpatialUnderreporting.PaperInterface

/-!
# Proof endpoints: Quantifying Spatial Under-reporting Disparities

Each theorem below is the separately checked proof endpoint for one transparent
source-facing specification in `PaperInterface.lean`.
-/

namespace LBG24SpatialUnderreporting

open Filter MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped Function ProbabilityTheory Topology NNReal

noncomputable section

theorem sourceEquation2PoissonCountPMF :
    sourceEquation2PoissonCountPMFSpec := by
  intro rate exposure count _
  rfl

theorem sourceLemma1CalendarTimeDurationObservedProcess
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : Lemma1CalendarTimeDurationSourceModel Omega P) :
    sourceLemma1CalendarTimeDurationObservedProcessSpec M := by
  exact M.observed_calendar_process_properties

theorem sourceProposition1CalendarTimeNonidentifiability
    : sourceProposition1CalendarTimeNonidentifiabilitySpec := by
  intro Omega1 Omega2 mOmega1 mOmega2 P1 P2 M1 M2 observedRate
    observedRate_pos reporting_rates_ne _same_duration_density
    firstReportProbability1_pos firstReportProbability2_pos
    incidentRate1_eq incidentRate2_eq
  have observedRate1_eq : M1.observedIncidentRate = observedRate := by
    simp only [Proposition1CalendarTimeDurationSourceModel.observedIncidentRate,
      continuousDurationObservedIncidentRate]
    rw [incidentRate1_eq]
    exact div_mul_cancel₀ observedRate (ne_of_gt firstReportProbability1_pos)
  have observedRate2_eq : M2.observedIncidentRate = observedRate := by
    simp only [Proposition1CalendarTimeDurationSourceModel.observedIncidentRate,
      continuousDurationObservedIncidentRate]
    rw [incidentRate2_eq]
    exact div_mul_cancel₀ observedRate (ne_of_gt firstReportProbability2_pos)
  have incidentRate1_pos : 0 < M1.calendarFirstReports.incidentRate := by
    rw [incidentRate1_eq]
    exact div_pos observedRate_pos firstReportProbability1_pos
  have retention1_pos : 0 < M1.calendarFirstReports.retentionProbability := by
    rw [M1.preFirstReport_survival_retention_probability]
    exact firstReportProbability1_pos
  have incidentRate2_pos : 0 < M2.calendarFirstReports.incidentRate := by
    rw [incidentRate2_eq]
    exact div_pos observedRate_pos firstReportProbability2_pos
  have retention2_pos : 0 < M2.calendarFirstReports.retentionProbability := by
    rw [M2.preFirstReport_survival_retention_probability]
    exact firstReportProbability2_pos
  refine ⟨?_, ?_, reporting_rates_ne,
    M1.observedProcess incidentRate1_pos retention1_pos,
    M2.observedProcess incidentRate2_pos retention2_pos,
    rfl, rfl, ?_, ?_⟩
  · simpa only [observedRate1_eq] using
      M1.observedUniqueIncidentCount_real_strongLaw incidentRate1_pos retention1_pos
  · simpa only [observedRate2_eq] using
      M2.observedUniqueIncidentCount_real_strongLaw incidentRate2_pos retention2_pos
  · rw [M1.observedProcess_rate incidentRate1_pos retention1_pos, observedRate1_eq]
  · rw [M2.observedProcess_rate incidentRate2_pos retention2_pos, observedRate2_eq]

theorem sourceLemma2SelectedStartExponentialTail
    {Omega : Type*} [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P]
    (M : Lemma2ForwardSourceModel Omega P) :
    sourceLemma2SelectedStartExponentialTailSpec M := by
  intro u
  filter_upwards [M.conditional_no_report_given_firstReport u] with omega homega
  intro _
  rw [homega]
  exact noArrivalProb_eq_exponential_tail M.rate M.rate_pos
    (NNReal.coe_nonneg u)

theorem sourceTheorem1LikelihoodDecomposition
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {rate : ℝ} (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) :
    sourceTheorem1LikelihoodDecompositionSpec T M D rate_pos exposure_pos := by
  intro Omega _ _ P _ Tail _ selection startReference _ G selected_start_likelihood
  refine ⟨AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8
    M D rate_pos exposure_pos, ?_⟩
  exact ⟨AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D,
    fun _ => rfl⟩

theorem sourceHomogeneousReportingDelayMean :
    sourceHomogeneousReportingDelayMeanSpec := by
  intro rate rate_pos
  exact homogeneous_reporting_delay_mean rate rate_pos

theorem sourceEquation3MaximumLikelihoodEstimate :
    sourceEquation3MaximumLikelihoodEstimateSpec := by
  intro totalCount totalExposure exposure_pos
  refine ⟨rfl, ?_, ?_⟩
  · intro count_zero rate rate_nonneg
    subst totalCount
    simp [poissonRateLogLikelihood, poissonRateLogLikelihoodKernel, mleRate]
    exact mul_nonneg rate_nonneg (le_of_lt exposure_pos)
  · intro count_ne rate rate_pos
    exact mleRate_global_logLikelihood_max count_ne exposure_pos rate_pos

theorem sourceEquation6PoissonRegressionLikelihood :
    sourceEquation6PoissonRegressionLikelihoodSpec := by
  intro Feature _ alpha beta theta T M D exposure_pos Omega _ _ P _ Tail _ selection
    startReference _ G selected_start_likelihood
  constructor
  · simpa only [poissonRegressionRate_eq_logLink] using
      (AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8
        M D (poissonRegressionRate_pos alpha beta theta) exposure_pos)
  · exact ⟨AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D,
      fun _ => rfl⟩

theorem sourceZeroInflatedLikelihoodExtension :
    sourceZeroInflatedLikelihoodExtensionSpec := by
  intro M
  refine ⟨?_, ?_, ?_⟩
  · simpa [sourcePoissonPMF, sourcePoissonPMFOnSourceDomain] using
      (zeroInflatedIncidentLikelihood_zero M.gamma M.rate M.exposure)
  · intro count count_pos
    simpa [sourcePoissonPMF, sourcePoissonPMFOnSourceDomain] using
      (zeroInflatedIncidentLikelihood_of_positive_count (show count ≠ 0 by omega))
  · intro Incident incidents model count
    rfl

theorem sourcePostFirstJumpPoissonShift :
    sourcePostFirstJumpPoissonShiftSpec := by
  intro Omega _ _ P _ rate rate_pos interarrivalPath
    interarrivalPath_measurable interarrivalPath_hasLaw
  exact condDistrib_futureInterarrival_one_of_hasLaw rate_pos interarrivalPath
    interarrivalPath_measurable interarrivalPath_hasLaw

end

end LBG24SpatialUnderreporting
