import LBG24SpatialUnderreporting.LegacyPaperInterface

/-!
# LBG24 proof support

This module retains Lean-checked auxiliary constructions used to develop and
test the paper-local models. They are deliberately outside `PaperInterface`:
the review surface contains only declarations that directly state a selected
source result. The source map retains explicit links from the relevant source
items to these support declarations where they supply proof infrastructure.
-/

namespace LBG24SpatialUnderreporting

open Filter
open MeasureTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped BigOperators Function ProbabilityTheory Topology NNReal

noncomputable section

/-! ## Lemma 1 support constructions -/

/--
Restricted finite-horizon birth-cohort form of Lemma 1: if the actual source
cohort has a checked iid eventual-report retention law, retained births have
the corresponding thinned Poisson count law.

This counts births in one fixed window by an eventual-report label; it does
not identify first-report times, construct a retained process, or establish
steady state.
-/
theorem lemma1_birth_cohort_finite_horizon_thinning
    {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega}
    (M : BirthCohortFiniteHorizonBridge.BirthCohortRetentionSource Omega P) :
    ProbabilityTheory.HasLaw M.retainedBirthCount
      (ProbabilityTheory.poissonMeasure
        (rateExposureParam M.incidentRate M.exposure
          (mul_nonneg M.incidentRate_nonneg M.exposure_nonneg) *
          M.retentionProbability)) P := by
  exact M.retainedBirthCount_hasLaw

/--
Nonhomogeneous cumulative-intensity version of the combined Lemma 1 process
construction. The supplied probability bounds are the explicit side conditions
needed by the marked-Poisson constructor. The integral identity equates this
probability with the paper's literal intensity formula.

This is a restricted construction, not the full duration-law steady-state
observed process asserted by source Lemma 1.
-/
theorem lemma1_nonhomogeneous_marked_poisson_process_construction
    (incidentRate : ℝ) (reportingRate durationDensity : ℝ → ℝ)
    (hincident : 0 < incidentRate)
    (hdetection :
      0 < continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => ∫ u in (0 : ℝ)..t, reportingRate u) durationDensity)
    (hdetection_le :
      continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => ∫ u in (0 : ℝ)..t, reportingRate u) durationDensity ≤ 1) :
    (∀ observedCount : ℕ,
        (∑' originalCount : ℕ,
            countLikelihood 1 incidentRate originalCount *
              binomialThinningMass
                (continuousDurationFirstReportProbabilityOfCumulativeIntensity
                  (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
                  durationDensity)
                originalCount observedCount) =
          countLikelihood 1
            (continuousDurationObservedIncidentRateOfCumulativeIntensity
              incidentRate (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
              durationDensity)
            observedCount) ∧
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
          (observedProcess :
            @ForwardHomogeneousPoissonCountingProcessByLaw Ω mΩ P),
        observedProcess.rate =
          continuousDurationObservedIncidentRateOfCumulativeIntensity
            incidentRate (fun t => ∫ u in (0 : ℝ)..t, reportingRate u)
            durationDensity := by
  constructor
  · intro observedCount
    exact lemma1_nonhomogeneous_poisson_thinning_count_law
      incidentRate reportingRate durationDensity observedCount
  · let detectionProbability :=
      continuousDurationFirstReportProbabilityOfCumulativeIntensity
        (fun t => ∫ u in (0 : ℝ)..t, reportingRate u) durationDensity
    rcases
        Lemma1MarkedPoissonThinning.MarkedPoissonReportingProcess.exists_markedPoissonReportingProcess
          incidentRate detectionProbability hincident hdetection hdetection_le with
      ⟨Ω, mΩ, P, M, hlatent, hdetectionEq⟩
    have M_detection_pos : 0 < M.detectionProbability := by
      rw [hdetectionEq]
      exact hdetection
    rcases M.observed_process_is_homogeneous_poisson M_detection_pos with
      ⟨observedProcess, _hcount, hrate⟩
    refine ⟨Ω, mΩ, P, observedProcess, ?_⟩
    rw [hrate, hlatent, hdetectionEq]
    rfl

/-! ## Eq. (7) derivational bridges -/

/--
The zero-count Eq. (7) branch derived from the already reviewed direct
causal-stopping Eq. (8) theorem. This is a proof bridge, not a separate source
route.
-/
theorem equation7_zero_count_proportional_to_causal_stopping_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {gamma rate : ℝ}
    (hcount : T.count = 0) (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) :
    gamma * AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D +
        (1 - gamma) *
          AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D rate =
      AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
        zeroInflatedIncidentLikelihood gamma rate T.window.exposure T.count := by
  rw [AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8
    M D rate_pos exposure_pos]
  rw [hcount, equation7_zero_inflated_likelihood_zero]
  simp only [sourcePoissonPMF, sourcePoissonPMFOnSourceDomain]
  ring

/--
The positive-count Eq. (7) branch derived from the already reviewed direct
causal-stopping Eq. (8) theorem. This is a proof bridge, not a separate source
route.
-/
theorem equation7_positive_count_proportional_to_causal_stopping_eq8
    (T : OrderedFiniteJumpTimeline)
    (M : AppendixTheorem2CausalStoppingSourceModel T.count)
    (D : AppendixTheorem2CausalStoppingSourceModel.EndpointDensityPresentation M)
    {gamma rate : ℝ}
    (hcount : 1 ≤ T.count) (rate_pos : 0 < rate)
    (exposure_pos : 0 < T.window.exposure) :
    (1 - gamma) *
        AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood T M D rate =
      AppendixTheorem2CausalStoppingSourceModel.rateFreeResidual T M D *
        zeroInflatedIncidentLikelihood gamma rate T.window.exposure T.count := by
  rw [AppendixTheorem2CausalStoppingSourceModel.conditionalLikelihood_factorizes_eq8
    M D rate_pos exposure_pos]
  rw [equation7_zero_inflated_likelihood_positive_count hcount]
  simp only [sourcePoissonPMF, sourcePoissonPMFOnSourceDomain]
  ring

/-! ## Proposition 1 restricted witness -/

/--
Restricted non-identifiability witness for two concrete reporting rates. The
source-facing Proposition 1 route additionally establishes the steady-state
process and its large-time law.
-/
theorem proposition1_continuous_duration_nonidentifiability_witness
    (durationDensity : ℝ → ℝ)
    (hdetection_one :
      0 < continuousDurationFirstReportProbability 1 durationDensity)
    (hdetection_two :
      0 < continuousDurationFirstReportProbability 2 durationDensity) :
    ∃ observedRate rate₁ rate₂ : ℝ,
      0 < observedRate ∧
      rate₁ ≠ rate₂ ∧
      0 < observedRate /
        continuousDurationFirstReportProbability rate₁ durationDensity ∧
      0 < observedRate /
        continuousDurationFirstReportProbability rate₂ durationDensity ∧
      continuousDurationObservedIncidentRate
          (observedRate /
            continuousDurationFirstReportProbability rate₁ durationDensity)
          rate₁ durationDensity =
        continuousDurationObservedIncidentRate
          (observedRate /
            continuousDurationFirstReportProbability rate₂ durationDensity)
          rate₂ durationDensity := by
  refine ⟨1, 1, 2, by norm_num, by norm_num,
    div_pos (by norm_num) hdetection_one,
    div_pos (by norm_num) hdetection_two, ?_⟩
  exact
    (proposition1_continuous_duration_nonidentifiability_collision
      durationDensity (by norm_num) (ne_of_gt hdetection_one)
        (ne_of_gt hdetection_two)).2

/-! ## Corrected-model Eq. (8) constructions -/

/--
Under the explicit full resampled-response law, the fixed-tag weighted model
likelihood measure equals the atom-safe collapsed observation law. This is a
corrected-model construction, not an archived-source derivation.
-/
theorem corrected_resampled_endpoint_observation_likelihood
    {OmegaBase Omega : Type*}
    [MeasurableSpace OmegaBase] [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource OmegaBase Omega P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (J : CausalPreEndEndpointKernelPackage.FullResampledCausalResponseLaw S K) :
    CausalPreEndEndpointKernelPackage.FullResampledCausalResponseLaw.modelObservationLikelihood S K =
      (K.toKernelCollapsed S).collapsedObservationLaw rate := by
  exact
    CausalPreEndEndpointKernelPackage.FullResampledCausalResponseLaw.modelObservationLikelihood_eq_collapsedObservationLaw
      S K J

/--
The fixed-tag resampled-model likelihood measure has the exact Poisson gap
density relative to the terminal candidate-clock kernel. It is a corrected-model
support theorem and does not provide an archived-source endpoint or
selected-start bridge.
-/
theorem corrected_resampled_endpoint_observation_density
    {OmegaBase Omega : Type*}
    [MeasurableSpace OmegaBase] [MeasurableSpace Omega] [StandardBorelSpace Omega]
    {P : Measure Omega} [IsProbabilityMeasure P] {count : ℕ} {rate : ℝ}
    (S : StationaryPalmTaggedArrivalSource OmegaBase Omega P count rate)
    (K : CausalPreEndEndpointKernelPackage S)
    (J : CausalPreEndEndpointKernelPackage.FullResampledCausalResponseLaw S K) :
    CausalPreEndEndpointKernelPackage.FullResampledCausalResponseLaw.modelObservationLikelihood S K =
      ((volume : Measure (Fin count -> ℝ)) ⊗ₘ
        (K.toKernelCollapsed S).terminalEndpointKernel).withDensity
          ((K.toKernelCollapsed S).rawEndpointKernelDensity rate) := by
  rw [corrected_resampled_endpoint_observation_likelihood S K J]
  exact
    CollapsedFiniteStageEndpointKernelModel.collapsedObservationLaw_eq_withDensity_rawEndpointKernelDensity
      (K.toKernelCollapsed S) S.rate_pos

/--
A restricted one-endpoint special case after fixing a Palm tag and one
nonnegative deterministic absolute cap. This is proof support for a fixed-cap
Palm model, not an archived Eq. (8) derivation.
-/
theorem corrected_fixed_cap_palm_observation_likelihood
    {OmegaBase Omega : Type*}
    [MeasurableSpace OmegaBase] [MeasurableSpace Omega]
    {P : Measure Omega} {count : ℕ} {rate c : ℝ}
    (S : StationaryPalmTaggedArrivalSource OmegaBase Omega P count rate)
    (hc : 0 <= c) :
    FixedCapPalmBridge.oneCapPalmLikelihood S c =
      (FixedCapPalmBridge.model count c S.startWeight).collapsedObservationLaw
        rate := by
  exact FixedCapPalmBridge.oneCapPalmLikelihood_eq_collapsedObservationLaw
    S c hc

/--
Corrected stationary/Palm factorization for a model with stronger
conditional-product/resampled-clock data than the archived source theorem.
It remains available as proof support without receiving source-theorem credit.
-/
theorem theorem2_stationary_palm_source_corrected_eq8
    (T : OrderedFiniteJumpTimeline) (rate : ℝ) (h_rate : 0 < rate)
    (S : assumption_theorem2_causal_endpoint_density_source T.count)
    (h_exposure : 0 < T.window.exposure) :
    StationaryPalmCausalObservationModel.conditionalLikelihoodDensity T
        (StationaryPalmCausalObservationModel.ofPoissonSuspension
          rate h_rate T.count S) =
      S.toCollapsedFiniteStageEndpointModel.toFiniteStageCausalEndpointProfile.correctedResidual *
        sourcePoissonPMF rate T.window.exposure T.count := by
  exact
    StationaryPalmCausalObservationModel.poissonSuspension_conditionalLikelihoodDensity_factorizes_corrected_eq8
      T rate h_rate S h_exposure

end

end LBG24SpatialUnderreporting
