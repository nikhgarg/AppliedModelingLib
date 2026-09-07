import LG21TestOptionalPolicies.HiddenAccessTheorem31RawCandidateActions
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge
import LG21TestOptionalPolicies.ReportRequiredSelectedUpperTailCandidate
import LG21TestOptionalPolicies.SelectedConditionalRestrictionMap

/-!
# Report-required base-dependent latent-tail source bridge

This module identifies the actual positive report branch of a candidate that
takes exactly when latent skill exceeds a measurable base-dependent cutoff.
The conditioning law is the literal raw hidden-access population restricted
to that candidate action.  The access bit is never exposed to the school.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open Probability

/-- The latent upper-tail action event on the full `(base, score, skill)`
Gaussian source carrier. -/
def lg21ReportRequiredBaseDependentTailTakeEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | threshold baseScoreSkill.1 ≤ baseScoreSkill.2.2}

theorem lg21ReportRequiredBaseDependentTailTakeEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  exact measurableSet_le (hthreshold.comp measurable_fst)
    (measurable_snd.comp measurable_snd)

/-- The corresponding selection event after retaining `(base, score)` as the
public observation and skill as the latent coordinate. -/
def lg21ReportRequiredBaseDependentTailObservationEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set ((Base × ℝ) × ℝ) :=
  {observationSkill | threshold observationSkill.1.1 ≤ observationSkill.2}

theorem lg21ReportRequiredBaseDependentTailObservationEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet
      (lg21ReportRequiredBaseDependentTailObservationEvent threshold) := by
  exact measurableSet_le
    (hthreshold.comp (measurable_fst.comp measurable_fst)) measurable_snd

theorem lg21ReportRequiredBaseDependentTailTakeEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (publicBase : Base) :
    selectedFiber (lg21ReportRequiredBaseDependentTailTakeEvent threshold)
      publicBase = Set.univ ×ˢ Set.Ici (threshold publicBase) := by
  ext scoreSkill
  simp [selectedFiber, lg21ReportRequiredBaseDependentTailTakeEvent]

theorem lg21ReportRequiredBaseDependentTailObservationEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (publicObservation : Base × ℝ) :
    selectedFiber (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation = Set.Ici (threshold publicObservation.1) := by
  ext latentSkill
  simp [selectedFiber, lg21ReportRequiredBaseDependentTailObservationEvent]

/-- The selected conditional skill kernel induced by the latent-tail action. -/
noncomputable def lg21ReportRequiredBaseDependentTailSelectedTakeKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (threshold : Base -> ℝ) :
    Kernel (Base × ℝ) ℝ := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  exact selectedNormalizedKernel
    (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance)
    (lg21ReportRequiredBaseDependentTailObservationEvent threshold)

theorem lg21ReportRequiredBaseDependentTailSelectedTakeKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold)
    (publicBase : Base) (observedScore : ℝ) :
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance threshold
        (publicBase, observedScore) =
      lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        (Set.Ici (threshold publicBase)) := by
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredBaseDependentTailObservationEvent threshold
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  change selectedNormalizedKernel posteriorKernel event
      (publicBase, observedScore) = _
  rw [selectedNormalizedKernel_apply
    (lg21ReportRequiredBaseDependentTailObservationEvent_measurable
      threshold hthreshold)]
  rw [gaussianSignalPosteriorBaseKernel_apply,
    gaussianSignalPosteriorKernel_apply]
  congr 1

/-- The Gaussian joint kernel's latent-skill marginal is its displayed prior. -/
theorem lg21ReportRequiredBaseDependentTail_skill_marginal
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (publicBase : Base) :
    (gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance publicBase).map
      Prod.snd = gaussianReal (baseMean publicBase) priorVariance.toNNReal := by
  rw [gaussianSignalJointKernel_apply]
  let primitive := gaussianSignalPair
    (baseMean publicBase) priorVariance noiseVariance
  let scoreSkill : ℝ × ℝ -> ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  have hscoreSkill : Measurable scoreSkill := by
    dsimp [scoreSkill]
    fun_prop
  calc
    (primitive.map scoreSkill).map Prod.snd =
        primitive.map (Prod.snd ∘ scoreSkill) := by
          rw [Measure.map_map measurable_snd hscoreSkill]
    _ = primitive.map Prod.fst := by rfl
    _ = gaussianReal (baseMean publicBase) priorVariance.toNNReal := by
      change Measure.map Prod.fst
        ((gaussianReal (baseMean publicBase) priorVariance.toNNReal).prod
          (gaussianReal 0 noiseVariance.toNNReal)) = _
      rw [Measure.map_fst_prod]
      simp

private theorem lg21ReportRequiredBaseDependentTail_selectedTake_fibre_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ)
    (publicObservation : Base × ℝ) :
    selectionMass
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation ≠ 0 := by
  unfold selectionMass
  rw [gaussianSignalPosteriorBaseKernel_apply]
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have htail : 0 < gaussianReal (baseMean publicObservation.1)
      priorVariance.toNNReal (Set.Ioi (threshold publicObservation.1)) :=
    lg21_gaussianReal_Ioi_pos
      (baseMean publicObservation.1) (threshold publicObservation.1)
      hpriorVarianceNN
  have hselected : 0 < gaussianSignalPosteriorKernel
      (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
      (Set.Ici (threshold publicObservation.1)) :=
    lt_of_lt_of_le
      (lg21_gaussianSignalPosterior_selected_pos
        (baseMean publicObservation.1) priorVariance noiseVariance
        (Set.Ioi (threshold publicObservation.1))
        hpriorVariance hnoiseVariance htail publicObservation.2)
      (measure_mono Set.Ioi_subset_Ici_self)
  have hfibre : selectedFiber
      (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation = Set.Ici (threshold publicObservation.1) := by
    exact lg21ReportRequiredBaseDependentTailObservationEvent_selectedFiber
      threshold publicObservation
  have hkernelEq : gaussianReal
      (AppliedModelingLib.Probability.gaussianSignalWeight priorVariance noiseVariance *
          publicObservation.2 +
        AppliedModelingLib.Probability.gaussianSignalPriorWeight priorVariance noiseVariance *
          baseMean publicObservation.1)
      (AppliedModelingLib.Probability.gaussianSignalPosteriorVariance
        priorVariance noiseVariance)
      (selectedFiber
        (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
        publicObservation) =
      gaussianSignalPosteriorKernel
        (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
        (Set.Ici (threshold publicObservation.1)) := by
    rw [gaussianSignalPosteriorKernel_apply]
    rw [hfibre]
  rw [hkernelEq]
  exact ne_of_gt hselected

/-- Every measurable base-dependent latent upper tail has positive mass under
the nondegenerate Gaussian score/skill source. -/
theorem lg21ReportRequiredBaseDependentTail_take_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance)
        (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hfibre : ∀ publicBase,
      0 < rawKernel publicBase (selectedFiber event publicBase) := by
    intro publicBase
    have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
    have hupper : 0 < gaussianReal (baseMean publicBase)
        priorVariance.toNNReal (Set.Ici (threshold publicBase)) := by
      exact lt_of_lt_of_le
        (lg21_gaussianReal_Ioi_pos
          (baseMean publicBase) (threshold publicBase) hpriorVarianceNN)
        (measure_mono Set.Ioi_subset_Ici_self)
    calc
      0 < gaussianReal (baseMean publicBase)
          priorVariance.toNNReal (Set.Ici (threshold publicBase)) := hupper
      _ = (rawKernel publicBase).map Prod.snd
          (Set.Ici (threshold publicBase)) := by
        rw [lg21ReportRequiredBaseDependentTail_skill_marginal
          baseMean hbaseMean priorVariance noiseVariance publicBase]
      _ = rawKernel publicBase
          (selectedFiber event publicBase) := by
        rw [Measure.map_apply measurable_snd measurableSet_Ici]
        rw [lg21ReportRequiredBaseDependentTailTakeEvent_selectedFiber]
        congr 1
        ext scoreSkill
        simp
  have hmassMeasurable : Measurable
      (fun publicBase => rawKernel publicBase
        (selectedFiber event publicBase)) := by
    exact Kernel.measurable_kernel_prodMk_left hevent
  change 0 < (baseLaw ⊗ₘ rawKernel) event
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsupp : Function.support
      (fun publicBase => rawKernel publicBase
        (selectedFiber event publicBase)) = Set.univ := by
    ext publicBase
    simp [Function.mem_support, ne_of_gt (hfibre publicBase)]
  rw [hsupp, IsProbabilityMeasure.measure_univ]
  norm_num

/-- Conditioning the Gaussian source on a base-dependent latent upper tail
gives the selected posterior at the actual public `(base, score)` record. -/
theorem lg21ReportRequiredBaseDependentTail_selectedTake_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredBaseDependentTailTakeEvent threshold)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21ReportRequiredBaseDependentTail_take_positive
            baseLaw baseMean hbaseMean priorVariance noiseVariance
            hpriorVariance hnoiseVariance threshold hthreshold))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib
      (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
      selectedLaw =ᵐ[selectedLaw.map
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
      lg21ReportRequiredBaseDependentTailSelectedTakeKernel
        baseMean hbaseMean priorVariance noiseVariance threshold := by
  intro selectedLaw
  let rawLaw := baseLaw ⊗ₘ gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + noiseVariance).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  let observedLaw := baseLaw ⊗ₘ scoreKernel
  let selectedEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let observedEvent := lg21ReportRequiredBaseDependentTailObservationEvent threshold
  let association : Base × (ℝ × ℝ) → (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) → Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) → ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure observedLaw := by
    dsimp [observedLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw selectedEvent
      (ne_of_gt
        (lg21ReportRequiredBaseDependentTail_take_positive
          baseLaw baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance threshold hthreshold))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedEvent : MeasurableSet selectedEvent :=
    lg21ReportRequiredBaseDependentTailTakeEvent_measurable
      threshold hthreshold
  have hobservedEvent : MeasurableSet observedEvent :=
    lg21ReportRequiredBaseDependentTailObservationEvent_measurable
      threshold hthreshold
  have hassociation : Measurable association := by
    dsimp [association]
    fun_prop
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hselectionPositive : ∀ publicObservation,
      selectionMass posteriorKernel observedEvent publicObservation ≠ 0 := by
    intro publicObservation
    simpa [posteriorKernel, observedEvent] using
      (lg21ReportRequiredBaseDependentTail_selectedTake_fibre_positive
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance threshold publicObservation)
  letI : IsMarkovKernel
      (selectedNormalizedKernel posteriorKernel observedEvent) :=
    selectedNormalizedKernel_isMarkov hobservedEvent hselectionPositive
  have hselectedPreimage :
      selectedEvent = association ⁻¹' observedEvent := by
    ext scoreSkill
    simp [selectedEvent, association, observedEvent,
      lg21ReportRequiredBaseDependentTailTakeEvent,
      lg21ReportRequiredBaseDependentTailObservationEvent]
  have hrawAssoc : rawLaw.map association = observedLaw ⊗ₘ posteriorKernel := by
    simpa [rawLaw, association, observedLaw, posteriorKernel,
      gaussianSignalBaseScoreLatentLaw] using
      (gaussianSignalBaseScoreLatentLaw_factorization
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
  have hselectedAssoc :
      selectedLaw.map association =
        lg21NormalizedRestriction (rawLaw.map association) observedEvent := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw selectedEvent by rfl,
      hselectedPreimage]
    exact lg21_normalizedRestriction_map_preimage
      rawLaw association hassociation observedEvent hobservedEvent
  have hselectedFactor :
      selectedLaw.map association =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map association =
          lg21NormalizedRestriction (rawLaw.map association) observedEvent := hselectedAssoc
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
            observedEvent := by rw [hrawAssoc]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent :=
        normalizedRestriction_compProd_selectedNormalizedKernel
          (μ := observedLaw) (κ := posteriorKernel)
          hobservedEvent hselectionPositive
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel observedEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have hselectedObservation :
      selectedLaw.map observation =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent := by
    calc
      selectedLaw.map observation = (selectedLaw.map association).map Prod.fst := by
        rw [Measure.map_map measurable_fst hassociation]
        rfl
      _ = (normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent).map Prod.fst := by
        rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      selectedLaw.map (fun scoreSkill => (observation scoreSkill, latent scoreSkill)) =
        selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map (fun scoreSkill =>
          (observation scoreSkill, latent scoreSkill)) =
          selectedLaw.map association := by rfl
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := hselectedFactor
      _ = selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
        rw [hselectedObservation]
  change condDistrib latent observation selectedLaw =ᵐ[selectedLaw.map observation]
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance threshold
  simpa [posteriorKernel, observedEvent,
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel] using
    (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hlatent hselectedJoint)

/-- The literal report event is positive access together with the candidate's
latent-tail selection.  The public record does not reveal access. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true) =
      {student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessConditionalMeanTailTake,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21ContinuousPopulationSkill,
      lg21HiddenAccessBaseScoreSkillObservation,
      lg21ReportRequiredBaseDependentTailTakeEvent]

/-- Normalizing the literal report action and forgetting hidden access gives
the Gaussian source law selected by the same latent upper tail. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReportBaseScoreSkillLaw_eq_normalizedTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true))).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have haccessLaw : accessLaw = lg21NormalizedRestriction rawLaw accessEvent := by
    rfl
  have hreportEvent : reportEvent =
      accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  have hnormalizedRaw :
      lg21NormalizedRestriction rawLaw reportEvent =
        lg21NormalizedRestriction accessLaw (observation ⁻¹' tailEvent) := by
    calc
      lg21NormalizedRestriction rawLaw reportEvent =
          lg21NormalizedRestriction rawLaw
            (accessEvent ∩ observation ⁻¹' tailEvent) := by rw [hreportEvent]
      _ = lg21NormalizedRestriction
          (lg21NormalizedRestriction rawLaw accessEvent)
          (observation ⁻¹' tailEvent) := by
          symm
          exact lg21_normalizedRestriction_normalizedRestriction_eq_inter
            rawLaw accessEvent (observation ⁻¹' tailEvent) haccessEvent
            (htailEvent.preimage hobservation)
      _ = lg21NormalizedRestriction accessLaw
          (observation ⁻¹' tailEvent) := by rw [haccessLaw]
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  change (lg21NormalizedRestriction rawLaw reportEvent).map observation =
    lg21NormalizedRestriction (baseLaw ⊗ₘ joint) tailEvent
  rw [hnormalizedRaw]
  calc
    (lg21NormalizedRestriction accessLaw
      (observation ⁻¹' tailEvent)).map observation =
        lg21NormalizedRestriction (accessLaw.map observation) tailEvent := by
          exact lg21_normalizedRestriction_map_preimage accessLaw
            observation hobservation tailEvent htailEvent
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ joint) tailEvent := by
          rw [haccessScoreSkill]

/-- The literal report branch has positive mass whenever the access group
does, before any action-law normalization. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  have htailPositive : 0 < (baseLaw ⊗ₘ joint) tailEvent := by
    simpa [joint, tailEvent] using
      (lg21ReportRequiredBaseDependentTail_take_positive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have haccessTailPositive : 0 < accessLaw (observation ⁻¹' tailEvent) := by
    rw [← Measure.map_apply hobservation htailEvent, haccessScoreSkill]
    exact htailPositive
  have hintersectionPositive : 0 < rawLaw
      (accessEvent ∩ observation ⁻¹' tailEvent) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (observation ⁻¹' tailEvent) at haccessTailPositive
    rw [lg21NormalizedRestriction_apply rawLaw
      (htailEvent.preimage hobservation)] at haccessTailPositive
    have hraw : 0 < rawLaw
        ((observation ⁻¹' tailEvent) ∩ accessEvent) :=
      (ENNReal.mul_pos_iff.mp haccessTailPositive).2
    simpa [inter_comm] using hraw
  have hreportEvent : reportEvent =
      accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  change 0 < rawLaw reportEvent
  rw [hreportEvent]
  exact hintersectionPositive

/-- The displayed selected-tail reporter value is the conditional mean on its
actual positive raw report action law. -/
theorem lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true)
    let actionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
      lg21NormalizedRestriction_isProbability rawLaw reportEvent
        (ne_of_gt
          (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
            M haccess testFeature baseLaw baseMean hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            threshold hthreshold hsourceFactor))
        (measure_ne_top _ _)
    letI : IsProbabilityMeasure actionLaw :=
      Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            scoreSkill.2.2)
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            (scoreSkill.1, scoreSkill.2.1))
          actionLaw publicObservation := by
  intro rawLaw reportEvent actionLaw
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hreportPositive : 0 < rawLaw reportEvent := by
    simpa [rawLaw, reportEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  let selectedLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ joint) tailEvent
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt
        (lg21ReportRequiredBaseDependentTail_take_positive
          baseLaw baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance threshold hthreshold))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hactionLaw : actionLaw = selectedLaw := by
    simpa [actionLaw, rawLaw, reportEvent, selectedLaw, tailEvent, joint] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportBaseScoreSkillLaw_eq_normalizedTail
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance threshold hthreshold hsourceFactor)
  have hRCD := lg21ReportRequiredBaseDependentTail_selectedTake_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance threshold hthreshold
  have hRCDAction : condDistrib
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        scoreSkill.2.2)
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1))
      actionLaw =ᵐ[actionLaw.map
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          (scoreSkill.1, scoreSkill.2.1))]
      lg21ReportRequiredBaseDependentTailSelectedTakeKernel
        baseMean hbaseMean baseVariance noiseVariance threshold := by
    simpa only [hactionLaw] using hRCD
  filter_upwards [hRCDAction] with publicObservation hkernel
  rw [← lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
    (baseMean publicObservation.1) baseVariance noiseVariance
    publicObservation.2 (threshold publicObservation.1)
    hbaseVariance hnoiseVariance]
  rw [← lg21ReportRequiredBaseDependentTailSelectedTakeKernel_apply
    baseMean hbaseMean baseVariance noiseVariance threshold hthreshold
    publicObservation.1 publicObservation.2]
  rw [hkernel]

/-- A measurable cutoff graph has zero mass under a nondegenerate Gaussian
location kernel. -/
theorem lg21ReportRequiredBaseDependentTail_gaussianLocation_graph_measure_zero
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ) (hbaseVariance : 0 < baseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    (baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
      {baseSkill | baseSkill.2 = threshold baseSkill.1} = 0 := by
  let graph : Set (Base × ℝ) :=
    {baseSkill | baseSkill.2 = threshold baseSkill.1}
  let kernel := gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel kernel := by
    simpa [kernel] using
      (gaussianLocationKernel_isMarkov
        baseMean hbaseMean baseVariance.toNNReal)
  have hgraph : MeasurableSet graph := by
    simpa [graph] using
      measurableSet_eq_fun measurable_snd (hthreshold.comp measurable_fst)
  have hvariance : baseVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance)
  have hfiberZero : ∀ publicBase,
      kernel publicBase (Prod.mk publicBase ⁻¹' graph) = 0 := by
    intro publicBase
    have hfiber : Prod.mk publicBase ⁻¹' graph = {threshold publicBase} := by
      ext latentSkill
      simp [graph]
    rw [hfiber, gaussianLocationKernel_apply,
      gaussianReal_singleton_eq_zero (baseMean publicBase) hvariance]
  rw [Measure.compProd_apply hgraph]
  have hzero : (fun publicBase =>
      kernel publicBase (Prod.mk publicBase ⁻¹' graph)) = 0 := by
    funext publicBase
    exact hfiberZero publicBase
  rw [hzero]
  exact lintegral_zero

/-- Forgetting score from the raw Gaussian score/skill factorization gives
the raw base/skill Gaussian factorization used for the cutoff-boundary null
set. -/
theorem lg21ReportRequiredBaseDependentTail_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    (lg21ContinuousGaussianPopulationLaw M).map
      (lg21HiddenAccessBaseSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreSkill := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseSkill := lg21HiddenAccessBaseSkillObservation testFeature
  let projection : ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) -> (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.2)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreSkill : Measurable scoreSkill := by
    simpa [scoreSkill] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hprojection : Measurable projection := by
    dsimp [projection]
    fun_prop
  have hjointMarginal : joint.map Prod.snd =
      gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21ReportRequiredBaseDependentTail_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance publicBase,
      gaussianLocationKernel_apply]
  calc
    rawLaw.map baseSkill = (rawLaw.map scoreSkill).map projection := by
      rw [Measure.map_map hprojection hscoreSkill]
      rfl
    _ = (baseLaw ⊗ₘ joint).map projection := by
      rw [show rawLaw.map scoreSkill = baseLaw ⊗ₘ joint by
        simpa [rawLaw, scoreSkill, joint] using hsourceFactor]
    _ = baseLaw ⊗ₘ joint.map Prod.snd := by
      simpa [projection, joint] using
        (map_compProd_eq_compProd_map measurable_snd
          (μ := baseLaw) (κ := joint))
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by rw [hjointMarginal]

/-- Forgetting score in the source factorization recovers the full base/skill
law used by the literal no-report raw mixture. -/
theorem lg21ReportRequiredBaseDependentTail_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        baseVariance.toNNReal := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreMarginal : joint.map Prod.snd =
      gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_snd,
      lg21ReportRequiredBaseDependentTail_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance publicBase,
      gaussianLocationKernel_apply]
  calc
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ joint.map Prod.snd := by
          simpa [joint] using
            (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
              M haccess testFeature baseLaw baseMean hbaseMean
              baseVariance noiseVariance hsourceFactor)
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by rw [hscoreMarginal]

end

end LG21TestOptionalPolicies
