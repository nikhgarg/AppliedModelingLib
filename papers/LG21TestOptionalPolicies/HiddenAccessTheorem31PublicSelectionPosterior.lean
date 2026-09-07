import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate

/-!
# Gaussian posterior under arbitrary public selection

A report action may be any measurable predicate of the public non-test
profile and the realized score.  Conditioning a Gaussian source population on
such an attained action changes the observed marginal, but not the conditional
skill law after that public observation is known.  This file states that fact
for an arbitrary measurable public selection set rather than a named cutoff
or a particular reporting function.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Lift a selection on the public `(base, score)` record to the complete
`(base, score, skill)` Gaussian source record. -/
def lg21BaseScoreSelectionEvent
    {Base : Type*} [MeasurableSpace Base]
    (selected : Set (Base × ℝ)) : Set (Base × (ℝ × ℝ)) :=
  {scoreSkill | (scoreSkill.1, scoreSkill.2.1) ∈ selected}

theorem lg21BaseScoreSelectionEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected) :
    MeasurableSet (lg21BaseScoreSelectionEvent selected) := by
  exact hselected.preimage (measurable_fst.prodMk (measurable_fst.comp measurable_snd))

/--
Selecting any positive measurable set of public `(base, score)` records does
not change the Gaussian posterior over skill conditional on that record.

The selected law is explicitly normalized and the conclusion is almost
everywhere under its attained public-observation marginal.  No claim is made
on unselected records, and no cutoff representation of `selected` is used.
-/
theorem lg21Gaussian_selectedPublic_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (hpositive : 0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
        (lg21BaseScoreSelectionEvent selected)) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      (lg21BaseScoreSelectionEvent selected)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib
      (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
      selectedLaw =ᵐ[selectedLaw.map
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
      gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance := by
  intro selectedLaw
  let rawLaw := baseLaw ⊗ₘ gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (baseVariance + noiseVariance).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean baseVariance noiseVariance
  let observedLaw := baseLaw ⊗ₘ scoreKernel
  let selectionEvent := lg21BaseScoreSelectionEvent selected
  let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) -> Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) -> ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (baseVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsProbabilityMeasure observedLaw := by
    dsimp [observedLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw selectionEvent
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectionEvent : MeasurableSet selectionEvent := by
    simpa [selectionEvent] using
      (lg21BaseScoreSelectionEvent_measurable selected hselected)
  have hassociation : Measurable association := by
    dsimp [association]
    fun_prop
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hselectionPreimage :
      selectionEvent = association ⁻¹' (selected ×ˢ Set.univ) := by
    ext scoreSkill
    simp [selectionEvent, association, lg21BaseScoreSelectionEvent]
  have hrawAssoc : rawLaw.map association = observedLaw ⊗ₘ posteriorKernel := by
    simpa [rawLaw, association, observedLaw, posteriorKernel,
      gaussianSignalBaseScoreLatentLaw] using
      (gaussianSignalBaseScoreLatentLaw_factorization
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance)
  have hselectedAssoc :
      selectedLaw.map association =
        lg21NormalizedRestriction (rawLaw.map association)
          (selected ×ˢ Set.univ) := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw selectionEvent by rfl,
      hselectionPreimage]
    exact lg21_optional_normalizedRestriction_map_preimage
      rawLaw association hassociation (selected ×ˢ Set.univ)
      (hselected.prod MeasurableSet.univ)
  have hselectedFactor :
      selectedLaw.map association =
        lg21NormalizedRestriction observedLaw selected ⊗ₘ posteriorKernel := by
    calc
      selectedLaw.map association =
          lg21NormalizedRestriction (rawLaw.map association)
            (selected ×ˢ Set.univ) := hselectedAssoc
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
            (selected ×ˢ Set.univ) := by rw [hrawAssoc]
      _ = lg21NormalizedRestriction observedLaw selected ⊗ₘ posteriorKernel :=
        lg21_normalizedRestriction_compProd_left
          observedLaw posteriorKernel selected hselected
  letI : SFinite (lg21NormalizedRestriction observedLaw selected) := by
    unfold lg21NormalizedRestriction
    infer_instance
  have hselectedObservation :
      selectedLaw.map observation =
        lg21NormalizedRestriction observedLaw selected := by
    calc
      selectedLaw.map observation = (selectedLaw.map association).map Prod.fst := by
        rw [Measure.map_map measurable_fst hassociation]
        rfl
      _ = (lg21NormalizedRestriction observedLaw selected ⊗ₘ
          posteriorKernel).map Prod.fst := by rw [hselectedFactor]
      _ = lg21NormalizedRestriction observedLaw selected :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      selectedLaw.map (fun scoreSkill => (observation scoreSkill, latent scoreSkill)) =
        selectedLaw.map observation ⊗ₘ posteriorKernel := by
    calc
      selectedLaw.map (fun scoreSkill =>
          (observation scoreSkill, latent scoreSkill)) =
          selectedLaw.map association := by rfl
      _ = lg21NormalizedRestriction observedLaw selected ⊗ₘ posteriorKernel :=
        hselectedFactor
      _ = selectedLaw.map observation ⊗ₘ posteriorKernel := by
        rw [hselectedObservation]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hobservation hlatent hselectedJoint

/-! ## Literal hidden-access report-branch transport -/

/-- The public selection induced by an arbitrary measurable post-score report
action.  It records only information visible to the school. -/
def lg21HiddenAccessPublicReportSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
  {publicRecord | candidateReport publicRecord.1 publicRecord.2 = true}

theorem lg21HiddenAccessPublicReportSelection_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessPublicReportSelection testFeature candidateReport) := by
  exact (measurableSet_singleton true).preimage hcandidateReport

/-- The public records assigned to the no-report action by an arbitrary
measurable report rule.  As with the report selection, this contains no
latent skill, access bit, or unreported-score cohort information. -/
def lg21HiddenAccessPublicNoReportSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
  {publicRecord | candidateReport publicRecord.1 publicRecord.2 = false}

theorem lg21HiddenAccessPublicNoReportSelection_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport) := by
  exact (measurableSet_singleton false).preimage hcandidateReport

/-- With all access students taking, an arbitrary public report rule selects
the literal source report branch exactly on the access slice of its public
selection set. -/
theorem lg21HiddenAccessAllTake_rawCandidateReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport =
      {student | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21BaseScoreSelectionEvent
            (lg21HiddenAccessPublicReportSelection testFeature candidateReport)) := by
  ext student
  rcases student with ⟨access, primitive⟩
  cases access <;>
    simp [lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction, lg21HiddenAccessAllTake,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessStudentScore,
      lg21HiddenAccessBaseScoreSkillObservation, lg21BaseScoreSelectionEvent,
      lg21HiddenAccessPublicReportSelection]

/-- Under an all-take candidate, the access component of the literal
no-report branch is selected exactly by the same arbitrary public
`(base, score)` no-report predicate. -/
theorem lg21HiddenAccessAllTake_accessTakeNoReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport =
      {student | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21BaseScoreSelectionEvent
            (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport)) := by
  ext student
  rcases student with ⟨access, primitive⟩
  cases access <;>
    simp [lg21HiddenAccessCandidateAccessTakeNoReportEvent,
      lg21HiddenAccessAllTake, lg21HiddenAccessStudentTake,
      lg21HiddenAccessStudentReport, lg21HiddenAccessStudentScore,
      lg21HiddenAccessBaseScoreSkillObservation, lg21BaseScoreSelectionEvent,
      lg21HiddenAccessPublicNoReportSelection]

/--
After normalizing an all-take candidate's literal report branch, forgetting
the hidden access coordinate gives exactly the Gaussian law selected by the
same arbitrary public report set.  This is a source-law equality; it neither
conditions the school on access nor infers anything from the name or shape of
the report action.
-/
theorem lg21HiddenAccessAllTake_rawCandidateReportBaseScoreSkillLaw_eq_normalizedPublicSelection
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
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21BaseScoreSelectionEvent
          (lg21HiddenAccessPublicReportSelection testFeature candidateReport)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let publicSelection := lg21HiddenAccessPublicReportSelection testFeature candidateReport
  let selectionEvent := lg21BaseScoreSelectionEvent publicSelection
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
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
  have hpublicSelection : MeasurableSet publicSelection := by
    simpa [publicSelection] using
      (lg21HiddenAccessPublicReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hselectionEvent : MeasurableSet selectionEvent := by
    simpa [selectionEvent] using
      (lg21BaseScoreSelectionEvent_measurable publicSelection hpublicSelection)
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have haccessLaw : accessLaw = lg21NormalizedRestriction rawLaw accessEvent := by
    rfl
  have hreportEvent : reportEvent =
      accessEvent ∩ scoreSkillObservation ⁻¹' selectionEvent := by
    simpa [reportEvent, accessEvent, scoreSkillObservation, selectionEvent,
      publicSelection] using
      (lg21HiddenAccessAllTake_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature candidateReport)
  have hnormalizedRaw :
      lg21NormalizedRestriction rawLaw reportEvent =
        lg21NormalizedRestriction accessLaw
          (scoreSkillObservation ⁻¹' selectionEvent) := by
    calc
      lg21NormalizedRestriction rawLaw reportEvent =
          lg21NormalizedRestriction rawLaw
            (accessEvent ∩ scoreSkillObservation ⁻¹' selectionEvent) := by
              rw [hreportEvent]
      _ = lg21NormalizedRestriction
          (lg21NormalizedRestriction rawLaw accessEvent)
            (scoreSkillObservation ⁻¹' selectionEvent) := by
              symm
              exact lg21_normalizedRestriction_normalizedRestriction_eq_inter
                rawLaw accessEvent (scoreSkillObservation ⁻¹' selectionEvent)
                haccessEvent (hselectionEvent.preimage hscoreSkillObservation)
      _ = lg21NormalizedRestriction accessLaw
          (scoreSkillObservation ⁻¹' selectionEvent) := by rw [haccessLaw]
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  change (lg21NormalizedRestriction rawLaw reportEvent).map scoreSkillObservation =
    lg21NormalizedRestriction (baseLaw ⊗ₘ joint) selectionEvent
  rw [hnormalizedRaw]
  calc
    (lg21NormalizedRestriction accessLaw
      (scoreSkillObservation ⁻¹' selectionEvent)).map scoreSkillObservation =
        lg21NormalizedRestriction (accessLaw.map scoreSkillObservation) selectionEvent := by
          exact lg21_normalizedRestriction_map_preimage accessLaw
            scoreSkillObservation hscoreSkillObservation selectionEvent hselectionEvent
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ joint) selectionEvent := by
          rw [haccessScoreSkill]

/-- The canonical Gaussian score posterior is the literal PBO on an attained
all-take report branch selected by any measurable public report action. -/
theorem lg21HiddenAccessAllTake_arbitraryReport_condDistribMean_ae
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
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hreportPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport
    let actionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
      lg21NormalizedRestriction_isProbability rawLaw reportEvent
        (ne_of_gt hreportPositive) (measure_ne_top _ _)
    letI : IsProbabilityMeasure actionLaw :=
      Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance
        publicObservation.1 publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            scoreSkill.2.2)
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            (scoreSkill.1, scoreSkill.2.1))
          actionLaw publicObservation := by
  intro rawLaw reportEvent actionLaw
  let publicSelection := lg21HiddenAccessPublicReportSelection testFeature candidateReport
  let selectionEvent := lg21BaseScoreSelectionEvent publicSelection
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let selectedLaw := lg21NormalizedRestriction (baseLaw ⊗ₘ joint) selectionEvent
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let rawObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let observation :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  have hselection : MeasurableSet publicSelection := by
    simpa [publicSelection] using
      (lg21HiddenAccessPublicReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hselectionEvent : MeasurableSet selectionEvent := by
    simpa [selectionEvent] using
      (lg21BaseScoreSelectionEvent_measurable publicSelection hselection)
  have hrawObservation : Measurable rawObservation := by
    simpa [rawObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hreportEvent : reportEvent =
      accessEvent ∩ rawObservation ⁻¹' selectionEvent := by
    simpa [reportEvent, accessEvent, rawObservation, selectionEvent,
      publicSelection] using
      (lg21HiddenAccessAllTake_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature candidateReport)
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hrawIntersectionPositive : 0 < rawLaw
      (accessEvent ∩ rawObservation ⁻¹' selectionEvent) := by
    change 0 < rawLaw reportEvent at hreportPositive
    rw [← hreportEvent]
    exact hreportPositive
  have haccessSelectedPositive : 0 < accessLaw
      (rawObservation ⁻¹' selectionEvent) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (rawObservation ⁻¹' selectionEvent)
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw accessEvent
      (rawObservation ⁻¹' selectionEvent) haccessEvent hrawIntersectionPositive
  have haccessScoreSkill : accessLaw.map rawObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map rawObservation = rawLaw.map rawObservation := by
        symm
        simpa [rawLaw, accessLaw, rawObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, rawObservation, joint] using hsourceFactor
  have hselectedPositive : 0 < (baseLaw ⊗ₘ joint) selectionEvent := by
    rw [← haccessScoreSkill, Measure.map_apply hrawObservation hselectionEvent]
    exact haccessSelectedPositive
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability (baseLaw ⊗ₘ joint) selectionEvent
      (ne_of_gt hselectedPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hactionLaw : actionLaw = selectedLaw := by
    simpa [rawLaw, reportEvent, actionLaw, joint, selectionEvent,
      publicSelection] using
      (lg21HiddenAccessAllTake_rawCandidateReportBaseScoreSkillLaw_eq_normalizedPublicSelection
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
        hsourceFactor candidateReport hcandidateReport)
  have hRCD := lg21Gaussian_selectedPublic_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance publicSelection hselection hselectedPositive
  have hRCDAction : condDistrib latent observation actionLaw =ᵐ[
      actionLaw.map observation] gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance := by
    simpa only [hactionLaw] using hRCD
  filter_upwards [hRCDAction] with publicObservation hposterior
  rw [hposterior]
  rfl

/-! ## Literal candidate no-report conditional mean -/

/-- Positive no-access mass makes the arbitrary all-take candidate's literal
`X = 0` base/skill law a probability law. -/
theorem lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool) :
    IsProbabilityMeasure
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateTake := lg21HiddenAccessAllTake testFeature
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature candidateTake candidateReport hnoAccess))
      (measure_ne_top _ _)
  change IsProbabilityMeasure
    ((lg21NormalizedRestriction rawLaw noReportEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature))
  exact Measure.isProbabilityMeasure_map
    (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable

/-- The candidate's literal `X = 0` payoff after all access students take.
It is defined from the normalized raw action law, which retains both the
no-access source population and access students who withhold under the
candidate's public report action. -/
noncomputable def lg21HiddenAccessAllTakeCandidateNoReportValue
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) : ℝ := by
  let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  letI : IsProbabilityMeasure actionLaw :=
    lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
      M hnoAccess testFeature candidateReport
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  exact ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst actionLaw publicBase

/-- The displayed arbitrary-candidate no-report value is, by construction,
the conditional mean under the candidate's own literal raw `X = 0` law.
The statement is intentionally pointwise as an identity of the chosen RCD
version; candidate use remains restricted to the attained positive branch. -/
theorem lg21HiddenAccessAllTake_candidateNoReportValue_eq_condDistribMean
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport
    letI : IsProbabilityMeasure actionLaw :=
      lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
      candidateReport publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase := by
  rfl

/-! ## Candidate record with literal branch values -/

/-- A Gaussian-test candidate with an arbitrary measurable public report
action and explicitly supplied base-only no-report value.  The next
specialization supplies that value from the literal candidate `X = 0` law.
The continuation-integrability field is proved for the supplied action rather
than inherited from a cutoff candidate. -/
noncomputable def lg21HiddenAccessGaussianCandidateWithReportAction
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (noReportValue : Base -> ℝ) :
    LG21OptionalCandidateBranchData ℝ Base ℝ := by
  refine {
    testLaw := fun latentSkill _publicBase =>
      gaussianReal latentSkill noiseVariance.toNNReal
    testLaw_isProbability := ?_
    reportDecision := candidateReport
    reportedValue := lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance
    noReportValue := noReportValue
    continuationValue_integrable := ?_ }
  · intro latentSkill publicBase
    infer_instance
  · intro latentSkill publicBase
    let testLaw := gaussianReal latentSkill noiseVariance.toNNReal
    letI : IsProbabilityMeasure testLaw := by
      dsimp [testLaw]
      infer_instance
    letI : IsFiniteMeasure testLaw := ⟨by simp⟩
    have hdecision : Measurable (fun score : ℝ =>
        candidateReport publicBase score) := by
      exact hcandidateReport.comp (measurable_const.prodMk measurable_id)
    have hreported : Integrable
        (lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase)
        testLaw := by
      simpa [testLaw] using
        (lg21_optional_rawGaussianPosteriorMean_integrable_under_test
          baseMean hbaseMean baseVariance noiseVariance publicBase
          noiseVariance.toNNReal latentSkill)
    have hnoReport : Integrable (fun _score : ℝ => noReportValue publicBase)
        testLaw :=
      integrable_const _
    have hreportSet : MeasurableSet {score : ℝ |
        candidateReport publicBase score = true} :=
      (measurableSet_singleton true).preimage hdecision
    have hnoReportSet : MeasurableSet {score : ℝ |
        candidateReport publicBase score = false} :=
      (measurableSet_singleton false).preimage hdecision
    have hsplit : (fun score : ℝ =>
        if candidateReport publicBase score then
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score
        else noReportValue publicBase) =
        {score : ℝ | candidateReport publicBase score = true}.indicator
          (lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase) +
        {score : ℝ | candidateReport publicBase score = false}.indicator
          (fun _score => noReportValue publicBase) := by
      funext score
      by_cases hreport : candidateReport publicBase score = true <;>
        simp [Set.indicator, hreport]
    rw [hsplit]
    exact (hreported.indicator hreportSet).add
      (hnoReport.indicator hnoReportSet)

@[simp] theorem lg21HiddenAccessGaussianCandidateWithReportAction_reportDecision
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (noReportValue : Base -> ℝ) (publicBase : Base) (score : ℝ) :
    (lg21HiddenAccessGaussianCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance candidateReport
      hcandidateReport noReportValue).reportDecision publicBase score =
      candidateReport publicBase score := by
  rfl

@[simp] theorem lg21HiddenAccessGaussianCandidateWithReportAction_reportedValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (noReportValue : Base -> ℝ) (publicBase : Base) (score : ℝ) :
    (lg21HiddenAccessGaussianCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance candidateReport
      hcandidateReport noReportValue).reportedValue publicBase score =
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase score := by
  rfl

@[simp] theorem lg21HiddenAccessGaussianCandidateWithReportAction_noReportValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (noReportValue : Base -> ℝ) (publicBase : Base) :
    (lg21HiddenAccessGaussianCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance candidateReport
      hcandidateReport noReportValue).noReportValue publicBase =
      noReportValue publicBase := by
  rfl

/-- The arbitrary-report candidate whose `X = 0` value is the literal
conditional mean induced by that same candidate action. -/
noncomputable def lg21HiddenAccessAllTakeLiteralCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
  lg21HiddenAccessGaussianCandidateWithReportAction
    baseMean hbaseMean baseVariance noiseVariance candidateReport hcandidateReport
    (lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
      candidateReport)

/-! ## Source-timed carriers for the literal all-take candidate -/

/-- The whole public-base region has positive raw mass.  Keeping this fact
separate makes the following carrier theorems state the same literal local
PBO contract used by source-timed deviations. -/
theorem lg21HiddenAccessBaseRegion_univ_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature
        (Set.univ : Set (LG21NonTestFeature Feature testFeature -> ℝ))) := by
  have hregion : lg21HiddenAccessBaseRegionEvent testFeature
      (Set.univ : Set (LG21NonTestFeature Feature testFeature -> ℝ)) =
      Set.univ := by
    ext student
    simp [lg21HiddenAccessBaseRegionEvent]
  rw [hregion]
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) := by
    simpa using lg21ContinuousGaussianPopulationLaw_isProbability M
  simp

/-- The arbitrary public report action of the literal all-take candidate has
the canonical Gaussian reported-score PBO under the existing source-timed
carrier.  The candidate report event is not assumed to be a cutoff and the
carrier observes no hidden access coordinate. -/
theorem lg21HiddenAccessAllTakeLiteralCandidate_sourceTimedReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hlocalReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature Set.univ
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)) :
    LG21HiddenAccessSourceTimedCandidateReportPBOOn M testFeature Set.univ
      (lg21HiddenAccessBaseRegion_univ_positive M testFeature)
      (lg21HiddenAccessAllTake testFeature) candidateReport
      (lg21HiddenAccessAllTakeLiteralCandidate M hnoAccess testFeature
        baseMean hbaseMean baseVariance noiseVariance candidateReport
        hcandidateReport)
      hlocalReportPositive := by
  have hreportPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
    simpa only [lg21HiddenAccessLocalRawLaw_univ] using hlocalReportPositive
  have hPBO := lg21HiddenAccessAllTake_arbitraryReport_condDistribMean_ae
    M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance hsourceFactor candidateReport hcandidateReport
    hreportPositive
  unfold LG21HiddenAccessSourceTimedCandidateReportPBOOn
  dsimp only
  simpa only [lg21HiddenAccessLocalRawLaw_univ,
    lg21HiddenAccessAllTakeLiteralCandidate,
    lg21HiddenAccessGaussianCandidateWithReportAction_reportedValue] using hPBO

/-- The literal all-take candidate's `X = 0` continuation value is the
conditional mean of its own raw no-report branch in the source-timed
carrier.  In particular, no-access students remain in the conditioning law. -/
theorem lg21HiddenAccessAllTakeLiteralCandidate_sourceTimedNoReportPBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hlocalNoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature Set.univ
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)) :
    LG21HiddenAccessSourceTimedCandidateNoReportPBOOn M testFeature Set.univ
      (lg21HiddenAccessBaseRegion_univ_positive M testFeature)
      (lg21HiddenAccessAllTake testFeature) candidateReport
      (lg21HiddenAccessAllTakeLiteralCandidate M hnoAccess testFeature
        baseMean hbaseMean baseVariance noiseVariance candidateReport
        hcandidateReport)
      hlocalNoReportPositive := by
  have hnoReportPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := by
    simpa only [lg21HiddenAccessLocalRawLaw_univ] using hlocalNoReportPositive
  letI : IsProbabilityMeasure
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) :=
    lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
      M hnoAccess testFeature candidateReport
  letI : IsFiniteMeasure
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport) := ⟨by simp⟩
  have hvalue : ∀ publicBase,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
        candidateReport publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
          (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
            (lg21HiddenAccessAllTake testFeature) candidateReport) publicBase := by
    intro publicBase
    exact lg21HiddenAccessAllTake_candidateNoReportValue_eq_condDistribMean
      M hnoAccess testFeature candidateReport publicBase
  unfold LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
  dsimp only
  simpa only [lg21HiddenAccessLocalRawLaw_univ,
    lg21HiddenAccessAllTakeLiteralCandidate,
    lg21HiddenAccessGaussianCandidateWithReportAction_noReportValue,
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw] using
    (Filter.Eventually.of_forall hvalue)

/-! ## Arbitrary public no-report source transport -/

/-- The unnormalized latent-skill kernel obtained by selecting an arbitrary
public `(base, score)` set in a Gaussian score/skill kernel, then forgetting
the observed score. -/
def lg21HiddenAccessPublicScoreSelectedSkillKernel
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (selected : Set (Base × ℝ)) : Kernel Base ℝ :=
  (selectedRestrictionKernel joint
    (lg21BaseScoreSelectionEvent selected)).map Prod.snd

instance lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (selected : Set (Base × ℝ)) :
    IsFiniteKernel (lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected) := by
  letI : IsFiniteKernel joint := by infer_instance
  letI : IsFiniteKernel (selectedRestrictionKernel joint
      (lg21BaseScoreSelectionEvent selected)) :=
    selectedRestrictionKernel_isFinite (lg21BaseScoreSelectionEvent selected)
  unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
  infer_instance

/-- The selected skill kernel's total mass is the literal selected
score/skill fibre mass. -/
theorem lg21HiddenAccessPublicScoreSelectedSkillKernel_apply_univ
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (publicBase : Base) :
    lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected publicBase Set.univ =
      joint publicBase
        (selectedFiber (lg21BaseScoreSelectionEvent selected) publicBase) := by
  unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
  rw [Kernel.map_apply _ measurable_snd publicBase,
    Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ,
    selectedRestrictionKernel_apply
      (lg21BaseScoreSelectionEvent_measurable selected hselected)]
  simp

/-- With the whole public score space selected, the selected skill kernel is
the ordinary latent-skill marginal of the Gaussian joint kernel. -/
theorem lg21HiddenAccessPublicScoreSelectedSkillKernel_univ_eq_joint_map_snd
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint] :
    lg21HiddenAccessPublicScoreSelectedSkillKernel joint Set.univ =
      joint.map Prod.snd := by
  ext publicBase target htarget
  unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
  rw [Kernel.map_apply _ measurable_snd publicBase,
    Kernel.map_apply _ measurable_snd publicBase,
    selectedRestrictionKernel_apply]
  · simp [lg21BaseScoreSelectionEvent, selectedFiber]
  · simpa using
      (lg21BaseScoreSelectionEvent_measurable (Base := Base)
        Set.univ MeasurableSet.univ)

/-- The raw fibre mass of an arbitrary public-score selection is measurable
in the public base profile. -/
theorem lg21HiddenAccessPublicScoreRawFibreMass_measurable
    {Base : Type*} [MeasurableSpace Base]
    (joint : Kernel Base (ℝ × ℝ)) [IsMarkovKernel joint]
    (noAccessMass accessMass : ENNReal) (selected : Set (Base × ℝ))
    (hselected : MeasurableSet selected) :
    Measurable (lg21HiddenAccessScoreRawFibreMass
      (lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected)
      noAccessMass accessMass) := by
  have hselectionEvent : MeasurableSet (lg21BaseScoreSelectionEvent selected) :=
    lg21BaseScoreSelectionEvent_measurable selected hselected
  have hselection : Measurable (fun publicBase : Base =>
      joint publicBase
        (selectedFiber (lg21BaseScoreSelectionEvent selected) publicBase)) :=
    Kernel.measurable_kernel_prodMk_left hselectionEvent
  unfold lg21HiddenAccessScoreRawFibreMass
  simp_rw [lg21HiddenAccessPublicScoreSelectedSkillKernel_apply_univ
    joint selected hselected]
  exact measurable_const.add (measurable_const.mul hselection)

/-- Forgetting the score after any measurable public-score selection preserves
integrability of latent skill.  This is needed before expanding the raw
hidden-access mixture; it makes no positivity assumption on the selection. -/
theorem lg21HiddenAccessPublicScoreSelectedSkillKernel_integrable
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (publicBase : Base) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    Integrable (fun latentSkill : ℝ => latentSkill)
      (lg21HiddenAccessPublicScoreSelectedSkillKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        selected publicBase) := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let event := lg21BaseScoreSelectionEvent selected
  let fibre : Set ℝ := {score | (publicBase, score) ∈ selected}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21BaseScoreSelectionEvent_measurable selected hselected)
  have hselectedFiber : selectedFiber event publicBase = fibre ×ˢ Set.univ := by
    ext scoreSkill
    simp [event, fibre, lg21BaseScoreSelectionEvent, selectedFiber]
  have hskillMarginal : (joint publicBase).map Prod.snd =
      gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
    simpa [joint] using
      (lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance publicBase)
  have hintegrableJoint : Integrable Prod.snd (joint publicBase) := by
    have hgaussian : Integrable (fun skill : ℝ => skill)
        (gaussianReal (baseMean publicBase) baseVariance.toNNReal) := by
      exact (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
    rw [← hskillMarginal] at hgaussian
    exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp (by
        simpa [Function.comp_def] using hgaussian)
  have hselectedKernel :
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected publicBase =
        ((joint publicBase).restrict (fibre ×ˢ Set.univ)).map Prod.snd := by
    unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
    rw [Kernel.map_apply _ measurable_snd publicBase,
      selectedRestrictionKernel_apply hevent, hselectedFiber]
  rw [hselectedKernel]
  apply (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
    measurable_snd.aemeasurable).mpr
  simpa [Function.comp_def] using hintegrableJoint.restrict

/-- Selecting a public score set and then forgetting the score integrates
latent skill by the posterior-mean tower over exactly that score set. -/
theorem lg21HiddenAccessPublicScoreSelectedSkillKernel_integral_eq_posteriorScoreIntegral
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (publicBase : Base) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    ∫ latentSkill, latentSkill ∂
      lg21HiddenAccessPublicScoreSelectedSkillKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        selected publicBase =
      ∫ score in {score | (publicBase, score) ∈ selected},
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
          gaussianReal (baseMean publicBase)
            (baseVariance + noiseVariance).toNNReal := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let scoreLaw := gaussianReal (baseMean publicBase)
    (baseVariance + noiseVariance).toNNReal
  let posterior := Kernel.sectR
    (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) publicBase
  let fibre : Set ℝ := {score | (publicBase, score) ∈ selected}
  let event := lg21BaseScoreSelectionEvent selected
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) := by
    exact gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel posterior := by
    dsimp [posterior]
    infer_instance
  letI : IsProbabilityMeasure scoreLaw := by
    dsimp [scoreLaw]
    infer_instance
  letI : IsFiniteMeasure scoreLaw := ⟨by simp⟩
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21BaseScoreSelectionEvent_measurable selected hselected)
  have hfibre : MeasurableSet fibre := by
    change MeasurableSet ((fun score : ℝ => (publicBase, score)) ⁻¹' selected)
    exact hselected.preimage (measurable_const.prodMk measurable_id)
  have hselectedFiber : selectedFiber event publicBase = fibre ×ˢ Set.univ := by
    ext scoreSkill
    simp [event, fibre, lg21BaseScoreSelectionEvent, selectedFiber]
  have hjoint : joint publicBase = scoreLaw ⊗ₘ posterior := by
    simpa [joint, scoreLaw, posterior] using
      (lg21_optional_fullBaseGaussian_jointKernel_apply
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance publicBase)
  have hskillMarginal : (joint publicBase).map Prod.snd =
      gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
    simpa [joint] using
      (lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance publicBase)
  have hintegrableJoint : Integrable Prod.snd (joint publicBase) := by
    have hgaussian : Integrable (fun skill : ℝ => skill)
        (gaussianReal (baseMean publicBase) baseVariance.toNNReal) := by
      exact (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
    rw [← hskillMarginal] at hgaussian
    exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp (by
        simpa [Function.comp_def] using hgaussian)
  have hintegrableSelected : IntegrableOn Prod.snd (fibre ×ˢ Set.univ)
      (scoreLaw ⊗ₘ posterior) := by
    rw [← hjoint]
    exact hintegrableJoint.integrableOn
  have hselectedKernel :
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected publicBase =
        ((joint publicBase).restrict (fibre ×ˢ Set.univ)).map Prod.snd := by
    unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
    rw [Kernel.map_apply _ measurable_snd publicBase,
      selectedRestrictionKernel_apply hevent, hselectedFiber]
  calc
    ∫ latentSkill, latentSkill ∂
        lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected publicBase =
        ∫ scoreSkill, scoreSkill.2 ∂(joint publicBase).restrict
          (fibre ×ˢ Set.univ) := by
            rw [hselectedKernel]
            exact integral_map_of_stronglyMeasurable
              measurable_snd stronglyMeasurable_id
    _ = ∫ scoreSkill in fibre ×ˢ Set.univ, scoreSkill.2 ∂joint publicBase := by rfl
    _ = ∫ score in fibre, ∫ latentSkill, latentSkill ∂posterior score ∂scoreLaw := by
          rw [hjoint]
          simpa only [Measure.compProd, Kernel.const_apply,
            Kernel.prodMkLeft_apply'] using
            (setIntegral_compProd_univ_right
              (κ := Kernel.const Unit scoreLaw)
              (η := Kernel.prodMkLeft Unit posterior) (a := ())
              (fun scoreSkill : ℝ × ℝ => scoreSkill.2) hfibre
              (by simpa [Measure.compProd] using hintegrableSelected))
    _ = ∫ score in {score | (publicBase, score) ∈ selected},
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase score ∂scoreLaw := by
          rfl
    _ = ∫ score in {score | (publicBase, score) ∈ selected},
        lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
          gaussianReal (baseMean publicBase)
            (baseVariance + noiseVariance).toNNReal := by
          rfl

/-- The mass of an arbitrary public-score selected skill kernel is exactly
the Gaussian score-law mass of its public-base fibre. -/
theorem lg21HiddenAccessPublicScoreSelectedSkillKernel_mass_eq_scoreLaw
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (publicBase : Base) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    lg21HiddenAccessPublicScoreSelectedSkillKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)
      selected publicBase Set.univ =
      gaussianReal (baseMean publicBase)
        (baseVariance + noiseVariance).toNNReal
        {score | (publicBase, score) ∈ selected} := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let scoreLaw := gaussianReal (baseMean publicBase)
    (baseVariance + noiseVariance).toNNReal
  let posterior := Kernel.sectR
    (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean baseVariance noiseVariance) publicBase
  let fibre : Set ℝ := {score | (publicBase, score) ∈ selected}
  let event := lg21BaseScoreSelectionEvent selected
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean baseVariance noiseVariance) := by
    exact gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel posterior := by
    dsimp [posterior]
    infer_instance
  letI : IsProbabilityMeasure scoreLaw := by
    dsimp [scoreLaw]
    infer_instance
  letI : IsFiniteMeasure scoreLaw := ⟨by simp⟩
  have hfibre : MeasurableSet fibre := by
    change MeasurableSet ((fun score : ℝ => (publicBase, score)) ⁻¹' selected)
    exact hselected.preimage (measurable_const.prodMk measurable_id)
  have hselectedFiber : selectedFiber event publicBase = fibre ×ˢ Set.univ := by
    ext scoreSkill
    simp [event, fibre, lg21BaseScoreSelectionEvent, selectedFiber]
  have hjoint : joint publicBase = scoreLaw ⊗ₘ posterior := by
    simpa [joint, scoreLaw, posterior] using
      (lg21_optional_fullBaseGaussian_jointKernel_apply
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance publicBase)
  calc
    lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected publicBase Set.univ =
        joint publicBase (selectedFiber event publicBase) := by
          rw [lg21HiddenAccessPublicScoreSelectedSkillKernel_apply_univ
            joint selected hselected]
    _ = joint publicBase (fibre ×ˢ Set.univ) := by rw [hselectedFiber]
    _ = (scoreLaw ⊗ₘ posterior) (fibre ×ˢ Set.univ) := by rw [hjoint]
    _ = scoreLaw fibre := by
      rw [Measure.compProd_apply_prod hfibre MeasurableSet.univ]
      simp
    _ = gaussianReal (baseMean publicBase)
        (baseVariance + noiseVariance).toNNReal
        {score | (publicBase, score) ∈ selected} := by
      rfl

/-- The raw hidden-access `X = 0` kernel has the literal two-component
posterior-score numerator: all no-access scores plus the selected access
scores.  The public selection can be arbitrary and may have zero mass. -/
theorem lg21HiddenAccessPublicScoreRawKernel_integral_eq_posteriorScoreMixture
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (publicBase : Base) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    letI : IsMarkovKernel joint := gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selected
    (∫ latentSkill, latentSkill ∂
      lg21HiddenAccessScoreRawKernel noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass publicBase) =
      noAccessMass.toReal *
        (∫ score,
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
            gaussianReal (baseMean publicBase)
              (baseVariance + noiseVariance).toNNReal) +
      accessMass.toReal *
        (∫ score in {score | (publicBase, score) ∈ selected},
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
            gaussianReal (baseMean publicBase)
              (baseVariance + noiseVariance).toNNReal) := by
  intro joint noAccessKernel accessSelectedSkillKernel
  let scoreLaw := gaussianReal (baseMean publicBase)
    (baseVariance + noiseVariance).toNNReal
  let fibre : Set ℝ := {score | (publicBase, score) ∈ selected}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selected)
  have hskillMarginal : (joint publicBase).map Prod.snd =
      gaussianReal (baseMean publicBase) baseVariance.toNNReal := by
    simpa [joint] using
      (lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
        baseMean hbaseMean baseVariance noiseVariance publicBase)
  have hintegrableJoint : Integrable Prod.snd (joint publicBase) := by
    have hgaussian : Integrable (fun skill : ℝ => skill)
        (gaussianReal (baseMean publicBase) baseVariance.toNNReal) := by
      exact (ProbabilityTheory.memLp_id_gaussianReal'
        (p := 1) (by norm_num)).integrable le_rfl
    rw [← hskillMarginal] at hgaussian
    exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mp (by
        simpa [Function.comp_def] using hgaussian)
  have hnoAccessIntegrable : Integrable (fun latentSkill : ℝ => latentSkill)
      (noAccessKernel publicBase) := by
    dsimp [noAccessKernel]
    rw [Kernel.map_apply _ measurable_snd publicBase]
    apply (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
      measurable_snd.aemeasurable).mpr
    simpa [Function.comp_def] using hintegrableJoint
  have hselectedIntegrable : Integrable (fun latentSkill : ℝ => latentSkill)
      (accessSelectedSkillKernel publicBase) := by
    simpa [accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_integrable
        baseMean hbaseMean baseVariance noiseVariance selected hselected publicBase)
  have hnoAccessIntegral :
      (∫ latentSkill, latentSkill ∂noAccessKernel publicBase) =
        ∫ score,
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂scoreLaw := by
    have huniv :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_integral_eq_posteriorScoreIntegral
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance Set.univ MeasurableSet.univ publicBase
    rw [lg21HiddenAccessPublicScoreSelectedSkillKernel_univ_eq_joint_map_snd] at huniv
    simpa [noAccessKernel, joint, scoreLaw] using huniv
  have hselectedIntegral :
      (∫ latentSkill, latentSkill ∂accessSelectedSkillKernel publicBase) =
        ∫ score in fibre,
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂scoreLaw := by
    simpa [accessSelectedSkillKernel, joint, fibre, scoreLaw] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_integral_eq_posteriorScoreIntegral
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance selected hselected publicBase)
  have hweightedNoAccess : Integrable (fun latentSkill : ℝ => latentSkill)
      (noAccessMass • noAccessKernel publicBase) :=
    hnoAccessIntegrable.smul_measure hnoAccessFinite
  have hweightedSelected : Integrable (fun latentSkill : ℝ => latentSkill)
      (accessMass • accessSelectedSkillKernel publicBase) :=
    hselectedIntegrable.smul_measure haccessFinite
  rw [lg21HiddenAccessScoreRawKernel_apply,
    MeasureTheory.integral_add_measure hweightedNoAccess hweightedSelected,
    MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure,
    hnoAccessIntegral, hselectedIntegral]
  rfl

/-- The literal normalized hidden-access `X = 0` value is the posterior-score
mixture used by the score-local patch algebra.  Both components are retained:
the full no-access score population and the arbitrary public no-report score
selection among access students. -/
theorem lg21HiddenAccessPublicScoreNormalizedKernel_mean_eq_posteriorScoreMixture
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (publicBase : Base) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    letI : IsMarkovKernel joint := gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selected
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selected
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel noAccessMass accessMass
    let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      noAccessMass accessMass hnoAccessFinite haccessFinite
    (∫ latentSkill, latentSkill ∂normalizedKernel publicBase) =
      (noAccessMass.toReal *
          (∫ score,
            lg21OptionalRawGaussianPosteriorMean
              baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
              gaussianReal (baseMean publicBase)
                (baseVariance + noiseVariance).toNNReal) +
        accessMass.toReal *
          (∫ score in {score | (publicBase, score) ∈ selected},
            lg21OptionalRawGaussianPosteriorMean
              baseMean hbaseMean baseVariance noiseVariance publicBase score ∂
              gaussianReal (baseMean publicBase)
                (baseVariance + noiseVariance).toNNReal)) /
        (noAccessMass.toReal + accessMass.toReal *
          (gaussianReal (baseMean publicBase)
            (baseVariance + noiseVariance).toNNReal
            {score | (publicBase, score) ∈ selected}).toReal) := by
  intro joint noAccessKernel accessSelectedSkillKernel fibreMass normalizedKernel
  let scoreLaw := gaussianReal (baseMean publicBase)
    (baseVariance + noiseVariance).toNNReal
  let fibre : Set ℝ := {score | (publicBase, score) ∈ selected}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selected)
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessPublicScoreRawFibreMass_measurable
        joint noAccessMass accessMass selected hselected)
  have hselectedMass :
      accessSelectedSkillKernel publicBase Set.univ = scoreLaw fibre := by
    simpa [accessSelectedSkillKernel, joint, scoreLaw, fibre] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_mass_eq_scoreLaw
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance selected hselected publicBase)
  have hrawMass : fibreMass publicBase =
      noAccessMass + accessMass * scoreLaw fibre := by
    unfold fibreMass lg21HiddenAccessScoreRawFibreMass
    rw [hselectedMass]
  have hrawMass' :
      lg21HiddenAccessScoreRawFibreMass
        accessSelectedSkillKernel noAccessMass accessMass publicBase =
        noAccessMass + accessMass * scoreLaw fibre := by
    simpa [fibreMass] using hrawMass
  have hscoreMassFinite : scoreLaw fibre ≠ ⊤ := measure_ne_top _ _
  have hselectedWeightFinite : accessMass * scoreLaw fibre ≠ ⊤ :=
    ENNReal.mul_ne_top haccessFinite hscoreMassFinite
  rw [show normalizedKernel =
      lg21HiddenAccessScoreNormalizedKernel
        noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass hnoAccessFinite haccessFinite by rfl,
    lg21HiddenAccessScoreNormalizedKernel_apply
      noAccessKernel accessSelectedSkillKernel noAccessMass accessMass
      hnoAccessFinite haccessFinite hfibreMass publicBase,
    MeasureTheory.integral_smul_measure]
  rw [show (∫ latentSkill, latentSkill ∂
      lg21HiddenAccessScoreRawKernel
        noAccessKernel accessSelectedSkillKernel
        noAccessMass accessMass publicBase) =
      noAccessMass.toReal *
        (∫ score,
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂scoreLaw) +
      accessMass.toReal *
        (∫ score in fibre,
          lg21OptionalRawGaussianPosteriorMean
            baseMean hbaseMean baseVariance noiseVariance publicBase score ∂scoreLaw) by
      simpa [noAccessKernel, accessSelectedSkillKernel, joint, scoreLaw, fibre] using
        (lg21HiddenAccessPublicScoreRawKernel_integral_eq_posteriorScoreMixture
          baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance selected hselected
          noAccessMass accessMass hnoAccessFinite haccessFinite publicBase)]
  rw [ENNReal.toReal_inv, hrawMass',
    ENNReal.toReal_add hnoAccessFinite hselectedWeightFinite,
    ENNReal.toReal_mul]
  simp only [scoreLaw, fibre]
  rw [div_eq_mul_inv]
  ring

/-- The access-and-withhold component of an arbitrary all-take public report
rule is exactly the positive-access source mass times the corresponding
selected Gaussian base/skill law.  This is a source measure identity; it
does not condition the school on access. -/
theorem lg21HiddenAccessAllTake_accessTakeNoReportBaseSkillMeasure_eq_smul_selected
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
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport =
      M.accessLaw {true} •
        (baseLaw ⊗ₘ lg21HiddenAccessPublicScoreSelectedSkillKernel
          (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance)
          (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreSkillObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseSkillObservation := lg21HiddenAccessBaseSkillObservation testFeature
  let selection := lg21HiddenAccessPublicNoReportSelection testFeature candidateReport
  let selectionEvent := lg21BaseScoreSelectionEvent selection
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance
  let accessMass := M.accessLaw {true}
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hrawProbability : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsProbabilityMeasure rawLaw := hrawProbability
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have hselection : MeasurableSet selection := by
    simpa [selection] using
      (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hselectionEvent : MeasurableSet selectionEvent := by
    simpa [selectionEvent] using
      (lg21BaseScoreSelectionEvent_measurable selection hselection)
  have hscoreSkillObservation : Measurable scoreSkillObservation := by
    simpa [scoreSkillObservation] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hbaseSkillObservation : Measurable baseSkillObservation := by
    simpa [baseSkillObservation] using
      lg21HiddenAccessBaseSkillObservation_measurable testFeature
  have hrawAccessMass : rawLaw accessEvent = accessMass := by
    rw [show accessEvent = ({true} : Set Bool) ×ˢ Set.univ by
      ext student
      simp [accessEvent],
      lg21ContinuousGaussianPopulation_access_student_factorization]
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
      unfold lg21ContinuousGaussianStudentPrimitiveLaw
      unfold lg21ContinuousGaussianNoiseLaw
      infer_instance
    simpa [accessMass]
  have haccessMass_ne_zero : accessMass ≠ 0 := ne_of_gt haccess
  have haccessMass_ne_top : accessMass ≠ ⊤ := by
    exact measure_ne_top _ _
  have hrawAccessRestrict : rawLaw.restrict accessEvent = accessMass • accessLaw := by
    calc
      rawLaw.restrict accessEvent = (1 : ENNReal) • rawLaw.restrict accessEvent := by simp
      _ = (accessMass * accessMass⁻¹) • rawLaw.restrict accessEvent := by
        rw [ENNReal.mul_inv_cancel haccessMass_ne_zero haccessMass_ne_top]
      _ = accessMass • (accessMass⁻¹ • rawLaw.restrict accessEvent) := by
        rw [smul_smul]
      _ = accessMass • accessLaw := by
        congr 1
        simp [accessLaw, lg21ContinuousGaussianAccessPopulationLaw, rawLaw,
          accessEvent, lg21ContinuousPopulationAccess,
          lg21NormalizedRestriction, hrawAccessMass]
  have hrawSelectionRestrict :
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' selectionEvent) =
        accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' selectionEvent)) := by
    calc
      rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' selectionEvent) =
          (rawLaw.restrict accessEvent).restrict
            (scoreSkillObservation ⁻¹' selectionEvent) := by
              rw [Measure.restrict_restrict]
              · rw [Set.inter_comm]
              · exact hselectionEvent.preimage hscoreSkillObservation
      _ = (accessMass • accessLaw).restrict
          (scoreSkillObservation ⁻¹' selectionEvent) := by
            rw [hrawAccessRestrict]
      _ = accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' selectionEvent)) := by
            rw [Measure.restrict_smul]
  have haccessScoreSkill : accessLaw.map scoreSkillObservation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map scoreSkillObservation = rawLaw.map scoreSkillObservation := by
        symm
        simpa [rawLaw, accessLaw, scoreSkillObservation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, scoreSkillObservation, joint] using hsourceFactor
  have haccessMapRestrict :
      (accessLaw.restrict (scoreSkillObservation ⁻¹' selectionEvent)).map
          baseSkillObservation =
        baseLaw ⊗ₘ lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection := by
    calc
      (accessLaw.restrict (scoreSkillObservation ⁻¹' selectionEvent)).map
          baseSkillObservation =
          ((accessLaw.restrict (scoreSkillObservation ⁻¹' selectionEvent)).map
            scoreSkillObservation).map (Prod.map id Prod.snd) := by
              rw [Measure.map_map (by fun_prop) hscoreSkillObservation]
              rfl
      _ = ((accessLaw.map scoreSkillObservation).restrict selectionEvent).map
          (Prod.map id Prod.snd) := by
            rw [← Measure.restrict_map hscoreSkillObservation hselectionEvent]
      _ = ((baseLaw ⊗ₘ joint).restrict selectionEvent).map
          (Prod.map id Prod.snd) := by rw [haccessScoreSkill]
      _ = baseLaw ⊗ₘ lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection := by
            symm
            unfold lg21HiddenAccessPublicScoreSelectedSkillKernel
            exact compProd_selectedRestrictionKernel_map_snd hselectionEvent
  change (rawLaw.restrict
      (lg21HiddenAccessCandidateAccessTakeNoReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature) candidateReport)).map
      baseSkillObservation = _
  rw [lg21HiddenAccessAllTake_accessTakeNoReportEvent_eq_access_inter_preimage]
  calc
    (rawLaw.restrict (accessEvent ∩ scoreSkillObservation ⁻¹' selectionEvent)).map
        baseSkillObservation =
        (accessMass • (accessLaw.restrict
          (scoreSkillObservation ⁻¹' selectionEvent))).map baseSkillObservation := by
            rw [hrawSelectionRestrict]
    _ = accessMass •
        ((accessLaw.restrict (scoreSkillObservation ⁻¹' selectionEvent)).map
          baseSkillObservation) := by rw [Measure.map_smul]
    _ = accessMass •
        (baseLaw ⊗ₘ lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection) := by
          rw [haccessMapRestrict]

/-- Exact raw-population `(base, skill)` law of an arbitrary all-take
candidate's no-report branch.  The two terms are the full no-access source
component and the access component selected by the candidate's public
no-report action.  This is the common measure identity from which the
incumbent and localized-patch base-fibre PBO formulas are obtained. -/
theorem lg21HiddenAccessAllTake_arbitraryNoReportBaseSkillLaw_eq_normalized_publicScoreRawKernel
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
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
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let accessSelectedSkillKernel := lg21HiddenAccessPublicScoreSelectedSkillKernel
      joint (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport)
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint
        (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport)
    lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature) candidateReport))⁻¹ •
        (baseLaw ⊗ₘ lg21HiddenAccessScoreRawKernel
          noAccessKernel accessSelectedSkillKernel
          (M.accessLaw {false}) (M.accessLaw {true})) := by
  intro joint noAccessKernel accessSelectedSkillKernel
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let candidateTake := lg21HiddenAccessAllTake testFeature
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint
        (lg21HiddenAccessPublicNoReportSelection testFeature candidateReport))
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true})
  have htakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2) := by
    simpa [candidateTake] using lg21HiddenAccessAllTake_measurable testFeature
  have hnoTakeComponent :
      lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure M testFeature
        candidateTake = 0 := by
    unfold lg21HiddenAccessCandidateAccessNoTakeBaseSkillMeasure
    rw [show lg21HiddenAccessCandidateAccessNoTakeEvent testFeature candidateTake = ∅ by
      simpa [candidateTake] using
        lg21HiddenAccessAllTake_candidateAccessNoTakeEvent_eq_empty testFeature]
    simp
  have hnoAccessComponent :
      lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature =
        M.accessLaw {false} • (baseLaw ⊗ₘ noAccessKernel) := by
    calc
      lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature =
          M.accessLaw {false} •
            lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature :=
        lg21HiddenAccessNoAccessBaseSkillMeasure_eq_smul_fullBaseLatent
          M hnoAccess testFeature
      _ = M.accessLaw {false} • (baseLaw ⊗ₘ noAccessKernel) := by
        rw [show lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
            baseLaw ⊗ₘ noAccessKernel by
          simpa [noAccessKernel, joint] using
            (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
              M haccess testFeature baseLaw baseMean hbaseMean
              baseVariance noiseVariance hsourceFactor)]
  have hselectedComponent :
      lg21HiddenAccessCandidateAccessTakeNoReportBaseSkillMeasure M testFeature
        candidateTake candidateReport =
        M.accessLaw {true} • (baseLaw ⊗ₘ accessSelectedSkillKernel) := by
    simpa [candidateTake, accessSelectedSkillKernel, joint] using
      (lg21HiddenAccessAllTake_accessTakeNoReportBaseSkillMeasure_eq_smul_selected
        M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
        hsourceFactor candidateReport hcandidateReport)
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    exact measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := by
    letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
    exact measure_ne_top _ _
  change lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      candidateTake candidateReport = (rawLaw noReportEvent)⁻¹ •
        (baseLaw ⊗ₘ rawKernel)
  rw [lg21HiddenAccessRawCandidate_noReportBaseSkillLaw_eq_normalized_components
    M testFeature candidateTake candidateReport htakeMeasurable hcandidateReport,
    hnoAccessComponent, hnoTakeComponent, hselectedComponent]
  simp only [add_zero]
  rw [← lg21HiddenAccessScoreRawKernel_compProd_eq_raw_mixture
    baseLaw noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite]

/-- The literal raw no-report law of any all-take public report action has
the normalized public-score selected kernel as its conditional skill law
given the public base.  This is the base-fibre RCD identity shared by an
incumbent all-take action and a localized report patch. -/
theorem lg21HiddenAccessAllTake_arbitraryNoReport_condDistrib_eq_publicScoreNormalizedKernel_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
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
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    letI : IsMarkovKernel joint := gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let selection := lg21HiddenAccessPublicNoReportSelection testFeature candidateReport
    let accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
    let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite
    let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport
    letI : IsProbabilityMeasure actionLaw :=
      lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst actionLaw =ᵐ[actionLaw.map Prod.fst]
      normalizedKernel := by
  intro joint noAccessKernel selection accessSelectedSkillKernel fibreMass
    normalizedKernel actionLaw
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection)
  have hselection : MeasurableSet selection := by
    simpa [selection] using
      (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
        candidateReport hcandidateReport)
  have hfibreMass : Measurable fibreMass := by
    simpa [fibreMass, accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreRawFibreMass_measurable
        joint (M.accessLaw {false}) (M.accessLaw {true}) selection hselection)
  letI : IsMarkovKernel normalizedKernel := by
    simpa [normalizedKernel, fibreMass] using
      (lg21HiddenAccessScoreNormalizedKernel_isMarkov
        noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess hnoAccessFinite haccessFinite hfibreMass)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature) candidateReport
  let weightedBase := (rawLaw noReportEvent)⁻¹ • baseLaw.withDensity fibreMass
  let rawKernel := lg21HiddenAccessScoreRawKernel
    noAccessKernel accessSelectedSkillKernel
    (M.accessLaw {false}) (M.accessLaw {true})
  letI : IsProbabilityMeasure actionLaw := by
    simpa [actionLaw] using
      (lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport)
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  have hrawLaw : actionLaw = (rawLaw noReportEvent)⁻¹ •
      (baseLaw ⊗ₘ rawKernel) := by
    simpa [actionLaw, rawLaw, noReportEvent, rawKernel,
      noAccessKernel, accessSelectedSkillKernel, selection, joint] using
      (lg21HiddenAccessAllTake_arbitraryNoReportBaseSkillLaw_eq_normalized_publicScoreRawKernel
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hsourceFactor candidateReport hcandidateReport)
  have hweighted : baseLaw.withDensity fibreMass ⊗ₘ normalizedKernel =
      baseLaw ⊗ₘ rawKernel := by
    simpa [normalizedKernel, rawKernel, fibreMass] using
      (lg21HiddenAccessScoreWeightedBase_compProd_normalizedKernel
        baseLaw noAccessKernel accessSelectedSkillKernel
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccess hnoAccessFinite haccessFinite hfibreMass)
  have hfactor : actionLaw = weightedBase ⊗ₘ normalizedKernel := by
    calc
      actionLaw = (rawLaw noReportEvent)⁻¹ •
          (baseLaw ⊗ₘ rawKernel) := hrawLaw
      _ = (rawLaw noReportEvent)⁻¹ •
          (baseLaw.withDensity fibreMass ⊗ₘ normalizedKernel) := by rw [hweighted]
      _ = weightedBase ⊗ₘ normalizedKernel := by
        rw [Measure.compProd_smul_left]
  have hbaseMarginal : actionLaw.map Prod.fst = weightedBase := by
    calc
      actionLaw.map Prod.fst = (weightedBase ⊗ₘ normalizedKernel).map Prod.fst := by
        rw [hfactor]
      _ = weightedBase := Measure.fst_compProd _ _
  have hjoint : actionLaw.map (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      (baseSkill.1, baseSkill.2)) =
      actionLaw.map Prod.fst ⊗ₘ normalizedKernel := by
    calc
      actionLaw.map (fun baseSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
          (baseSkill.1, baseSkill.2)) = actionLaw := by
            simpa using (Measure.map_id actionLaw)
      _ = weightedBase ⊗ₘ normalizedKernel := hfactor
      _ = actionLaw.map Prod.fst ⊗ₘ normalizedKernel := by rw [hbaseMarginal]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    measurable_fst measurable_snd hjoint

/-- The displayed no-report value of the literal all-take candidate equals
the mean of the same arbitrary-public-selection normalized kernel on its
attained base marginal. -/
theorem lg21HiddenAccessAllTakeLiteralCandidate_noReportValue_eq_publicScoreNormalizedKernelMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
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
            baseMean hbaseMean baseVariance noiseVariance)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool)
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2))
    (hnoAccessFinite : M.accessLaw {false} ≠ ⊤)
    (haccessFinite : M.accessLaw {true} ≠ ⊤) :
    let joint := gaussianSignalJointKernel
      baseMean hbaseMean baseVariance noiseVariance
    letI : IsMarkovKernel joint := gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean baseVariance noiseVariance
    let noAccessKernel := joint.map Prod.snd
    letI : IsMarkovKernel noAccessKernel :=
      Kernel.IsMarkovKernel.map joint measurable_snd
    let selection := lg21HiddenAccessPublicNoReportSelection testFeature candidateReport
    let accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel joint selection
    letI : IsFiniteKernel accessSelectedSkillKernel :=
      lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection
    let fibreMass := lg21HiddenAccessScoreRawFibreMass
      accessSelectedSkillKernel (M.accessLaw {false}) (M.accessLaw {true})
    let normalizedKernel := lg21HiddenAccessScoreNormalizedKernel
      noAccessKernel accessSelectedSkillKernel
      (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite
    let actionLaw := lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
      (lg21HiddenAccessAllTake testFeature) candidateReport
    letI : IsProbabilityMeasure actionLaw :=
      lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
        candidateReport publicBase =
        ∫ latentSkill, latentSkill ∂normalizedKernel publicBase := by
  intro joint noAccessKernel selection accessSelectedSkillKernel fibreMass
    normalizedKernel actionLaw
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsMarkovKernel noAccessKernel := by
    simpa [noAccessKernel] using Kernel.IsMarkovKernel.map joint measurable_snd
  letI : IsFiniteKernel accessSelectedSkillKernel := by
    simpa [accessSelectedSkillKernel] using
      (lg21HiddenAccessPublicScoreSelectedSkillKernel_isFinite joint selection)
  letI : IsProbabilityMeasure actionLaw := by
    simpa [actionLaw] using
      (lg21HiddenAccessAllTake_candidateNoReportBaseSkillLaw_isProbability
        M hnoAccess testFeature candidateReport)
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  have hcond :=
    lg21HiddenAccessAllTake_arbitraryNoReport_condDistrib_eq_publicScoreNormalizedKernel_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
      baseVariance noiseVariance hsourceFactor candidateReport hcandidateReport
      hnoAccessFinite haccessFinite
  have hvalue : ∀ publicBase,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
        candidateReport publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst actionLaw
          publicBase := by
    intro publicBase
    simpa [actionLaw] using
      (lg21HiddenAccessAllTake_candidateNoReportValue_eq_condDistribMean
        M hnoAccess testFeature candidateReport publicBase)
  filter_upwards [hcond] with publicBase hcondAt
  rw [hvalue publicBase, hcondAt]

end

end LG21TestOptionalPolicies
