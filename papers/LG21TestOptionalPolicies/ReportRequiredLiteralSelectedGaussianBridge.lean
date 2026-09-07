import LG21TestOptionalPolicies.ReportRequiredLocalGaussianCandidate
import LG21TestOptionalPolicies.SelectedConditionalPositiveFibresRCD
import LG21TestOptionalPolicies.SelectedGaussianSignalActionTransport

/-!
# Literal report-required selected-Gaussian source bridge

This module transports the report-required source carrier's PBO identity only
along actually attained selected actions. A total measurable patch is used
internally to move an a.e. equality through a mapped law; each public theorem
returns the literal normalized selected posterior on positive fibres.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib Probability
open scoped ENNReal ProbabilityTheory

theorem lg21_source_reportedPBO_eq_selectedPosteriorMean_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hreporterPositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}) :
    let scoreKernel := gaussianLocationKernel
      baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let reportEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | E.takeDecision observationSkill.2 observationSkill.1.1 = true}
    let reporterLaw := lg21NormalizedRestriction sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}
    ∀ᵐ omega ∂reporterLaw,
      E.reportedPayoff (base omega) (score omega) = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel posteriorKernel reportEvent
          ((base omega, score omega)) := by
  dsimp
  let scoreKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  let posteriorKernel : Kernel (Base × ℝ) ℝ := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let observedLaw : Measure (Base × ℝ) := baseLaw ⊗ₘ scoreKernel
  let reportEvent : Set ((Base × ℝ) × ℝ) :=
    {observationSkill | E.takeDecision observationSkill.2 observationSkill.1.1 = true}
  let sourceReporterEvent : Set Omega :=
    {omega | E.takeDecision (skill omega) (base omega) = true}
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    (observation omega, skill omega)
  let reporterLaw : Measure Omega :=
    lg21NormalizedRestriction sourceLaw sourceReporterEvent
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        E.takeDecision observationSkill.2 observationSkill.1.1) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (S.action_measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hsourceReporterEvent : MeasurableSet sourceReporterEvent := by
    simpa [sourceReporterEvent] using S.actualReporterEvent_measurable
  have hobservation : Measurable observation := S.base_measurable.prodMk S.score_measurable
  have hobservationSkill : Measurable observationSkill :=
    hobservation.prodMk S.skill_measurable
  have hsourceEvent : sourceReporterEvent = observationSkill ⁻¹' reportEvent := by
    rfl
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) hreportEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := posteriorKernel)
      hreportEvent
  letI : IsProbabilityMeasure reporterLaw := by
    dsimp [reporterLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw sourceReporterEvent
      (ne_of_gt hreporterPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  letI : SFinite (selectedBase observedLaw posteriorKernel reportEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel reportEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hrawFactor : sourceLaw.map observationSkill =
      observedLaw ⊗ₘ posteriorKernel := by
    let rawObservationSkill : Omega -> Base × (ℝ × ℝ) := fun omega =>
      (base omega, (score omega, skill omega))
    let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
      MeasurableEquiv.prodAssoc.symm
    have hrawObservationSkill : Measurable rawObservationSkill :=
      S.base_measurable.prodMk (S.score_measurable.prodMk S.skill_measurable)
    have hassociation : Measurable association := MeasurableEquiv.measurable _
    calc
      sourceLaw.map observationSkill =
          (sourceLaw.map rawObservationSkill).map association := by
            rw [Measure.map_map hassociation hrawObservationSkill]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).map association := by
            rw [show sourceLaw.map rawObservationSkill =
              baseLaw ⊗ₘ gaussianSignalJointKernel
                baseMean hbaseMean priorVariance noiseVariance by
              simpa [rawObservationSkill] using hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
            rfl
      _ = observedLaw ⊗ₘ posteriorKernel := by
            simpa [observedLaw, scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization
                baseLaw baseMean hbaseMean priorVariance noiseVariance
                hpriorVariance hnoiseVariance)
  have hselectedPair : reporterLaw.map observationSkill =
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent := by
    calc
      reporterLaw.map observationSkill =
          (lg21NormalizedRestriction sourceLaw sourceReporterEvent).map
            observationSkill := by rfl
      _ = lg21NormalizedRestriction (sourceLaw.map observationSkill) reportEvent := by
        rw [hsourceEvent]
        exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
          hobservationSkill reportEvent hreportEvent
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent := by
        rw [hrawFactor]
  have hselectedFactor :
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent =
        normalizedSelectedBase observedLaw posteriorKernel reportEvent ⊗ₘ patch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := observedLaw) (κ := posteriorKernel) hreportEvent
  have hreporterObservationLaw : reporterLaw.map observation =
      normalizedSelectedBase observedLaw posteriorKernel reportEvent := by
    calc
      reporterLaw.map observation =
          (reporterLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = (lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
          reportEvent).map Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase observedLaw posteriorKernel reportEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel reportEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint : reporterLaw.map observationSkill =
      reporterLaw.map observation ⊗ₘ patch := by
    rw [hselectedPair, hselectedFactor, hreporterObservationLaw]
  have hcondDistrib : condDistrib skill observation reporterLaw =ᵐ[
      reporterLaw.map observation] patch := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation S.skill_measurable hselectedJoint
  have hpatch : patch =ᵐ[reporterLaw.map observation]
      selectedNormalizedKernel posteriorKernel reportEvent := by
    rw [hreporterObservationLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := observedLaw) (κ := posteriorKernel) hreportEvent
  have hcondDistribSelected : condDistrib skill observation reporterLaw =ᵐ[
      reporterLaw.map observation]
      selectedNormalizedKernel posteriorKernel reportEvent := hcondDistrib.trans hpatch
  have hcondExp := condExp_ae_eq_integral_condDistrib'
    hobservation (S.reported_integrable hreporterPositive)
  have hcondDistribPullback : ∀ᵐ omega ∂reporterLaw,
      condDistrib skill observation reporterLaw (observation omega) =
        selectedNormalizedKernel posteriorKernel reportEvent (observation omega) := by
    exact ae_of_ae_map hobservation.aemeasurable hcondDistribSelected
  have hsourcePBO : (fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
      reporterLaw]
      reporterLaw[skill | MeasurableSpace.comap observation inferInstance] := by
    simpa [LG21FullPublicReportRequiredReportedPBO, reporterLaw,
      sourceReporterEvent, observation] using S.reported_pbo hreporterPositive
  filter_upwards [hsourcePBO, hcondExp, hcondDistribPullback] with omega hPBO hExp hKernel
  rw [hPBO, hExp, hKernel]

theorem lg21_source_reporter_selected_extension_factor
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet take
    let reporterLaw := lg21NormalizedRestriction sourceLaw
      {omega | take (base omega) (skill omega) = true}
    let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
      ((base omega, score omega), skill omega)
    reporterLaw.map observationSkill =
      gaussianSignalExtendBaseLatentLaw
        (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) takeEvent)
        noiseVariance := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  let takeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicTakeSet take
  let sourceReporterEvent : Set Omega :=
    {omega | take (base omega) (skill omega) = true}
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    ((base omega, score omega), skill omega)
  let reporterLaw : Measure Omega :=
    lg21NormalizedRestriction sourceLaw sourceReporterEvent
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  have hobservationSkill : Measurable observationSkill :=
    (hbase.prodMk hscore).prodMk hskill
  let reportEvent : Set ((Base × ℝ) × ℝ) :=
    gaussianSignalExtendedSelectionEvent takeEvent
  have hreportEvent : MeasurableSet reportEvent := by
    exact htakeEvent.preimage (by fun_prop)
  have hsourceEvent : sourceReporterEvent = observationSkill ⁻¹' reportEvent := by
    rfl
  have hrawExtension :
      gaussianSignalExtendBaseLatentLaw (baseLaw ⊗ₘ skillKernel) noiseVariance =
        gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
    exact gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
      baseLaw baseMean hbaseMean priorVariance noiseVariance
      (baseLaw ⊗ₘ skillKernel) (by rfl)
  have hrawObservation : sourceLaw.map observationSkill =
      gaussianSignalExtendBaseLatentLaw (baseLaw ⊗ₘ skillKernel) noiseVariance := by
    let rawObservation : Omega -> Base × (ℝ × ℝ) := fun omega =>
      (base omega, (score omega, skill omega))
    let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
      MeasurableEquiv.prodAssoc.symm
    have hrawObservationMeasurable : Measurable rawObservation :=
      hbase.prodMk (hscore.prodMk hskill)
    have hassociation : Measurable association := MeasurableEquiv.measurable _
    calc
      sourceLaw.map observationSkill =
          (sourceLaw.map rawObservation).map association := by
            rw [Measure.map_map hassociation hrawObservationMeasurable]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).map association := by
            rw [show sourceLaw.map rawObservation =
              baseLaw ⊗ₘ gaussianSignalJointKernel
                baseMean hbaseMean priorVariance noiseVariance by
              simpa [rawObservation] using hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
            rfl
      _ = gaussianSignalExtendBaseLatentLaw
          (baseLaw ⊗ₘ skillKernel) noiseVariance := hrawExtension.symm
  calc
    reporterLaw.map observationSkill =
        lg21NormalizedRestriction (sourceLaw.map observationSkill) reportEvent := by
          rw [show reporterLaw = lg21NormalizedRestriction sourceLaw
            (observationSkill ⁻¹' reportEvent) by
              rw [show reporterLaw = lg21NormalizedRestriction sourceLaw
                sourceReporterEvent by rfl, hsourceEvent]]
          exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
            hobservationSkill reportEvent hreportEvent
    _ = lg21NormalizedRestriction
        (gaussianSignalExtendBaseLatentLaw
          (baseLaw ⊗ₘ skillKernel) noiseVariance) reportEvent := by
          rw [hrawObservation]
    _ = gaussianSignalExtendBaseLatentLaw
        (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) takeEvent)
        noiseVariance := by
          simpa [reportEvent] using
            (normalizedRestriction_gaussianSignalExtendBaseLatentLaw
              (baseLaw ⊗ₘ skillKernel) noiseVariance takeEvent htakeEvent)

theorem lg21_source_reporter_selected_base_score_factor
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet take
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by simpa [takeEvent] using
        (lg21ReportRequiredFullPublicTakeSet_measurable take htake))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov
        (κ := skillKernel)
        (by simpa [takeEvent] using
          (lg21ReportRequiredFullPublicTakeSet_measurable take htake))
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov
        selectedSkillPatch noiseVariance
    let reporterLaw := lg21NormalizedRestriction sourceLaw
      {omega | take (base omega) (skill omega) = true}
    let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
      ((base omega, score omega), skill omega)
    reporterLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let takeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicTakeSet take
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch noiseVariance
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch noiseVariance
  let sourceReporterEvent : Set Omega :=
    {omega | take (base omega) (skill omega) = true}
  let reporterLaw : Measure Omega :=
    lg21NormalizedRestriction sourceLaw sourceReporterEvent
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    ((base omega, score omega), skill omega)
  letI : SFinite (selectedBase baseLaw skillKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  letI : SFinite (selectedBase baseLaw skillKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hselectedBaseSkill :
      lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) takeEvent =
        normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ selectedSkillPatch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := baseLaw) (κ := skillKernel) htakeEvent
  have hselectedExtension :
      gaussianSignalExtendBaseLatentLaw
        (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) takeEvent)
        noiseVariance =
      (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := by
    rw [hselectedBaseSkill]
    simpa [scoreSkillKernel] using
      (gaussianSignalExtendBaseLatentLaw_compProd
        (normalizedSelectedBase baseLaw skillKernel takeEvent)
        selectedSkillPatch noiseVariance)
  calc
    reporterLaw.map observationSkill =
        gaussianSignalExtendBaseLatentLaw
          (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) takeEvent)
          noiseVariance := by
            simpa [skillKernel, takeEvent, sourceReporterEvent, reporterLaw,
              observationSkill] using
              (lg21_source_reporter_selected_extension_factor
                hbase hscore hskill baseLaw baseMean hbaseMean priorVariance
                noiseVariance hsourceFactor take htake)
    _ = (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := hselectedExtension

theorem lg21_selectedScoreKernel_eq_selectedGaussianScoreLaw
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (publicBase : Base)
    (htakePositive : selectionMass
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicTakeSet take) publicBase ≠ 0) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet take
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by simpa [takeEvent] using
        (lg21ReportRequiredFullPublicTakeSet_measurable take htake))
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | take publicBase latentSkill = true}) := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let takeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicTakeSet take
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := skillKernel)
      htakeEvent
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch noiseVariance
  let priorLaw : Measure ℝ := gaussianReal (baseMean publicBase)
    priorVariance.toNNReal
  let selected : Set ℝ := {latentSkill | take publicBase latentSkill = true}
  let scoreLaw : Measure ℝ := gaussianReal (baseMean publicBase)
    (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
    (baseMean publicBase) priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let stage : ℝ × ℝ → ℝ × ℝ :=
    fun skillNoise => (skillNoise.1 + skillNoise.2, skillNoise.1)
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((take publicBase) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp (measurable_const.prodMk measurable_id))
  have hselectedPatch : selectedSkillPatch publicBase =
      lg21NormalizedRestriction priorLaw selected := by
    rw [selectedNormalizedKernelAtPositiveFibres_apply_pos
      (κ := skillKernel) htakeEvent publicBase]
    · rw [selectedNormalizedKernel_apply htakeEvent]
      rw [gaussianLocationKernel_apply]
      congr 1
    · simpa [skillKernel, takeEvent] using htakePositive
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  have hscoreSkill : scoreSkillKernel publicBase =
      ((lg21NormalizedRestriction priorLaw selected).prod noiseLaw).map stage := by
    rw [show scoreSkillKernel publicBase =
      ((selectedSkillPatch publicBase).prod noiseLaw).map stage by
        unfold scoreSkillKernel gaussianSignalJointKernelOfLatentKernel
        rw [Kernel.map_apply _ hstage, Kernel.prod_apply, Kernel.const_apply]]
    rw [hselectedPatch]
  have hselectedJoint : lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event =
      ((lg21NormalizedRestriction priorLaw selected).prod noiseLaw).map stage := by
    simpa [priorLaw, scoreLaw, posterior, event, noiseLaw, stage] using
      (normalizedRestriction_gaussianSignal_scoreLatent
        (baseMean publicBase) priorVariance noiseVariance selected
        hpriorVariance hnoiseVariance hselectedMeasurable)
  have hfirst : (lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event).map
      Prod.fst = normalizedSelectedBase scoreLaw posterior event := by
    letI : IsMarkovKernel posterior :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    exact normalizedRestriction_map_fst_eq_normalizedSelectedBase
      (μ := scoreLaw) (κ := posterior)
      (MeasurableSet.univ.prod hselectedMeasurable)
  calc
    (scoreSkillKernel.map Prod.fst) publicBase =
        (scoreSkillKernel publicBase).map Prod.fst := by
          rw [Kernel.map_apply _ measurable_fst]
    _ = (lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event).map Prod.fst := by
          rw [hscoreSkill, hselectedJoint]
    _ = normalizedSelectedBase scoreLaw posterior event := hfirst

theorem lg21_selectedReporterPatch_eq_fixedSelectedGaussianPosterior
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (publicBase : Base) (observedScore : ℝ)
    (htakePositive : selectionMass
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicTakeSet take) publicBase ≠ 0) :
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let reportEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | take observationSkill.1.1 observationSkill.2 = true}
    let fixedPosterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
      (baseMean publicBase) priorVariance noiseVariance
    letI : IsMarkovKernel fixedPosterior :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        (baseMean publicBase) priorVariance noiseVariance
    let patch := selectedNormalizedKernelAtPositiveFibres
      (κ := posteriorKernel)
      (by
        change MeasurableSet
          ((fun observationSkill : (Base × ℝ) × ℝ =>
            take observationSkill.1.1 observationSkill.2) ⁻¹' ({true} : Set Bool))
        exact (measurableSet_singleton true).preimage
          (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    patch (publicBase, observedScore) =
      selectedNormalizedKernel fixedPosterior
        (Set.univ ×ˢ {latentSkill | take publicBase latentSkill = true})
        observedScore := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let posteriorKernel : Kernel (Base × ℝ) ℝ := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let reportEvent : Set ((Base × ℝ) × ℝ) :=
    {observationSkill | take observationSkill.1.1 observationSkill.2 = true}
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        take observationSkill.1.1 observationSkill.2) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) hreportEvent
  let selected : Set ℝ := {latentSkill | take publicBase latentSkill = true}
  let fixedEvent : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hpriorSelected : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal selected := by
    rw [← lg21_reportRequired_gaussianLocation_take_selectionMass
      baseMean hbaseMean priorVariance.toNNReal take publicBase]
    simpa [skillKernel, selected] using (pos_iff_ne_zero.mpr htakePositive)
  have hposteriorPositive : selectionMass posteriorKernel reportEvent
      (publicBase, observedScore) ≠ 0 := by
    change posteriorKernel (publicBase, observedScore)
      (selectedFiber reportEvent (publicBase, observedScore)) ≠ 0
    rw [gaussianSignalPosteriorBaseKernel_apply]
    have hfiber : selectedFiber reportEvent (publicBase, observedScore) = selected := by
      ext latentSkill
      simp [selectedFiber, reportEvent, selected]
    rw [hfiber]
    have hpositive := lg21_gaussianSignalPosterior_selected_pos
      (baseMean publicBase) priorVariance noiseVariance selected
      hpriorVariance hnoiseVariance hpriorSelected observedScore
    simpa only [gaussianSignalPosteriorKernel_apply] using ne_of_gt hpositive
  change selectedNormalizedKernelAtPositiveFibres
      (κ := posteriorKernel) hreportEvent (publicBase, observedScore) =
    selectedNormalizedKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance)
      fixedEvent observedScore
  rw [selectedNormalizedKernelAtPositiveFibres_apply_pos
    (κ := posteriorKernel) hreportEvent (publicBase, observedScore)
    hposteriorPositive]
  rw [selectedNormalizedKernel_apply hreportEvent]
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((fun latentSkill : ℝ =>
      take publicBase latentSkill) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp (measurable_const.prodMk measurable_id))
  rw [selectedNormalizedKernel_apply
    (MeasurableSet.univ.prod hselectedMeasurable)]
  rw [gaussianSignalPosteriorBaseKernel_apply]
  congr 1
  · rw [gaussianSignalPosteriorKernel_apply]
  · ext latentSkill
    simp [selectedFiber, reportEvent, fixedEvent, selected]

theorem lg21_source_reporter_selected_base_score_marginal
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet take
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by simpa [takeEvent] using
        (lg21ReportRequiredFullPublicTakeSet_measurable take htake))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov
        (κ := skillKernel)
        (by simpa [takeEvent] using
          (lg21ReportRequiredFullPublicTakeSet_measurable take htake))
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov
        selectedSkillPatch noiseVariance
    let reporterLaw := lg21NormalizedRestriction sourceLaw
      {omega | take (base omega) (skill omega) = true}
    reporterLaw.map (fun omega => (base omega, score omega)) =
      normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ
        (scoreSkillKernel.map Prod.fst) := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let takeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicTakeSet take
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch noiseVariance
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch noiseVariance
  let reporterLaw : Measure Omega := lg21NormalizedRestriction sourceLaw
    {omega | take (base omega) (skill omega) = true}
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    ((base omega, score omega), skill omega)
  letI : SFinite (selectedBase baseLaw skillKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hobservationSkill : Measurable observationSkill :=
    (hbase.prodMk hscore).prodMk hskill
  have hfactor : reporterLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        MeasurableEquiv.prodAssoc.symm := by
    simpa [skillKernel, takeEvent, selectedSkillPatch, scoreSkillKernel,
      reporterLaw, observationSkill] using
      (lg21_source_reporter_selected_base_score_factor
        hbase hscore hskill baseLaw baseMean hbaseMean priorVariance noiseVariance
        hsourceFactor take htake)
  calc
    reporterLaw.map (fun omega => (base omega, score omega)) =
        (reporterLaw.map observationSkill).map Prod.fst := by
          rw [Measure.map_map measurable_fst hobservationSkill]
          rfl
    _ = ((normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
          MeasurableEquiv.prodAssoc.symm).map Prod.fst := by rw [hfactor]
    _ = (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
          (Prod.map id Prod.fst) := by
          rw [Measure.map_map measurable_fst (MeasurableEquiv.measurable _)]
          rfl
    _ = normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ
          (scoreSkillKernel.map Prod.fst) := by
          rw [← Measure.compProd_map measurable_fst]

theorem lg21_source_reportedPBO_eq_selectedPatchMean_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hreporterPositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}) :
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let reportEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | E.takeDecision observationSkill.2 observationSkill.1.1 = true}
    let patch := selectedNormalizedKernelAtPositiveFibres
      (κ := posteriorKernel)
      (by
        change MeasurableSet
          ((fun observationSkill : (Base × ℝ) × ℝ =>
            E.takeDecision observationSkill.2 observationSkill.1.1) ⁻¹' ({true} : Set Bool))
        exact (measurableSet_singleton true).preimage
          (S.action_measurable.comp
            ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    let reporterLaw := lg21NormalizedRestriction sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}
    ∀ᵐ omega ∂reporterLaw,
      E.reportedPayoff (base omega) (score omega) = ∫ latentSkill, latentSkill ∂
        patch (base omega, score omega) := by
  dsimp
  let scoreKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  let posteriorKernel : Kernel (Base × ℝ) ℝ := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let observedLaw : Measure (Base × ℝ) := baseLaw ⊗ₘ scoreKernel
  let reportEvent : Set ((Base × ℝ) × ℝ) :=
    {observationSkill | E.takeDecision observationSkill.2 observationSkill.1.1 = true}
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        E.takeDecision observationSkill.2 observationSkill.1.1) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (S.action_measurable.comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) hreportEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := posteriorKernel) hreportEvent
  let sourceReporterEvent : Set Omega :=
    {omega | E.takeDecision (skill omega) (base omega) = true}
  let reporterLaw : Measure Omega :=
    lg21NormalizedRestriction sourceLaw sourceReporterEvent
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    (observation omega, skill omega)
  change ∀ᵐ omega ∂reporterLaw,
    E.reportedPayoff (base omega) (score omega) = ∫ latentSkill, latentSkill ∂
      patch (observation omega)
  have hobservation : Measurable observation := S.base_measurable.prodMk S.score_measurable
  have hobservationSkill : Measurable observationSkill :=
    hobservation.prodMk S.skill_measurable
  have hsourceEvent : sourceReporterEvent = observationSkill ⁻¹' reportEvent := by
    rfl
  letI : SFinite (selectedBase observedLaw posteriorKernel reportEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel reportEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hrawFactor : sourceLaw.map observationSkill =
      observedLaw ⊗ₘ posteriorKernel := by
    let rawObservationSkill : Omega -> Base × (ℝ × ℝ) := fun omega =>
      (base omega, (score omega, skill omega))
    let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
      MeasurableEquiv.prodAssoc.symm
    have hrawObservationSkill : Measurable rawObservationSkill :=
      S.base_measurable.prodMk (S.score_measurable.prodMk S.skill_measurable)
    have hassociation : Measurable association := MeasurableEquiv.measurable _
    calc
      sourceLaw.map observationSkill =
          (sourceLaw.map rawObservationSkill).map association := by
            rw [Measure.map_map hassociation hrawObservationSkill]
            rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance).map association := by
            rw [show sourceLaw.map rawObservationSkill =
              baseLaw ⊗ₘ gaussianSignalJointKernel
                baseMean hbaseMean priorVariance noiseVariance by
              simpa [rawObservationSkill] using hsourceFactor]
      _ = gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
            rfl
      _ = observedLaw ⊗ₘ posteriorKernel := by
            simpa [observedLaw, scoreKernel, posteriorKernel] using
              (gaussianSignalBaseScoreLatentLaw_factorization
                baseLaw baseMean hbaseMean priorVariance noiseVariance
                hpriorVariance hnoiseVariance)
  have hselectedPair : reporterLaw.map observationSkill =
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent := by
    calc
      reporterLaw.map observationSkill =
          (lg21NormalizedRestriction sourceLaw sourceReporterEvent).map
            observationSkill := by rfl
      _ = lg21NormalizedRestriction (sourceLaw.map observationSkill) reportEvent := by
        rw [hsourceEvent]
        exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
          hobservationSkill reportEvent hreportEvent
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent := by
        rw [hrawFactor]
  have hselectedFactor :
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) reportEvent =
        normalizedSelectedBase observedLaw posteriorKernel reportEvent ⊗ₘ patch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := observedLaw) (κ := posteriorKernel) hreportEvent
  have hreporterObservationLaw : reporterLaw.map observation =
      normalizedSelectedBase observedLaw posteriorKernel reportEvent := by
    calc
      reporterLaw.map observation =
          (reporterLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = (lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
          reportEvent).map Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase observedLaw posteriorKernel reportEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel reportEvent :=
        Measure.fst_compProd _ _
  have hpatch : patch =ᵐ[reporterLaw.map observation]
      selectedNormalizedKernel posteriorKernel reportEvent := by
    rw [hreporterObservationLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := observedLaw) (κ := posteriorKernel) hreportEvent
  have hpatchPullback : ∀ᵐ omega ∂reporterLaw,
      patch (observation omega) =
        selectedNormalizedKernel posteriorKernel reportEvent (observation omega) := by
    exact ae_of_ae_map hobservation.aemeasurable hpatch
  have hsourceSelected : ∀ᵐ omega ∂reporterLaw,
      E.reportedPayoff (base omega) (score omega) = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel posteriorKernel reportEvent (observation omega) := by
    simpa [scoreKernel, posteriorKernel, reportEvent, sourceReporterEvent,
      reporterLaw, observation] using
      (lg21_source_reportedPBO_eq_selectedPosteriorMean_ae
        S baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor hreporterPositive)
  filter_upwards [hsourceSelected, hpatchPullback] with omega hsource hpatchEq
  rw [hsource, ← hpatchEq]

theorem lg21_source_reportedPBO_eq_selectedGaussianMean_ae_base
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hreporterPositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}) :
    ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.reportedPayoff publicBase =ᵐ[
        normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance)
          (Set.univ ×ˢ {latentSkill |
            E.takeDecision latentSkill publicBase = true})]
        fun observedScore => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance observedScore)
          {latentSkill | E.takeDecision latentSkill publicBase = true} := by
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let take : Base → ℝ → Bool := fun publicBase latentSkill =>
    E.takeDecision latentSkill publicBase
  let takeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicTakeSet take
  have htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2) := by
    simpa [take] using S.action_measurable
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable take htake)
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch noiseVariance
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch noiseVariance
  let posteriorKernel : Kernel (Base × ℝ) ℝ := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let reportEvent : Set ((Base × ℝ) × ℝ) :=
    {observationSkill | take observationSkill.1.1 observationSkill.2 = true}
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        take observationSkill.1.1 observationSkill.2) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) hreportEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := posteriorKernel) hreportEvent
  let reporterLaw : Measure Omega := lg21NormalizedRestriction sourceLaw
    {omega | take (base omega) (skill omega) = true}
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  have hobservation : Measurable observation :=
    S.base_measurable.prodMk S.score_measurable
  letI : SFinite (selectedBase baseLaw skillKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hsourcePatch : ∀ᵐ omega ∂reporterLaw,
      E.reportedPayoff (base omega) (score omega) = ∫ latentSkill, latentSkill ∂
        patch (observation omega) := by
    simpa [posteriorKernel, reportEvent, patch, reporterLaw, observation, take] using
      (lg21_source_reportedPBO_eq_selectedPatchMean_ae
        S baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor hreporterPositive)
  have hpatchMeanMeasurable : Measurable (fun publicScore : Base × ℝ =>
      ∫ latentSkill, latentSkill ∂patch publicScore) :=
    stronglyMeasurable_id.integral_kernel.measurable
  have hbaseScorePatch : ∀ᵐ publicScore ∂reporterLaw.map observation,
      E.reportedPayoff publicScore.1 publicScore.2 = ∫ latentSkill, latentSkill ∂
        patch publicScore := by
    rw [MeasureTheory.ae_map_iff hobservation.aemeasurable
      (measurableSet_eq_fun S.reportedPayoff_measurable hpatchMeanMeasurable)]
    exact hsourcePatch
  have hreporterBaseScoreLaw : reporterLaw.map observation =
      normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ
        (scoreSkillKernel.map Prod.fst) := by
    simpa [skillKernel, take, takeEvent, selectedSkillPatch, scoreSkillKernel,
      reporterLaw, observation] using
      (lg21_source_reporter_selected_base_score_marginal
        S.base_measurable S.score_measurable S.skill_measurable
        baseLaw baseMean hbaseMean priorVariance noiseVariance hsourceFactor take htake)
  rw [hreporterBaseScoreLaw] at hbaseScorePatch
  have hbyBase := Measure.ae_ae_of_ae_compProd hbaseScorePatch
  have hpositiveBase : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel takeEvent,
      selectionMass skillKernel takeEvent publicBase ≠ 0 :=
    ae_normalizedSelectedBase_positiveFibres
      (μ := baseLaw) (κ := skillKernel) htakeEvent
  filter_upwards [hbyBase, hpositiveBase] with publicBase hscorePatch htakePositive
  have hscoreLaw : (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | take publicBase latentSkill = true}) := by
    simpa [skillKernel, takeEvent, selectedSkillPatch, scoreSkillKernel] using
      (lg21_selectedScoreKernel_eq_selectedGaussianScoreLaw
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance take htake publicBase htakePositive)
  rw [hscoreLaw] at hscorePatch
  filter_upwards [hscorePatch] with observedScore hscoreEq
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hpatchFixed : patch (publicBase, observedScore) =
      selectedNormalizedKernel
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | take publicBase latentSkill = true})
        observedScore := by
    simpa [posteriorKernel, reportEvent, patch, take] using
      (lg21_selectedReporterPatch_eq_fixedSelectedGaussianPosterior
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance take htake publicBase observedScore htakePositive)
  rw [hpatchFixed] at hscoreEq
  let selected : Set ℝ := {latentSkill | take publicBase latentSkill = true}
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((fun latentSkill : ℝ =>
      take publicBase latentSkill) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp (measurable_const.prodMk measurable_id))
  have hfixedKernel : selectedNormalizedKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance)
      (Set.univ ×ˢ selected) observedScore =
      lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        selected := by
    rw [selectedNormalizedKernel_apply
      (MeasurableSet.univ.prod hselectedMeasurable)]
    congr 1
    ext latentSkill
    simp [selectedFiber, selected]
  rw [hfixedKernel] at hscoreEq
  simpa [selected, take] using hscoreEq


theorem lg21_source_noTake_selected_baseSkill_factor
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool)
    (hcurrentTake : Measurable (fun profileSkill : Base × ℝ =>
      currentTake profileSkill.2 profileSkill.1)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let noTakeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => currentTake latentSkill publicBase)
    let sourceNoTakeEvent : Set Omega :=
      {omega | currentTake (skill omega) (base omega) = false}
    let baseSkill : Omega -> Base × ℝ := fun omega => (base omega, skill omega)
    (lg21NormalizedRestriction sourceLaw sourceNoTakeEvent).map baseSkill =
      normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ
        selectedNormalizedKernelAtPositiveFibres (κ := skillKernel)
          (by simpa [noTakeEvent] using
            (lg21ReportRequiredFullPublicNoTakeSet_measurable
              (fun publicBase latentSkill => currentTake latentSkill publicBase)
              hcurrentTake)) := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  let noTakeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicNoTakeSet
      (fun publicBase latentSkill => currentTake latentSkill publicBase)
  let sourceNoTakeEvent : Set Omega :=
    {omega | currentTake (skill omega) (base omega) = false}
  let baseSkill : Omega -> Base × ℝ := fun omega => (base omega, skill omega)
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable
        (fun publicBase latentSkill => currentTake latentSkill publicBase)
        hcurrentTake)
  have hbaseSkill : Measurable baseSkill := hbase.prodMk hskill
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have hbaseSkillFactor : sourceLaw.map baseSkill = baseLaw ⊗ₘ skillKernel := by
    simpa [baseSkill, skillKernel] using
      (lg21_reportRequired_sourceBaseSkill_factorization_of_sourceFactor
        sourceLaw base score skill hbase hscore hskill baseLaw baseMean hbaseMean
        priorVariance noiseVariance hsourceFactor)
  have hsourceEvent : sourceNoTakeEvent = baseSkill ⁻¹' noTakeEvent := by
    rfl
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) hnoTakeEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := skillKernel)
      hnoTakeEvent
  calc
    (lg21NormalizedRestriction sourceLaw sourceNoTakeEvent).map baseSkill =
        lg21NormalizedRestriction (sourceLaw.map baseSkill) noTakeEvent := by
      rw [hsourceEvent]
      exact lg21_normalizedRestriction_map_preimage sourceLaw baseSkill
        hbaseSkill noTakeEvent hnoTakeEvent
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) noTakeEvent := by
      rw [hbaseSkillFactor]
    _ = normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ patch := by
      exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
        (μ := baseLaw) (κ := skillKernel) hnoTakeEvent

theorem lg21_source_noTakePBO_eq_selectedGaussianMean_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hnoTakePositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let noTakeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    let noTakeLaw := lg21NormalizedRestriction sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}
    ∀ᵐ omega ∂noTakeLaw,
      E.noReportPayoff (base omega) = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel skillKernel noTakeEvent (base omega) := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let noTakeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicNoTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
  let sourceNoTakeEvent : Set Omega :=
    {omega | E.takeDecision (skill omega) (base omega) = false}
  let baseSkill : Omega -> Base × ℝ := fun omega => (base omega, skill omega)
  let noTakeLaw : Measure Omega := lg21NormalizedRestriction sourceLaw sourceNoTakeEvent
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
        S.action_measurable)
  have hsourceNoTakeEvent : MeasurableSet sourceNoTakeEvent := by
    simpa [sourceNoTakeEvent] using S.actualNoTakeEvent_measurable
  have hbaseSkill : Measurable baseSkill := S.base_measurable.prodMk S.skill_measurable
  have hsourceEvent : sourceNoTakeEvent = baseSkill ⁻¹' noTakeEvent := by
    rfl
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) hnoTakeEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := skillKernel)
      hnoTakeEvent
  letI : IsProbabilityMeasure noTakeLaw := by
    dsimp [noTakeLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw sourceNoTakeEvent
      (ne_of_gt hnoTakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure noTakeLaw := ⟨by simp⟩
  letI : SFinite (selectedBase baseLaw skillKernel noTakeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel noTakeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hselectedPair : noTakeLaw.map baseSkill =
      lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) noTakeEvent := by
    calc
      noTakeLaw.map baseSkill =
          (lg21NormalizedRestriction sourceLaw sourceNoTakeEvent).map baseSkill := by
            rfl
      _ = lg21NormalizedRestriction (sourceLaw.map baseSkill) noTakeEvent := by
        rw [hsourceEvent]
        exact lg21_normalizedRestriction_map_preimage sourceLaw baseSkill
          hbaseSkill noTakeEvent hnoTakeEvent
      _ = lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) noTakeEvent := by
        rw [show sourceLaw.map baseSkill = baseLaw ⊗ₘ skillKernel by
          simpa [baseSkill, skillKernel] using
            (lg21_reportRequired_sourceBaseSkill_factorization_of_sourceFactor
              sourceLaw base score skill S.base_measurable S.score_measurable
              S.skill_measurable baseLaw baseMean hbaseMean priorVariance
              noiseVariance hsourceFactor)]
  letI : SFinite (selectedBase baseLaw skillKernel noTakeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel noTakeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hselectedFactor :
      lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) noTakeEvent =
        normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ patch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := baseLaw) (κ := skillKernel) hnoTakeEvent
  have hnoTakeBaseLaw : noTakeLaw.map base =
      normalizedSelectedBase baseLaw skillKernel noTakeEvent := by
    calc
      noTakeLaw.map base = (noTakeLaw.map baseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hbaseSkill]
        rfl
      _ = (lg21NormalizedRestriction (baseLaw ⊗ₘ skillKernel) noTakeEvent).map
          Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase baseLaw skillKernel noTakeEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint : noTakeLaw.map baseSkill = noTakeLaw.map base ⊗ₘ patch := by
    rw [hselectedPair, hselectedFactor, hnoTakeBaseLaw]
  have hcondDistrib : condDistrib skill base noTakeLaw =ᵐ[noTakeLaw.map base] patch := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      S.base_measurable S.skill_measurable hselectedJoint
  have hpatch : patch =ᵐ[noTakeLaw.map base]
      selectedNormalizedKernel skillKernel noTakeEvent := by
    rw [hnoTakeBaseLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := baseLaw) (κ := skillKernel) hnoTakeEvent
  have hcondDistribSelected : condDistrib skill base noTakeLaw =ᵐ[noTakeLaw.map base]
      selectedNormalizedKernel skillKernel noTakeEvent := hcondDistrib.trans hpatch
  have hcondExp := condExp_ae_eq_integral_condDistrib'
    S.base_measurable (S.noTake_integrable hnoTakePositive)
  have hcondDistribPullback : ∀ᵐ omega ∂noTakeLaw,
      condDistrib skill base noTakeLaw (base omega) =
        selectedNormalizedKernel skillKernel noTakeEvent (base omega) := by
    exact ae_of_ae_map S.base_measurable.aemeasurable hcondDistribSelected
  have hsourcePBO : (fun omega => E.noReportPayoff (base omega)) =ᵐ[noTakeLaw]
      noTakeLaw[skill | MeasurableSpace.comap base inferInstance] := by
    simpa [LG21FullPublicReportRequiredNoTakePBO, noTakeLaw, sourceNoTakeEvent]
      using S.noTake_pbo hnoTakePositive
  filter_upwards [hsourcePBO, hcondExp, hcondDistribPullback] with omega hPBO hExp hKernel
  rw [hPBO, hExp, hKernel]

theorem lg21_source_noTakePBO_eq_selectedGaussianMean_ae_base
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hnoTakePositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let noTakeEvent : Set (Base × ℝ) :=
      lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw skillKernel noTakeEvent,
      E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel skillKernel noTakeEvent publicBase := by
  dsimp
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let noTakeEvent : Set (Base × ℝ) :=
    lg21ReportRequiredFullPublicNoTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
  let sourceNoTakeEvent : Set Omega :=
    {omega | E.takeDecision (skill omega) (base omega) = false}
  let baseSkill : Omega -> Base × ℝ := fun omega => (base omega, skill omega)
  let noTakeLaw : Measure Omega := lg21NormalizedRestriction sourceLaw sourceNoTakeEvent
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
        S.action_measurable)
  have hbaseSkill : Measurable baseSkill := S.base_measurable.prodMk S.skill_measurable
  have hcurrentTake : Measurable (fun profileSkill : Base × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1) := S.action_measurable
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) hnoTakeEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := skillKernel)
      hnoTakeEvent
  letI : IsProbabilityMeasure noTakeLaw := by
    dsimp [noTakeLaw, sourceNoTakeEvent]
    exact lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hnoTakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure noTakeLaw := ⟨by simp⟩
  letI : SFinite (selectedBase baseLaw skillKernel noTakeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel noTakeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hselectedPair : noTakeLaw.map baseSkill =
      normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ patch := by
    simpa [skillKernel, noTakeEvent, sourceNoTakeEvent, baseSkill, patch] using
      (lg21_source_noTake_selected_baseSkill_factor
        sourceLaw base score skill S.base_measurable S.score_measurable
        S.skill_measurable baseLaw baseMean hbaseMean priorVariance noiseVariance
        hsourceFactor (fun latentSkill publicBase =>
          E.takeDecision latentSkill publicBase) hcurrentTake)
  have hnoTakeBaseLaw : noTakeLaw.map base =
      normalizedSelectedBase baseLaw skillKernel noTakeEvent := by
    calc
      noTakeLaw.map base = (noTakeLaw.map baseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hbaseSkill]
        rfl
      _ = (normalizedSelectedBase baseLaw skillKernel noTakeEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedPair]
      _ = normalizedSelectedBase baseLaw skillKernel noTakeEvent :=
        Measure.fst_compProd _ _
  have hsourceSelected : ∀ᵐ omega ∂noTakeLaw,
      E.noReportPayoff (base omega) = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel skillKernel noTakeEvent (base omega) := by
    simpa [skillKernel, noTakeEvent, sourceNoTakeEvent, noTakeLaw] using
      (lg21_source_noTakePBO_eq_selectedGaussianMean_ae
        S baseLaw baseMean hbaseMean priorVariance noiseVariance hsourceFactor
        hnoTakePositive)
  have hpatch : patch =ᵐ[noTakeLaw.map base]
      selectedNormalizedKernel skillKernel noTakeEvent := by
    rw [hnoTakeBaseLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := baseLaw) (κ := skillKernel) hnoTakeEvent
  have hpatchPullback : ∀ᵐ omega ∂noTakeLaw,
      patch (base omega) = selectedNormalizedKernel skillKernel noTakeEvent
        (base omega) := by
    exact ae_of_ae_map S.base_measurable.aemeasurable hpatch
  have hsourcePatch : ∀ᵐ omega ∂noTakeLaw,
      E.noReportPayoff (base omega) = ∫ latentSkill, latentSkill ∂patch (base omega) := by
    filter_upwards [hsourceSelected, hpatchPullback] with omega hselected hpatchEq
    rw [hselected, hpatchEq]
  have hpatchMeanMeasurable : Measurable (fun publicBase : Base =>
      ∫ latentSkill, latentSkill ∂patch publicBase) :=
    stronglyMeasurable_id.integral_kernel.measurable
  have hbasePatch : ∀ᵐ publicBase ∂noTakeLaw.map base,
      E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂patch publicBase := by
    rw [MeasureTheory.ae_map_iff S.base_measurable.aemeasurable
      (measurableSet_eq_fun S.noReportPayoff_measurable hpatchMeanMeasurable)]
    exact hsourcePatch
  rw [hnoTakeBaseLaw] at hbasePatch
  have hpatchBase : patch =ᵐ[normalizedSelectedBase baseLaw skillKernel noTakeEvent]
      selectedNormalizedKernel skillKernel noTakeEvent := by
    rw [← hnoTakeBaseLaw]
    exact hpatch
  filter_upwards [hbasePatch, hpatchBase] with publicBase hbase hpatchEq
  rw [hbase, hpatchEq]

theorem lg21_source_noTakePBO_eq_fixedSelectedGaussianMean_ae_base
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hnoTakePositive : 0 < sourceLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}) :
    ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw
      (gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal)
      (lg21ReportRequiredFullPublicNoTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)),
      E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂
        lg21NormalizedRestriction
          (gaussianReal (baseMean publicBase) priorVariance.toNNReal)
          {latentSkill | E.takeDecision latentSkill publicBase = false} := by
  let skillKernel : Kernel Base ℝ := gaussianLocationKernel
    baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  let noTakeEvent : Set (Base × ℝ) := lg21ReportRequiredFullPublicNoTakeSet
    (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using
      (lg21ReportRequiredFullPublicNoTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
        S.action_measurable)
  have hselected : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel noTakeEvent,
      E.noReportPayoff publicBase = ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel skillKernel noTakeEvent publicBase := by
    simpa [skillKernel, noTakeEvent] using
      (lg21_source_noTakePBO_eq_selectedGaussianMean_ae_base
        S baseLaw baseMean hbaseMean priorVariance noiseVariance hsourceFactor
        hnoTakePositive)
  filter_upwards [hselected] with publicBase hselectedEq
  rw [selectedNormalizedKernel_apply hnoTakeEvent] at hselectedEq
  rw [gaussianLocationKernel_apply] at hselectedEq
  have hfiber : selectedFiber noTakeEvent publicBase =
      {latentSkill | E.takeDecision latentSkill publicBase = false} := by
    ext latentSkill
    simp [selectedFiber, noTakeEvent, lg21ReportRequiredFullPublicNoTakeSet]
  rw [hfiber] at hselectedEq
  exact hselectedEq

/--
The literal source-carrier closeout for the report-required model.  The only
belief equations used here are the carrier's actual positive-branch PBOs;
the selected Gaussian equations are derived internally on attained fibres.
-/
theorem LG21FullPublicReportRequiredSourceEquilibrium.noPositiveMassNoTake_of_literalGaussianSource
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium sourceLaw base score skill E)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill noiseVariance.toNNReal)
    (hstable : LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
      sourceLaw base score skill
      (S.base_measurable.prodMk (S.score_measurable.prodMk S.skill_measurable))
      (fun latentSkill publicBase => E.takeDecision latentSkill publicBase)) :
    sourceLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  let currentTake : ℝ -> Base -> Bool := fun latentSkill publicBase =>
    E.takeDecision latentSkill publicBase
  let sourceReporterEvent : Set Omega :=
    {omega | currentTake (skill omega) (base omega) = true}
  by_cases hreporterZero : sourceLaw sourceReporterEvent = 0
  · have hcurrentTake : Measurable (fun omega =>
        currentTake (skill omega) (base omega)) := by
      simpa [currentTake] using
        S.action_measurable.comp (S.base_measurable.prodMk S.skill_measurable)
    have hregionPositive : 0 < sourceLaw (base ⁻¹' (Set.univ : Set Base)) := by
      simp
    have hcurrentZero : sourceLaw (base ⁻¹' (Set.univ : Set Base) ∩
        {omega | currentTake (skill omega) (base omega) = true}) = 0 := by
      simpa [sourceReporterEvent] using hreporterZero
    exact False.elim
      ((lg21_reportRequired_localGaussian_not_stable_of_positive_zeroTaker_region
        sourceLaw base score skill S.base_measurable S.score_measurable
        S.skill_measurable baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor currentTake hcurrentTake Set.univ
        MeasurableSet.univ hregionPositive hcurrentZero) hstable)
  · have hreporterPositive : 0 < sourceLaw
        {omega | E.takeDecision (skill omega) (base omega) = true} := by
      simpa [sourceReporterEvent, currentTake] using
        (pos_iff_ne_zero.mpr hreporterZero)
    by_contra hnoTakeNonzero
    have hnoTakePositive : 0 < sourceLaw
        {omega | E.takeDecision (skill omega) (base omega) = false} :=
      pos_iff_ne_zero.mpr hnoTakeNonzero
    have hreportedPBO := lg21_source_reportedPBO_eq_selectedGaussianMean_ae_base
      S baseLaw baseMean hbaseMean priorVariance noiseVariance hpriorVariance
      hnoiseVariance hsourceFactor hreporterPositive
    have hnoTakePBO := lg21_source_noTakePBO_eq_fixedSelectedGaussianMean_ae_base
      S baseLaw baseMean hbaseMean priorVariance noiseVariance hsourceFactor
      hnoTakePositive
    exact hnoTakeNonzero
      (lg21_reportRequired_allTake_of_ae_selectedGaussianPBO_and_sourceFactor
        sourceLaw base score skill S.base_measurable S.score_measurable
        S.skill_measurable baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance hsourceFactor E S.take_best_response
        S.action_measurable htestLaw hreportedPBO hnoTakePBO hstable)

/--
Paper-facing report-required Lemma 4.1 endpoint for the literal positive-access
continuous Gaussian population.  The caller supplies the inspectable source
carrier, whose PBO fields apply only on actual positive action branches; this
theorem obtains the population Gaussian factorization and invokes the literal
source closeout without a separate selected-PBO premise.
-/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ)
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∀ (S : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill E),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        lg21ContinuousPopulationSkill
        (S.base_measurable.prodMk
          (S.score_measurable.prodMk S.skill_measurable))
        (fun latentSkill publicBase => E.takeDecision latentSkill publicBase) →
      (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false} = 0 := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro S hstable
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  exact S.noPositiveMassNoTake_of_literalGaussianSource
    baseLaw baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
    hbaseVariance htestNoiseVariance hsourceFactor htestLaw hstable



end

end LG21TestOptionalPolicies
