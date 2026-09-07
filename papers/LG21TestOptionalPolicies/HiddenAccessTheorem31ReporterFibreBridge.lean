import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge
import LG21TestOptionalPolicies.ReportRequiredLiteralSelectedGaussianBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31PositiveReporterClosure
import AppliedModelingLib.Foundations.Probability.GaussianTranslationAC

/-!
# Hidden-access reporter-fibre source bridge

This module contains only source-law consequences of the literal hidden-access
carrier.  In particular, it disintegrates the a.e. score-stage best response
over the public-base Gaussian score law and transports the resulting null set
to every individual Gaussian test draw.  It does not impose a cutoff or a
posterior value on an unselected action branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/--
Conditioning a literal Gaussian source on its measurable pre-score taking
action gives the selected Gaussian posterior a.e. given the public
`(base, score)` observation.  This is a law-level result: it does not use a
payoff or complete an unreached public action branch.

The result is kept source-neutral because the hidden-access proof needs it
before subsequently restricting the already-selected taker law to the later
report action.
-/
theorem lg21_source_taker_condDistrib_eq_selectedGaussianPosterior_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {sourceLaw : Measure Omega} [IsProbabilityMeasure sourceLaw] [IsFiniteMeasure sourceLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2))
    (htakePositive : 0 < sourceLaw
      {omega | take (base omega) (skill omega) = true}) :
    let scoreKernel := gaussianLocationKernel
      baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let takeEvent : Set ((Base × ℝ) × ℝ) :=
      {observationSkill | take observationSkill.1.1 observationSkill.2 = true}
    let takerLaw := lg21NormalizedRestriction sourceLaw
      {omega | take (base omega) (skill omega) = true}
    letI : IsProbabilityMeasure takerLaw :=
      lg21NormalizedRestriction_isProbability sourceLaw
        {omega | take (base omega) (skill omega) = true}
        (ne_of_gt htakePositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
    ∀ᵐ omega ∂takerLaw,
      condDistrib skill (fun omega => (base omega, score omega)) takerLaw
          (base omega, score omega) =
        selectedNormalizedKernel posteriorKernel takeEvent
          (base omega, score omega) := by
  intro scoreKernel posteriorKernel takeEvent takerLaw
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov
      baseMean hbaseMean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability sourceLaw
      {omega | take (base omega) (skill omega) = true}
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  let observedLaw : Measure (Base × ℝ) := baseLaw ⊗ₘ scoreKernel
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  let observationSkill : Omega -> (Base × ℝ) × ℝ := fun omega =>
    (observation omega, skill omega)
  let sourceTakeEvent : Set Omega :=
    {omega | take (base omega) (skill omega) = true}
  have htakeEvent : MeasurableSet takeEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        take observationSkill.1.1 observationSkill.2) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hobservationSkill : Measurable observationSkill :=
    hobservation.prodMk hskill
  have hsourceTakeEvent : sourceTakeEvent = observationSkill ⁻¹' takeEvent := by
    rfl
  let patch := selectedNormalizedKernelAtPositiveFibres
    (κ := posteriorKernel) htakeEvent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := posteriorKernel) htakeEvent
  letI : SFinite (selectedBase observedLaw posteriorKernel takeEvent) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel takeEvent) := by
    unfold normalizedSelectedBase
    infer_instance
  have hrawFactor : sourceLaw.map observationSkill =
      observedLaw ⊗ₘ posteriorKernel := by
    let rawObservationSkill : Omega -> Base × (ℝ × ℝ) := fun omega =>
      (base omega, (score omega, skill omega))
    let association : Base × (ℝ × ℝ) -> (Base × ℝ) × ℝ :=
      MeasurableEquiv.prodAssoc.symm
    have hrawObservationSkill : Measurable rawObservationSkill :=
      hbase.prodMk (hscore.prodMk hskill)
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
  have hselectedPair : takerLaw.map observationSkill =
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent := by
    calc
      takerLaw.map observationSkill =
          (lg21NormalizedRestriction sourceLaw sourceTakeEvent).map
            observationSkill := by rfl
      _ = lg21NormalizedRestriction (sourceLaw.map observationSkill) takeEvent := by
        rw [hsourceTakeEvent]
        exact lg21_normalizedRestriction_map_preimage sourceLaw observationSkill
          hobservationSkill takeEvent htakeEvent
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent := by
        rw [hrawFactor]
  have hselectedFactor :
      lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel) takeEvent =
        normalizedSelectedBase observedLaw posteriorKernel takeEvent ⊗ₘ patch := by
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := observedLaw) (κ := posteriorKernel) htakeEvent
  have htakerObservationLaw : takerLaw.map observation =
      normalizedSelectedBase observedLaw posteriorKernel takeEvent := by
    calc
      takerLaw.map observation =
          (takerLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = (lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
          takeEvent).map Prod.fst := by rw [hselectedPair]
      _ = (normalizedSelectedBase observedLaw posteriorKernel takeEvent ⊗ₘ patch).map
          Prod.fst := by rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel takeEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint : takerLaw.map observationSkill =
      takerLaw.map observation ⊗ₘ patch := by
    rw [hselectedPair, hselectedFactor, htakerObservationLaw]
  have hcondDistrib : condDistrib skill observation takerLaw =ᵐ[
      takerLaw.map observation] patch := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hskill hselectedJoint
  have hpatch : patch =ᵐ[takerLaw.map observation]
      selectedNormalizedKernel posteriorKernel takeEvent := by
    rw [htakerObservationLaw]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := observedLaw) (κ := posteriorKernel) htakeEvent
  have hcondDistribSelected : condDistrib skill observation takerLaw =ᵐ[
      takerLaw.map observation]
      selectedNormalizedKernel posteriorKernel takeEvent := hcondDistrib.trans hpatch
  exact ae_of_ae_map hobservation.aemeasurable hcondDistribSelected

/--
The literal source's a.e. score-stage best response can be localized to
almost every public base.  The factorization is an equality of actual source
laws, so the result does not inspect or classify the reporting action.
-/
theorem lg21HiddenAccess_reportBestResponse_ae_by_base_of_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (scoreKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    [IsMarkovKernel scoreKernel]
    (hfactor : lg21HiddenAccessAccessBaseScoreLaw M testFeature =
      baseLaw ⊗ₘ scoreKernel) :
    ∀ᵐ publicBase ∂baseLaw,
      ∀ᵐ score ∂scoreKernel publicBase,
        E.reportDecision publicBase score = true ->
          E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase score := by
  have hbest := (E.optionalReportBestResponse_ae hreportBest).1
  rw [hfactor] at hbest
  exact Measure.ae_ae_of_ae_compProd hbest

/--
After the source-law Fubini step, every individual nondegenerate Gaussian
test draw sees the same a.e. reporting best response.  This uses only
absolute continuity of Gaussian laws; it is not an off-path PBO completion.
-/
theorem lg21HiddenAccess_reportBestResponse_ae_under_eachGaussianTestLaw_of_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (htestLaw : ∀ skill publicBase,
      E.testLaw skill publicBase = gaussianReal skill noiseVariance.toNNReal)
    (hfactor : lg21HiddenAccessAccessBaseScoreLaw M testFeature =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal) :
    ∀ᵐ publicBase ∂baseLaw, ∀ skill,
      ∀ᵐ score ∂E.testLaw skill publicBase,
        E.reportDecision publicBase score = true ->
          E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase score := by
  let scoreKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean
      (baseVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (baseVariance + noiseVariance).toNNReal)
  have hbyBase := lg21HiddenAccess_reportBestResponse_ae_by_base_of_factorization
    E hreportBest baseLaw scoreKernel (by simpa [scoreKernel] using hfactor)
  filter_upwards [hbyBase] with publicBase hscore skill
  have hscoreLaw : scoreKernel publicBase =
      gaussianReal (baseMean publicBase)
        (baseVariance + noiseVariance).toNNReal := by
    simp [scoreKernel, gaussianLocationKernel_apply]
  have hraw : ∀ᵐ score ∂gaussianReal (baseMean publicBase)
      (baseVariance + noiseVariance).toNNReal,
      E.reportDecision publicBase score = true ->
        E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase score := by
    simpa [hscoreLaw] using hscore
  rw [htestLaw skill publicBase]
  exact AppliedModelingLib.Probability.ae_of_absolutelyContinuous
    (AppliedModelingLib.Probability.gaussianReal_absolutelyContinuous_of_positive_variances
      skill (baseMean publicBase)
      (Real.toNNReal_pos.mpr hnoiseVariance)
      (Real.toNNReal_pos.mpr (add_pos hbaseVariance hnoiseVariance))) hraw

/-- The law-level positive-reporter construction used by the literal source
specialization below.  Its only public-PBO transport step is through the
measurable displayed payoff on the attained reporter law. -/
private theorem positiveReporterSelectedGaussianFibre_ae_of_gaussianFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision))
    (hreportedPayoff : Measurable (fun publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.reportedPayoff publicScore.1 publicScore.2))
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase =
        gaussianReal latentSkill noiseVariance.toNNReal) :
    let skillKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
      gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by
        simpa [takeEvent] using
          (lg21ReportRequiredFullPublicTakeSet_measurable
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
            (E.takeDecision_measurable.comp
              (measurable_snd.prodMk measurable_fst))))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov _
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch noiseVariance
    let reportEvent : Set
        ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) :=
      {profile | E.reportDecision profile.1 profile.2.1 = true}
    ∀ᵐ publicBase ∂normalizedSelectedBase
      (normalizedSelectedBase baseLaw skillKernel takeEvent)
      scoreSkillKernel reportEvent,
      LG21PositiveReporterSelectedGaussianFibre E.toOptionalSequentialData
        publicBase (baseMean publicBase) priorVariance noiseVariance
        {latentSkill | E.takeDecision latentSkill publicBase = true} := by
  intro skillKernel takeEvent selectedSkillPatch scoreSkillKernel reportEvent
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
  have htake : Measurable (fun profileSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1) :=
    E.takeDecision_measurable.comp (measurable_snd.prodMk measurable_fst)
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase) htake)
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch noiseVariance
  letI : IsMarkovKernel (scoreSkillKernel.map Prod.fst) :=
    Kernel.IsMarkovKernel.map scoreSkillKernel measurable_fst
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun profile : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        E.reportDecision profile.1 profile.2.1) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (E.reportDecision_measurable.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let latentSkill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let sourceTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | E.takeDecision (latentSkill student) (base student) = true}
  let sourceReportEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision
  let sourceReportSet : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    lg21HiddenAccessReportSet testFeature E.reportDecision
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
  let takerLaw := lg21NormalizedRestriction accessLaw sourceTakeEvent
  let reporterLaw := lg21NormalizedRestriction rawLaw sourceReportEvent
  let observationSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    fun student => (baseScore student, latentSkill student)
  have htakerPositive : 0 < accessLaw sourceTakeEvent := by
    simpa [accessLaw, sourceTakeEvent, latentSkill, base,
      lg21HiddenAccessTakerEvent] using
      (E.accessLaw_takerEvent_positive hreporterPositive)
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw sourceTakeEvent
      (ne_of_gt htakerPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  have hcondTaker := lg21_source_taker_condDistrib_eq_selectedGaussianPosterior_ae
    (sourceLaw := accessLaw) (base := base) (score := score) (skill := latentSkill)
    (by exact lg21HiddenAccessStudentBase_measurable testFeature |> fun h => h.comp measurable_snd)
    (by exact lg21HiddenAccessStudentScore_measurable testFeature |> fun h => h.comp measurable_snd)
    (by exact measurable_fst.comp measurable_snd)
    baseLaw baseMean hbaseMean priorVariance noiseVariance
    hpriorVariance hnoiseVariance
    (by simpa [accessLaw, base, score, latentSkill] using hsourceFactor)
    (fun publicBase q => E.takeDecision q publicBase) htake htakerPositive
  let posteriorKernel : Kernel
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  let takerObservationEvent : Set
      (((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ) :=
    {observationSkill | E.takeDecision observationSkill.2 observationSkill.1.1 = true}
  have hcondTaker' : ∀ᵐ student ∂takerLaw,
      condDistrib latentSkill baseScore takerLaw (baseScore student) =
        selectedNormalizedKernel posteriorKernel takerObservationEvent
          (baseScore student) := by
    simpa [takerLaw, sourceTakeEvent, baseScore, base, score, latentSkill,
      posteriorKernel, takerObservationEvent] using hcondTaker
  have hreporterLaw : reporterLaw =
      lg21NormalizedRestriction takerLaw (baseScore ⁻¹' sourceReportSet) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, sourceReportEvent, baseScore,
      sourceReportSet, base, score, latentSkill,
      lg21HiddenAccessTakerEvent] using
      (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E)
  have hcondReporter : ∀ᵐ student ∂reporterLaw,
      condDistrib latentSkill baseScore takerLaw (baseScore student) =
        selectedNormalizedKernel posteriorKernel takerObservationEvent
          (baseScore student) := by
    rw [hreporterLaw]
    change ∀ᵐ student ∂(takerLaw (baseScore ⁻¹' sourceReportSet))⁻¹ •
        takerLaw.restrict (baseScore ⁻¹' sourceReportSet),
      condDistrib latentSkill baseScore takerLaw (baseScore student) =
        selectedNormalizedKernel posteriorKernel takerObservationEvent
          (baseScore student)
    exact Measure.ae_smul_measure (ae_restrict_of_ae hcondTaker') _
  have hreportedSource := E.reportedPayoff_eq_takerBaseScoreCondMean_ae hreporterPositive
  have hreported : (fun student => E.reportedPayoff (base student) (score student)) =ᵐ[
      reporterLaw]
      fun student => ∫ q, q ∂condDistrib latentSkill baseScore takerLaw
        (baseScore student) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, sourceReportEvent, takerLaw,
      reporterLaw, baseScore, sourceReportSet, base, score, latentSkill,
      lg21HiddenAccessTakerEvent] using hreportedSource
  have hreportedSelected : ∀ᵐ student ∂reporterLaw,
      E.reportedPayoff (base student) (score student) =
        ∫ q, q ∂selectedNormalizedKernel posteriorKernel takerObservationEvent
          (baseScore student) := by
    filter_upwards [hreported, hcondReporter] with student hPBO hcond
    rw [hPBO, hcond]
  let rawObservation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
    fun student => (base student, (score student, latentSkill student))
  let association : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ≃ᵐ
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  have hbase : Measurable base :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hlatentSkill : Measurable latentSkill := measurable_fst.comp measurable_snd
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hlatentSkill)
  have hobservationSkill : Measurable observationSkill :=
    (hbase.prodMk hscore).prodMk hlatentSkill
  have htakerFactor := lg21_source_reporter_selected_base_score_factor
    (sourceLaw := accessLaw) (base := base) (score := score) (skill := latentSkill)
    hbase hscore hlatentSkill baseLaw baseMean hbaseMean priorVariance noiseVariance
    (by simpa [accessLaw, base, score, latentSkill] using hsourceFactor)
    (fun publicBase q => E.takeDecision q publicBase) htake
  have htakerFactor' : takerLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        association := by
    simpa [takerLaw, sourceTakeEvent, base, score, latentSkill, observationSkill,
      takeEvent, selectedSkillPatch, scoreSkillKernel, association] using htakerFactor
  have htakerRawFactor : takerLaw.map rawObservation =
      normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel := by
    calc
      takerLaw.map rawObservation =
          (takerLaw.map observationSkill).map association.symm := by
            rw [Measure.map_map (MeasurableEquiv.measurable association.symm)
              hobservationSkill]
            rfl
      _ = ((normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
          association).map association.symm := by rw [htakerFactor']
      _ = normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel := by
            rw [Measure.map_map (MeasurableEquiv.measurable association.symm)
              (MeasurableEquiv.measurable association)]
            have hcancel : association.symm ∘ association = id := by
              funext profile
              simp
            rw [hcancel, Measure.map_id]
  have hsourceReportPreimage : baseScore ⁻¹' sourceReportSet =
      rawObservation ⁻¹' reportEvent := by
    rfl
  let reporterPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := scoreSkillKernel) hreportEvent
  letI : IsMarkovKernel reporterPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := scoreSkillKernel) hreportEvent
  let reporterBaseLaw := normalizedSelectedBase
    (normalizedSelectedBase baseLaw skillKernel takeEvent)
    scoreSkillKernel reportEvent
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  letI : SFinite reporterBaseLaw := by
    unfold reporterBaseLaw normalizedSelectedBase selectedBase
    infer_instance
  have hreporterRaw : reporterLaw.map rawObservation =
      lg21NormalizedRestriction
        (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
        reportEvent := by
    calc
      reporterLaw.map rawObservation =
          (lg21NormalizedRestriction takerLaw (rawObservation ⁻¹' reportEvent)).map
            rawObservation := by rw [← hsourceReportPreimage, hreporterLaw]
      _ = lg21NormalizedRestriction (takerLaw.map rawObservation) reportEvent := by
        exact lg21_normalizedRestriction_map_preimage takerLaw rawObservation
          hrawObservation reportEvent hreportEvent
      _ = lg21NormalizedRestriction
          (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
          reportEvent := by rw [htakerRawFactor]
  have hreporterRawFactor : reporterLaw.map rawObservation =
      reporterBaseLaw ⊗ₘ reporterPatch := by
    rw [hreporterRaw]
    exact normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := normalizedSelectedBase baseLaw skillKernel takeEvent)
      (κ := scoreSkillKernel) hreportEvent
  have hreporterBaseScoreLaw : reporterLaw.map baseScore =
      reporterBaseLaw ⊗ₘ (reporterPatch.map Prod.fst) := by
    calc
      reporterLaw.map baseScore =
          (reporterLaw.map rawObservation).map (Prod.map id Prod.fst) := by
            rw [Measure.map_map (measurable_id.prodMap measurable_fst) hrawObservation]
            rfl
      _ = (reporterBaseLaw ⊗ₘ reporterPatch).map (Prod.map id Prod.fst) := by
            rw [hreporterRawFactor]
      _ = reporterBaseLaw ⊗ₘ (reporterPatch.map Prod.fst) := by
            rw [← Measure.compProd_map measurable_fst]
  have htakerBaseScoreLaw := lg21_source_reporter_selected_base_score_marginal
    (sourceLaw := accessLaw) (base := base) (score := score) (skill := latentSkill)
    hbase hscore hlatentSkill baseLaw baseMean hbaseMean priorVariance noiseVariance
    (by simpa [accessLaw, base, score, latentSkill] using hsourceFactor)
    (fun publicBase q => E.takeDecision q publicBase) htake
  have htakerBaseScoreLaw' : takerLaw.map baseScore =
      normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ
        (scoreSkillKernel.map Prod.fst) := by
    simpa [takerLaw, sourceTakeEvent, base, score, latentSkill, baseScore,
      takeEvent, selectedSkillPatch, scoreSkillKernel] using htakerBaseScoreLaw
  have htakerBaseLaw : takerLaw.map base =
      normalizedSelectedBase baseLaw skillKernel takeEvent := by
    calc
      takerLaw.map base = (takerLaw.map baseScore).map Prod.fst := by
        rw [Measure.map_map measurable_fst (hbase.prodMk hscore)]
        rfl
      _ = (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ
          (scoreSkillKernel.map Prod.fst)).map
          Prod.fst := by rw [htakerBaseScoreLaw']
      _ = normalizedSelectedBase baseLaw skillKernel takeEvent :=
        Measure.fst_compProd _ _
  letI : IsProbabilityMeasure
      (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    rw [← htakerBaseLaw]
    exact Measure.isProbabilityMeasure_map hbase.aemeasurable
  have hselectedMeanMeasurable : Measurable (fun publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      ∫ q, q ∂selectedNormalizedKernel posteriorKernel takerObservationEvent
        publicScore) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hPBOBaseScore : ∀ᵐ publicScore ∂reporterLaw.map baseScore,
      E.reportedPayoff publicScore.1 publicScore.2 =
        ∫ q, q ∂selectedNormalizedKernel posteriorKernel takerObservationEvent
          publicScore := by
    rw [MeasureTheory.ae_map_iff hbaseScore.aemeasurable
      (measurableSet_eq_fun
        hreportedPayoff
        hselectedMeanMeasurable)]
    simpa [baseScore] using hreportedSelected
  rw [hreporterBaseScoreLaw] at hPBOBaseScore
  have hPBOFibres := Measure.ae_ae_of_ae_compProd hPBOBaseScore
  have hreporterPositiveBase : ∀ᵐ publicBase ∂reporterBaseLaw,
      selectionMass scoreSkillKernel reportEvent publicBase ≠ 0 := by
    simpa [reporterBaseLaw] using
      (ae_normalizedSelectedBase_positiveFibres
        (μ := normalizedSelectedBase baseLaw skillKernel takeEvent)
        (κ := scoreSkillKernel) hreportEvent)
  have htakePositiveBase : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel takeEvent,
      selectionMass skillKernel takeEvent publicBase ≠ 0 := by
    exact ae_normalizedSelectedBase_positiveFibres
      (μ := baseLaw) (κ := skillKernel) htakeEvent
  have hreporterBase_ac_taker : reporterBaseLaw ≪
      normalizedSelectedBase baseLaw skillKernel takeEvent := by
    change ((normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
      reportEvent)⁻¹ •
      (normalizedSelectedBase baseLaw skillKernel takeEvent).withDensity
        (selectionMass scoreSkillKernel reportEvent) ≪
      normalizedSelectedBase baseLaw skillKernel takeEvent
    exact Measure.smul_absolutelyContinuous.trans
      (withDensity_absolutelyContinuous _ _)
  have htakerBase_ac_base : normalizedSelectedBase baseLaw skillKernel takeEvent ≪
      baseLaw := by
    change ((baseLaw ⊗ₘ skillKernel) takeEvent)⁻¹ •
      baseLaw.withDensity (selectionMass skillKernel takeEvent) ≪ baseLaw
    exact Measure.smul_absolutelyContinuous.trans
      (withDensity_absolutelyContinuous _ _)
  have hreporterBase_ac_base : reporterBaseLaw ≪ baseLaw :=
    hreporterBase_ac_taker.trans htakerBase_ac_base
  have haccessBaseScoreFactor :
      lg21HiddenAccessAccessBaseScoreLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          (priorVariance + noiseVariance).toNNReal := by
    have hassociated : accessLaw.map observationSkill =
        gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance := by
      calc
        accessLaw.map observationSkill =
            (accessLaw.map rawObservation).map association := by
              rw [Measure.map_map (MeasurableEquiv.measurable association)
                hrawObservation]
              rfl
        _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean priorVariance noiseVariance).map association := by
              rw [show accessLaw.map rawObservation =
                baseLaw ⊗ₘ gaussianSignalJointKernel
                  baseMean hbaseMean priorVariance noiseVariance by
                simpa [accessLaw, rawObservation, base, score, latentSkill] using
                  hsourceFactor]
        _ = gaussianSignalBaseScoreLatentLaw
            baseLaw baseMean hbaseMean priorVariance noiseVariance := rfl
    change accessLaw.map baseScore =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        (priorVariance + noiseVariance).toNNReal
    calc
      accessLaw.map baseScore =
          (accessLaw.map observationSkill).map Prod.fst := by
            rw [Measure.map_map measurable_fst hobservationSkill]
            rfl
      _ = (gaussianSignalBaseScoreLatentLaw
          baseLaw baseMean hbaseMean priorVariance noiseVariance).map Prod.fst := by
            rw [hassociated]
      _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          (priorVariance + noiseVariance).toNNReal := by
            rw [gaussianSignalBaseScoreLatentLaw_factorization
              baseLaw baseMean hbaseMean priorVariance noiseVariance
              hpriorVariance hnoiseVariance]
            exact Measure.fst_compProd _ _
  have hsourceBR : ∀ᵐ publicBase ∂baseLaw, ∀ latentSkill,
      ∀ᵐ observedScore ∂E.testLaw latentSkill publicBase,
        E.reportDecision publicBase observedScore = true ->
          E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase observedScore := by
    exact lg21HiddenAccess_reportBestResponse_ae_under_eachGaussianTestLaw_of_factorization
      E hreportBest baseLaw baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance htestLaw haccessBaseScoreFactor
  have hsourceBRReporterBase : ∀ᵐ publicBase ∂reporterBaseLaw, ∀ latentSkill,
      ∀ᵐ observedScore ∂E.testLaw latentSkill publicBase,
        E.reportDecision publicBase observedScore = true ->
          E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase observedScore :=
    hreporterBase_ac_base.ae_le hsourceBR
  have htakePositiveReporterBase : ∀ᵐ publicBase ∂reporterBaseLaw,
      selectionMass skillKernel takeEvent publicBase ≠ 0 :=
    hreporterBase_ac_taker.ae_le htakePositiveBase
  filter_upwards [hPBOFibres, hreporterPositiveBase,
    htakePositiveReporterBase, hsourceBRReporterBase] with publicBase hPBO
      hreporterPositiveAt htakePositiveAt hsourceBRAt
  let selected : Set ℝ :=
    {latentSkill | E.takeDecision latentSkill publicBase = true}
  let reported : Set ℝ :=
    {observedScore | E.reportDecision publicBase observedScore = true}
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet ((fun latentSkill : ℝ =>
      E.takeDecision latentSkill publicBase) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp (measurable_const.prodMk measurable_id))
  have hreportedMeasurable : MeasurableSet reported := by
    change MeasurableSet ((fun observedScore : ℝ =>
      E.reportDecision publicBase observedScore) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (E.reportDecision_measurable.comp (measurable_const.prodMk measurable_id))
  have hselectedPositive : 0 < gaussianReal (baseMean publicBase)
      priorVariance.toNNReal selected := by
    rw [← lg21_reportRequired_gaussianLocation_take_selectionMass
      baseMean hbaseMean priorVariance.toNNReal
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      publicBase]
    simpa [skillKernel, takeEvent, selected] using
      (pos_iff_ne_zero.mpr htakePositiveAt)
  let fixedPosterior : Kernel ℝ ℝ := gaussianSignalPosteriorKernel
    (baseMean publicBase) priorVariance noiseVariance
  letI : IsMarkovKernel fixedPosterior :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hscoreLaw : (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        fixedPosterior
        (Set.univ ×ˢ selected) := by
    simpa [skillKernel, takeEvent, selectedSkillPatch, scoreSkillKernel,
      selected, fixedPosterior] using
      (lg21_selectedScoreKernel_eq_selectedGaussianScoreLaw
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
        htake publicBase htakePositiveAt)
  have hreporterPatchAt : reporterPatch publicBase =
      selectedNormalizedKernel scoreSkillKernel reportEvent publicBase := by
    exact selectedNormalizedKernelAtPositiveFibres_apply_pos hreportEvent
      publicBase hreporterPositiveAt
  have hreporterFiber : selectedFiber reportEvent publicBase =
      Prod.fst ⁻¹' reported := by
    ext scoreSkill
    simp [selectedFiber, reportEvent, reported]
  have hreporterScoreLaw : (reporterPatch.map Prod.fst) publicBase =
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          fixedPosterior (Set.univ ×ˢ selected))
        reported := by
    calc
      (reporterPatch.map Prod.fst) publicBase =
          (reporterPatch publicBase).map Prod.fst := by
            rw [Kernel.map_apply _ measurable_fst]
      _ = (selectedNormalizedKernel scoreSkillKernel reportEvent publicBase).map
          Prod.fst := by rw [hreporterPatchAt]
      _ = (lg21NormalizedRestriction (scoreSkillKernel publicBase)
          (selectedFiber reportEvent publicBase)).map Prod.fst := by
            rw [selectedNormalizedKernel_apply hreportEvent]
      _ = (lg21NormalizedRestriction (scoreSkillKernel publicBase)
          (Prod.fst ⁻¹' reported)).map Prod.fst := by rw [hreporterFiber]
      _ = lg21NormalizedRestriction
          ((scoreSkillKernel publicBase).map Prod.fst) reported := by
            exact lg21_normalizedRestriction_map_preimage
              (scoreSkillKernel publicBase) Prod.fst measurable_fst
              reported hreportedMeasurable
      _ = lg21NormalizedRestriction
          (normalizedSelectedBase
            (gaussianReal (baseMean publicBase)
              (priorVariance + noiseVariance).toNNReal)
            fixedPosterior (Set.univ ×ˢ selected)) reported := by
              rw [← Kernel.map_apply scoreSkillKernel measurable_fst, hscoreLaw]
  have hfixedReporterPositive : 0 <
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        fixedPosterior (Set.univ ×ˢ selected) reported := by
    rw [← hscoreLaw, Kernel.map_apply _ measurable_fst,
      Measure.map_apply measurable_fst hreportedMeasurable]
    change 0 < scoreSkillKernel publicBase (Prod.fst ⁻¹' reported)
    rw [← hreporterFiber]
    exact pos_iff_ne_zero.mpr hreporterPositiveAt
  have htakerObservationEvent : MeasurableSet takerObservationEvent := by
    change MeasurableSet
      ((fun observationSkill :
        ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ =>
        E.takeDecision observationSkill.2 observationSkill.1.1) ⁻¹'
          ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (htake.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hposteriorPositiveAt : ∀ observedScore,
      selectionMass posteriorKernel takerObservationEvent
        (publicBase, observedScore) ≠ 0 := by
    intro observedScore
    change posteriorKernel (publicBase, observedScore)
      (selectedFiber takerObservationEvent (publicBase, observedScore)) ≠ 0
    rw [gaussianSignalPosteriorBaseKernel_apply]
    have hfiber : selectedFiber takerObservationEvent
        (publicBase, observedScore) = selected := by
      ext latentSkill
      simp [selectedFiber, takerObservationEvent, selected]
    rw [hfiber]
    have hpositive := lg21_gaussianSignalPosterior_selected_pos
      (baseMean publicBase) priorVariance noiseVariance selected
      hpriorVariance hnoiseVariance hselectedPositive observedScore
    simpa [posteriorKernel, fixedPosterior,
      gaussianSignalPosteriorKernel_apply] using ne_of_gt hpositive
  have hfixedPBO : E.reportedPayoff publicBase =ᵐ[
      lg21NormalizedRestriction
        (normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          fixedPosterior (Set.univ ×ˢ selected)) reported]
      fun observedScore => ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel fixedPosterior (Set.univ ×ˢ selected)
          observedScore := by
    rw [← hreporterScoreLaw]
    filter_upwards [hPBO] with observedScore hPBOAt
    rw [hPBOAt]
    have hselectedToPatch : selectedNormalizedKernel posteriorKernel
        takerObservationEvent (publicBase, observedScore) =
        selectedNormalizedKernelAtPositiveFibres (κ := posteriorKernel)
          htakerObservationEvent (publicBase, observedScore) := by
      symm
      exact selectedNormalizedKernelAtPositiveFibres_apply_pos htakerObservationEvent
        (publicBase, observedScore) (hposteriorPositiveAt observedScore)
    have hpatchAt := lg21_selectedReporterPatch_eq_fixedSelectedGaussianPosterior
      baseMean hbaseMean priorVariance noiseVariance hpriorVariance hnoiseVariance
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      htake publicBase observedScore htakePositiveAt
    rw [hselectedToPatch]
    simpa [posteriorKernel, takerObservationEvent, fixedPosterior, selected] using
      congrArg (fun measure : Measure ℝ => ∫ latentSkill, latentSkill ∂measure) hpatchAt
  refine ⟨hselectedMeasurable, ?_, hselectedPositive, hreportedMeasurable,
    hpriorVariance, hnoiseVariance, ?_, ?_, ?_, ?_, ?_⟩
  · intro latentSkill
    rfl
  · intro latentSkill
    simpa [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData,
      fixedPosterior] using htestLaw latentSkill publicBase
  · simpa [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData,
      fixedPosterior, selected, reported] using hfixedReporterPositive
  · simpa [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData,
      fixedPosterior, selected, reported] using hfixedPBO
  · have hselectedBR : ∀ᵐ observedScore ∂
        normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          fixedPosterior (Set.univ ×ˢ selected),
        E.reportDecision publicBase observedScore = true ->
          E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase observedScore := by
      have hsourceAtZero := hsourceBRAt 0
      rw [htestLaw 0 publicBase] at hsourceAtZero
      exact
        (lg21_selectedGaussianSignal_selectedScoreLaw_absolutelyContinuous_testLaw
          (baseMean publicBase) priorVariance noiseVariance selected
          hpriorVariance hnoiseVariance 0).ae_le hsourceAtZero
    change ∀ᵐ observedScore ∂
        (normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          fixedPosterior (Set.univ ×ˢ selected) reported)⁻¹ •
          (normalizedSelectedBase
            (gaussianReal (baseMean publicBase)
              (priorVariance + noiseVariance).toNNReal)
            fixedPosterior (Set.univ ×ˢ selected)).restrict reported,
      E.noReportPayoff publicBase ≤ E.reportedPayoff publicBase observedScore
    apply Measure.ae_smul_measure
    have hreportAction : ∀ᵐ observedScore ∂
        (normalizedSelectedBase
          (gaussianReal (baseMean publicBase)
            (priorVariance + noiseVariance).toNNReal)
          fixedPosterior (Set.univ ×ˢ selected)).restrict reported,
        E.reportDecision publicBase observedScore = true := by
      rw [ae_restrict_iff' hreportedMeasurable]
      exact Filter.Eventually.of_forall fun observedScore hscore => hscore
    filter_upwards [ae_restrict_of_ae hselectedBR, hreportAction]
      with observedScore hbest hreport
    exact hbest hreport
  · intro latentSkill
    simpa [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData] using
      hsourceBRAt latentSkill

/-- The source-specialized reporter-fibre theorem uses the model's own
test-noise variance.  It establishes the paper-facing fibre certificate
directly, without a closure assumption or a null-branch PBO completion. -/
theorem lg21HiddenAccess_positiveReporterSelectedGaussianFibre_ae_of_fullGaussianFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let skillKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
      gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by
        simpa [takeEvent] using
          (lg21ReportRequiredFullPublicTakeSet_measurable
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
            (E.takeDecision_measurable.comp
              (measurable_snd.prodMk measurable_fst))))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov _
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch (M.noiseVariance testFeature : ℝ)
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch
        (M.noiseVariance testFeature : ℝ)
    let reportEvent : Set
        ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) :=
      {profile | E.reportDecision profile.1 profile.2.1 = true}
    ∀ᵐ publicBase ∂normalizedSelectedBase
      (normalizedSelectedBase baseLaw skillKernel takeEvent)
      scoreSkillKernel reportEvent,
      LG21PositiveReporterSelectedGaussianFibre E.toOptionalSequentialData
        publicBase (baseMean publicBase) priorVariance
        (M.noiseVariance testFeature : ℝ)
        {latentSkill | E.takeDecision latentSkill publicBase = true} := by
  apply positiveReporterSelectedGaussianFibre_ae_of_gaussianFactorization
    E hreportBest baseLaw baseMean hbaseMean priorVariance
    (M.noiseVariance testFeature : ℝ) hpriorVariance hnoiseVariance
    hsourceFactor hreporterPositive E.reportedPayoff_measurable
  intro latentSkill publicBase
  simpa using E.raw_test_law latentSkill publicBase

/-- The attained reporter base marginal is exactly the final selected base
law.  This exports the population-law identity needed to transport the
fibrewise strict-gain result back to the literal source reporter branch. -/
theorem lg21HiddenAccess_actualReporterBaseMarginal_eq_selectedReporterBase_of_fullGaussianFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let skillKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
      gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel :=
      gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
    let takeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      lg21ReportRequiredFullPublicTakeSet
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (by
        simpa [takeEvent] using
          (lg21ReportRequiredFullPublicTakeSet_measurable
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
            (E.takeDecision_measurable.comp
              (measurable_snd.prodMk measurable_fst))))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov _
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch (M.noiseVariance testFeature : ℝ)
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch
        (M.noiseVariance testFeature : ℝ)
    let reportEvent : Set
        ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) :=
      {profile | E.reportDecision profile.1 profile.2.1 = true}
    (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)).map
        (fun student => lg21HiddenAccessStudentBase testFeature student.2) =
      normalizedSelectedBase
        (normalizedSelectedBase baseLaw skillKernel takeEvent)
        scoreSkillKernel reportEvent := by
  intro skillKernel takeEvent selectedSkillPatch scoreSkillKernel reportEvent
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
  have htake : Measurable (fun profileSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.takeDecision profileSkill.2 profileSkill.1) :=
    E.takeDecision_measurable.comp (measurable_snd.prodMk measurable_fst)
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase) htake)
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch
      (M.noiseVariance testFeature : ℝ)
  have hreportEvent : MeasurableSet reportEvent := by
    change MeasurableSet
      ((fun profile : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        E.reportDecision profile.1 profile.2.1) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      (E.reportDecision_measurable.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let latentSkill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let sourceTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | E.takeDecision (latentSkill student) (base student) = true}
  let sourceReportEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision
  let sourceReportSet : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    lg21HiddenAccessReportSet testFeature E.reportDecision
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
  let takerLaw := lg21NormalizedRestriction accessLaw sourceTakeEvent
  let reporterLaw := lg21NormalizedRestriction rawLaw sourceReportEvent
  let observationSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    fun student => (baseScore student, latentSkill student)
  let rawObservation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
    fun student => (base student, (score student, latentSkill student))
  let association : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ≃ᵐ
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  have htakerPositive : 0 < accessLaw sourceTakeEvent := by
    simpa [accessLaw, sourceTakeEvent, latentSkill, base,
      lg21HiddenAccessTakerEvent] using
      (E.accessLaw_takerEvent_positive hreporterPositive)
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      (lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive)
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw sourceTakeEvent
      (ne_of_gt htakerPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  have hbase : Measurable base :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hlatentSkill : Measurable latentSkill := measurable_fst.comp measurable_snd
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hlatentSkill)
  have hobservationSkill : Measurable observationSkill :=
    (hbase.prodMk hscore).prodMk hlatentSkill
  have htakerFactor := lg21_source_reporter_selected_base_score_factor
    (sourceLaw := accessLaw) (base := base) (score := score) (skill := latentSkill)
    hbase hscore hlatentSkill baseLaw baseMean hbaseMean priorVariance
      (M.noiseVariance testFeature : ℝ)
    (by simpa [accessLaw, base, score, latentSkill] using hsourceFactor)
    (fun publicBase q => E.takeDecision q publicBase) htake
  have htakerFactor' : takerLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
        association := by
    simpa [takerLaw, sourceTakeEvent, base, score, latentSkill, observationSkill,
      takeEvent, selectedSkillPatch, scoreSkillKernel, association] using htakerFactor
  have htakerRawFactor : takerLaw.map rawObservation =
      normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel := by
    calc
      takerLaw.map rawObservation =
          (takerLaw.map observationSkill).map association.symm := by
            rw [Measure.map_map (MeasurableEquiv.measurable association.symm)
              hobservationSkill]
            rfl
      _ = ((normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel).map
          association).map association.symm := by rw [htakerFactor']
      _ = normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel := by
            rw [Measure.map_map (MeasurableEquiv.measurable association.symm)
              (MeasurableEquiv.measurable association)]
            have hcancel : association.symm ∘ association = id := by
              funext profile
              simp
            rw [hcancel, Measure.map_id]
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel takeEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have hreporterLaw : reporterLaw =
      lg21NormalizedRestriction takerLaw (baseScore ⁻¹' sourceReportSet) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, sourceReportEvent, baseScore,
      sourceReportSet, base, score, latentSkill,
      lg21HiddenAccessTakerEvent] using
      (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E)
  have hsourceReportPreimage : baseScore ⁻¹' sourceReportSet =
      rawObservation ⁻¹' reportEvent := by
    rfl
  have hreporterRaw : reporterLaw.map rawObservation =
      lg21NormalizedRestriction
        (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
        reportEvent := by
    calc
      reporterLaw.map rawObservation =
          (lg21NormalizedRestriction takerLaw (rawObservation ⁻¹' reportEvent)).map
            rawObservation := by rw [← hsourceReportPreimage, hreporterLaw]
      _ = lg21NormalizedRestriction (takerLaw.map rawObservation) reportEvent := by
        exact lg21_normalizedRestriction_map_preimage takerLaw rawObservation
          hrawObservation reportEvent hreportEvent
      _ = lg21NormalizedRestriction
          (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
          reportEvent := by rw [htakerRawFactor]
  change reporterLaw.map base =
    normalizedSelectedBase
      (normalizedSelectedBase baseLaw skillKernel takeEvent)
      scoreSkillKernel reportEvent
  calc
    reporterLaw.map base = (reporterLaw.map rawObservation).map Prod.fst := by
      rw [Measure.map_map measurable_fst hrawObservation]
      rfl
    _ = (lg21NormalizedRestriction
        (normalizedSelectedBase baseLaw skillKernel takeEvent ⊗ₘ scoreSkillKernel)
        reportEvent).map Prod.fst := by rw [hreporterRaw]
    _ = normalizedSelectedBase
        (normalizedSelectedBase baseLaw skillKernel takeEvent)
        scoreSkillKernel reportEvent := by
      exact normalizedRestriction_map_fst_eq_normalizedSelectedBase hreportEvent

/-- The positive reporter fibre gives strict source-timed testing gain at
almost every literal raw reporter base.  The conclusion is stated under the
unnormalized reporter marginal used by the source-local all-taking closeout. -/
theorem lg21HiddenAccess_rawReporterBaseStrictGain_ae_of_fullGaussianFactorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ))
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    ∀ᵐ publicBase ∂((lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)).map
        (fun student => lg21HiddenAccessStudentBase testFeature student.2),
      ∀ latentSkill,
        E.noReportPayoff publicBase <
          ∫ observedScore,
            if E.reportDecision publicBase observedScore then
              E.reportedPayoff publicBase observedScore
            else E.noReportPayoff publicBase
            ∂E.testLaw latentSkill publicBase := by
  let skillKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ :=
    gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal
  let takeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    lg21ReportRequiredFullPublicTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
  have htakeEvent : MeasurableSet takeEvent := by
    simpa [takeEvent] using
      (lg21ReportRequiredFullPublicTakeSet_measurable
        (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
        (E.takeDecision_measurable.comp (measurable_snd.prodMk measurable_fst)))
  let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
    (κ := skillKernel) htakeEvent
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) htakeEvent
  let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
    selectedSkillPatch (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov selectedSkillPatch
      (M.noiseVariance testFeature : ℝ)
  let reportEvent : Set
      ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) :=
    {profile | E.reportDecision profile.1 profile.2.1 = true}
  let reporterBaseLaw := normalizedSelectedBase
    (normalizedSelectedBase baseLaw skillKernel takeEvent)
    scoreSkillKernel reportEvent
  have hfibre : ∀ᵐ publicBase ∂reporterBaseLaw,
      LG21PositiveReporterSelectedGaussianFibre E.toOptionalSequentialData
        publicBase (baseMean publicBase) priorVariance
        (M.noiseVariance testFeature : ℝ)
        {latentSkill | E.takeDecision latentSkill publicBase = true} := by
    simpa [skillKernel, takeEvent, selectedSkillPatch, scoreSkillKernel,
      reportEvent, reporterBaseLaw] using
      (lg21HiddenAccess_positiveReporterSelectedGaussianFibre_ae_of_fullGaussianFactorization
        E hreportBest baseLaw baseMean hbaseMean priorVariance hpriorVariance hnoiseVariance
        hsourceFactor hreporterPositive)
  have hselectedGain : ∀ᵐ publicBase ∂reporterBaseLaw, ∀ latentSkill,
      E.noReportPayoff publicBase <
        ∫ observedScore,
          if E.reportDecision publicBase observedScore then
            E.reportedPayoff publicBase observedScore
          else E.noReportPayoff publicBase
          ∂E.testLaw latentSkill publicBase := by
    filter_upwards [hfibre] with publicBase H
    intro latentSkill
    simpa only [LG21HiddenAccessLiteralSourceEquilibriumAE.toOptionalSequentialData,
      lg21OptionalSequentialTakeExpectedPayoff,
      lg21OptionalSequentialContinuationPayoff] using H.strictExpectedGain latentSkill
  have hreporterBaseEq :
      (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)).map
          (fun student => lg21HiddenAccessStudentBase testFeature student.2) =
        reporterBaseLaw := by
    simpa [skillKernel, takeEvent, selectedSkillPatch, scoreSkillKernel,
      reportEvent, reporterBaseLaw] using
      (lg21HiddenAccess_actualReporterBaseMarginal_eq_selectedReporterBase_of_fullGaussianFactorization
        E baseLaw baseMean hbaseMean priorVariance hsourceFactor hreporterPositive)
  have hnormalizedGain : ∀ᵐ publicBase ∂
      (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)).map
          (fun student => lg21HiddenAccessStudentBase testFeature student.2),
      ∀ latentSkill,
        E.noReportPayoff publicBase <
          ∫ observedScore,
            if E.reportDecision publicBase observedScore then
              E.reportedPayoff publicBase observedScore
            else E.noReportPayoff publicBase
            ∂E.testLaw latentSkill publicBase := by
    rw [hreporterBaseEq]
    exact hselectedGain
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let sourceReportEvent :=
    lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hnormal : (lg21NormalizedRestriction rawLaw sourceReportEvent).map base =
      (rawLaw sourceReportEvent)⁻¹ • (rawLaw.restrict sourceReportEvent).map base := by
    unfold lg21NormalizedRestriction
    rw [Measure.map_smul]
  change ∀ᵐ publicBase ∂(rawLaw.restrict sourceReportEvent).map base,
    ∀ latentSkill,
      E.noReportPayoff publicBase <
        ∫ observedScore,
          if E.reportDecision publicBase observedScore then
            E.reportedPayoff publicBase observedScore
          else E.noReportPayoff publicBase
          ∂E.testLaw latentSkill publicBase
  have hmass_ne_top : rawLaw sourceReportEvent ≠ ∞ := measure_ne_top _ _
  have hinv_ne_zero : (rawLaw sourceReportEvent)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr hmass_ne_top
  have hraw_ac_normal : (rawLaw.restrict sourceReportEvent).map base ≪
      (lg21NormalizedRestriction rawLaw sourceReportEvent).map base := by
    rw [hnormal]
    exact Measure.absolutelyContinuous_smul hinv_ne_zero
  exact hraw_ac_normal.ae_le hnormalizedGain

end

end LG21TestOptionalPolicies
