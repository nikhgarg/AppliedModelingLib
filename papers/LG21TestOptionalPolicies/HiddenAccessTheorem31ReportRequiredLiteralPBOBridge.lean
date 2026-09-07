import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralSource
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge
import LG21TestOptionalPolicies.SelectedGaussianSourcePosterior
import LG21TestOptionalPolicies.SelectedGaussianSourceActionFactor

/-!
# Literal selected-PBO bridge for report-required LG21

The theorem in this file starts with the literal public PBO field, restricts
it to the attained report branch, and then disintegrates the actual selected
source law by public base.  It never conditions the school on a latent skill
band.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/--
Under forced reporting, the literal on-path public PBO is the selected
Gaussian posterior mean on almost every attained public-base fibre.  The
selection is the actual measurable taking rule.  The conclusion is scoped to
the selected base law, exactly where the reporter PBO is attained.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.reportedPayoff_eq_selectedGaussianPosteriorMean_ae_by_selectedBase_of_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
        E.source.reportDecision)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean priorVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean priorVariance.toNNReal
    let action : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
      fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
    let actionEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      lg21SourceLatentActionEvent action
    let selectedSkillPatch := selectedNormalizedKernelAtPositiveFibres
      (κ := skillKernel)
      (lg21SourceLatentActionEvent_measurable action
        (E.source.takeDecision_measurable.comp
          (measurable_snd.prodMk measurable_fst)))
    letI : IsMarkovKernel selectedSkillPatch :=
      selectedNormalizedKernelAtPositiveFibres_isMarkov
        (κ := skillKernel)
        (lg21SourceLatentActionEvent_measurable action
          (E.source.takeDecision_measurable.comp
            (measurable_snd.prodMk measurable_fst)))
    let scoreSkillKernel := gaussianSignalJointKernelOfLatentKernel
      selectedSkillPatch noiseVariance
    letI : IsMarkovKernel scoreSkillKernel :=
      gaussianSignalJointKernelOfLatentKernel_isMarkov
        selectedSkillPatch noiseVariance
    ∀ᵐ publicBase ∂normalizedSelectedBase baseLaw skillKernel actionEvent,
      letI : IsMarkovKernel
          (gaussianSignalPosteriorKernel
            (baseMean publicBase) priorVariance noiseVariance) :=
        lg21_gaussianSignalPosteriorKernel_isMarkov
          (baseMean publicBase) priorVariance noiseVariance
      E.source.reportedPayoff publicBase =ᵐ[
        (scoreSkillKernel.map Prod.fst) publicBase]
        fun observedScore => ∫ latentSkill, latentSkill ∂
          selectedNormalizedKernel
            (gaussianSignalPosteriorKernel
              (baseMean publicBase) priorVariance noiseVariance)
            (Set.univ ×ˢ
              {latentSkill |
                E.source.takeDecision latentSkill publicBase = true})
            observedScore := by
  intro skillKernel action actionEvent selectedSkillPatch scoreSkillKernel
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean priorVariance.toNNReal
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using
      (lg21SourceLatentActionEvent_measurable action haction)
  letI : IsMarkovKernel selectedSkillPatch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov
      (κ := skillKernel) hactionEvent
  letI : IsMarkovKernel scoreSkillKernel :=
    gaussianSignalJointKernelOfLatentKernel_isMarkov
      selectedSkillPatch noiseVariance
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let sourceTakeEvent :=
    lg21HiddenAccessTakerEvent testFeature E.source.takeDecision
  let takerLaw := lg21NormalizedRestriction accessLaw sourceTakeEvent
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (base student, score student)
  let observationSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    fun student => (baseScore student, skill student)
  let posteriorKernel : Kernel
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel baseMean hbaseMean priorVariance noiseVariance
  let selectedObservationEvent : Set
      (((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ) :=
    {observationSkill |
      E.source.takeDecision observationSkill.2 observationSkill.1.1 = true}
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have htakePositive : 0 < accessLaw sourceTakeEvent := by
    simpa [accessLaw, sourceTakeEvent] using
      (E.source.accessLaw_takerEvent_positive hreporterPositive)
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw sourceTakeEvent
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hsourceTakeEvent : sourceTakeEvent =
      {student | action (base student) (skill student) = true} := by
    rfl
  have hreportSet :
      lg21HiddenAccessReportSet testFeature E.source.reportDecision = Set.univ := by
    ext publicScore
    simp [lg21HiddenAccessReportSet, E.reportDecision_eq_true]
  have hreporterLaw :
      lg21NormalizedRestriction rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
          E.source.reportDecision) = takerLaw := by
    calc
      lg21NormalizedRestriction rawLaw
          (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
            E.source.reportDecision) =
          lg21NormalizedRestriction takerLaw
            (baseScore ⁻¹'
              lg21HiddenAccessReportSet testFeature E.source.reportDecision) := by
            simpa [rawLaw, accessLaw, sourceTakeEvent, takerLaw, baseScore] using
              (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E.source)
      _ = takerLaw := by simp [hreportSet, lg21NormalizedRestriction]
  have hliteralPBOReporter : ∀ᵐ student ∂
      lg21NormalizedRestriction rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
          E.source.reportDecision),
      E.source.reportedPayoff (base student) (score student) =
        ∫ latentSkill, latentSkill ∂
          condDistrib skill baseScore takerLaw (baseScore student) := by
    simpa [rawLaw, accessLaw, sourceTakeEvent, takerLaw, baseScore, base, score,
      skill] using
      (E.source.reportedPayoff_eq_takerBaseScoreCondMean_ae hreporterPositive)
  have hliteralPBO : ∀ᵐ student ∂takerLaw,
      E.source.reportedPayoff (base student) (score student) =
        ∫ latentSkill, latentSkill ∂
          condDistrib skill baseScore takerLaw (baseScore student) := by
    simpa only [hreporterLaw] using hliteralPBOReporter
  have hselectedKernel :=
    lg21_source_taker_condDistrib_eq_selectedGaussianPosterior_ae_lawOnly
      (sourceLaw := accessLaw) (base := base) (score := score) (skill := skill)
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
      (measurable_fst.comp measurable_snd)
      baseLaw baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance
      (by simpa [accessLaw, base, score, skill] using hsourceFactor)
      action haction (by simpa [sourceTakeEvent, action, base, skill] using htakePositive)
  have hselectedKernel' : ∀ᵐ student ∂takerLaw,
      condDistrib skill baseScore takerLaw (baseScore student) =
        selectedNormalizedKernel posteriorKernel selectedObservationEvent
          (baseScore student) := by
    simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel,
      sourceTakeEvent, takerLaw, baseScore, posteriorKernel,
      selectedObservationEvent, action, base, score, skill] using hselectedKernel
  have hreportedSelected : ∀ᵐ student ∂takerLaw,
      E.source.reportedPayoff (base student) (score student) =
        ∫ latentSkill, latentSkill ∂
          selectedNormalizedKernel posteriorKernel selectedObservationEvent
            (baseScore student) := by
    filter_upwards [hliteralPBO, hselectedKernel'] with student hPBO hkernel
    rw [hPBO, hkernel]
  have hbase : Measurable base :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable score :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have hskill : Measurable skill := measurable_fst.comp measurable_snd
  have hbaseScore : Measurable baseScore := hbase.prodMk hscore
  have hobservationSkill : Measurable observationSkill := hbaseScore.prodMk hskill
  let rawObservation : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
    fun student => (base student, (score student, skill student))
  let association :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ≃ᵐ
        ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ :=
    MeasurableEquiv.prodAssoc.symm
  have hrawObservation : Measurable rawObservation :=
    hbase.prodMk (hscore.prodMk hskill)
  letI : SFinite (normalizedSelectedBase baseLaw skillKernel actionEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have htakerFactor := lg21_source_selectedAction_base_score_factor_lawOnly
    (sourceLaw := accessLaw) (base := base) (score := score) (skill := skill)
    hbase hscore hskill baseLaw baseMean hbaseMean priorVariance noiseVariance
    (by simpa [accessLaw, base, score, skill] using hsourceFactor)
    action haction
  have htakerFactor' : takerLaw.map observationSkill =
      (normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel).map
        association := by
    simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel,
      sourceTakeEvent, takerLaw, observationSkill, association, action, base, score,
      skill] using
      htakerFactor
  have htakerRawFactor : takerLaw.map rawObservation =
      normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel := by
    calc
      takerLaw.map rawObservation =
          (takerLaw.map observationSkill).map association.symm := by
            rw [Measure.map_map association.symm.measurable hobservationSkill]
            rfl
      _ = ((normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel).map
          association).map association.symm := by rw [htakerFactor']
      _ = normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel := by
            rw [Measure.map_map association.symm.measurable association.measurable]
            have hcancel : association.symm ∘ association = id := by
              funext profile
              simp
            rw [hcancel, Measure.map_id]
  have htakerBaseScoreLaw : takerLaw.map baseScore =
      normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ
        (scoreSkillKernel.map Prod.fst) := by
    calc
      takerLaw.map baseScore =
          (takerLaw.map rawObservation).map (Prod.map id Prod.fst) := by
            rw [Measure.map_map (measurable_id.prodMap measurable_fst)
              hrawObservation]
            rfl
      _ = (normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ scoreSkillKernel).map
          (Prod.map id Prod.fst) := by rw [htakerRawFactor]
      _ = normalizedSelectedBase baseLaw skillKernel actionEvent ⊗ₘ
          (scoreSkillKernel.map Prod.fst) := by
            rw [← Measure.compProd_map measurable_fst]
  have hselectedMeanMeasurable : Measurable (fun publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      ∫ latentSkill, latentSkill ∂
        selectedNormalizedKernel posteriorKernel selectedObservationEvent
          publicScore) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hPBOBaseScore : ∀ᵐ publicScore ∂takerLaw.map baseScore,
      E.source.reportedPayoff publicScore.1 publicScore.2 =
        ∫ latentSkill, latentSkill ∂
          selectedNormalizedKernel posteriorKernel selectedObservationEvent
            publicScore := by
    rw [MeasureTheory.ae_map_iff hbaseScore.aemeasurable
      (measurableSet_eq_fun E.source.reportedPayoff_measurable
        hselectedMeanMeasurable)]
    simpa [baseScore] using hreportedSelected
  rw [htakerBaseScoreLaw] at hPBOBaseScore
  have hPBOFibres := Measure.ae_ae_of_ae_compProd hPBOBaseScore
  have hpositiveBase : ∀ᵐ publicBase ∂normalizedSelectedBase
      baseLaw skillKernel actionEvent,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    exact ae_normalizedSelectedBase_positiveFibres hactionEvent
  filter_upwards [hPBOFibres, hpositiveBase] with publicBase hscorePBO
    htakePositiveBase
  have hscoreLaw : (scoreSkillKernel.map Prod.fst) publicBase =
      normalizedSelectedBase
        (gaussianReal (baseMean publicBase)
          (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | action publicBase latentSkill = true}) := by
    simpa [skillKernel, actionEvent, selectedSkillPatch, scoreSkillKernel] using
      (lg21_selectedAction_scoreLaw_eq_selectedGaussianScoreLaw_lawOnly
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance action haction publicBase htakePositiveBase)
  rw [hscoreLaw] at hscorePBO
  rw [hscoreLaw]
  filter_upwards [hscorePBO] with observedScore hPBO
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel
        (baseMean publicBase) priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      (baseMean publicBase) priorVariance noiseVariance
  have hfixedPosterior :
      selectedNormalizedKernel posteriorKernel selectedObservationEvent
        (publicBase, observedScore) =
      selectedNormalizedKernel
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance)
        (Set.univ ×ˢ {latentSkill | action publicBase latentSkill = true})
        observedScore := by
    simpa [posteriorKernel, selectedObservationEvent] using
      (lg21_selectedAction_selectedPosterior_eq_fixedSelectedGaussian_lawOnly
        baseMean hbaseMean priorVariance noiseVariance action haction
        publicBase observedScore)
  rw [hfixedPosterior] at hPBO
  simpa [action] using hPBO

end

end LG21TestOptionalPolicies
