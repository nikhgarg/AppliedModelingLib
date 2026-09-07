import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredAllTakeFibreCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredAllTakePreScoreExclusion

/-!
# Report-required all-taking fibre endpoint

This module closes the only remaining all-taking branch of the literal
report-required source model.  It uses the feasible pre-score take decision:
on a positive base region with no access non-takers, the attained reporter
PBO makes a positive lower latent-skill tail prefer not taking.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

/-- A positive public-base region cannot have zero literal access/no-take
mass.  The contradiction is entirely at the feasible pre-score taking stage:
all latent types taking would contradict the Gaussian lower-tail gain from
not taking. -/
theorem local_activeNoTake_zero_impossible_of_preScoreBestResponse
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (hregionNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩ E.source.activeNoTakeEvent) = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    False := by
  let selectedBaseLaw := lg21NormalizedRestriction baseLaw region
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  have hselectedAC : selectedBaseLaw ≪ baseLaw := by
    unfold selectedBaseLaw lg21NormalizedRestriction
    exact Measure.smul_absolutelyContinuous.trans
      Measure.restrict_le_self.absolutelyContinuous
  have hbestRaw := E.take_best_response_ae_by_base_of_sourceGaussianFactor
    baseLaw baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ)
    hsourceFactor
  have hbest : ∀ᵐ publicBase ∂selectedBaseLaw,
      NoProfitableBinaryChoiceDeviationAE (skillKernel publicBase)
        (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
        (fun latentSkill => ∫ score, E.source.reportedPayoff publicBase score
          ∂E.source.testLaw latentSkill publicBase)
        (fun _ => E.source.noReportPayoff publicBase) := by
    simpa [selectedBaseLaw, skillKernel] using hselectedAC.ae_le hbestRaw
  have hnoReport :=
    E.localNoReportPayoff_eq_baseMean_ae_on_selectedBase_of_activeNoTake_zero
      region hregion hregionPositive hnoAccess hregionNoTakeZero baseLaw baseMean
      hbaseMean priorVariance hpriorVariance hnoiseVariance hsourceFactor
  have htakeValue :=
    E.localTakeExpectedPayoff_eq_rawGaussianAffine_ae_of_activeNoTake_zero
      region hregion hregionPositive hregionNoTakeZero baseLaw baseMean hbaseMean
      priorVariance hpriorVariance hnoiseVariance hsourceFactor
  have hallTake := E.localAllTake_ae_of_activeNoTake_zero
    region hregion hregionPositive hregionNoTakeZero baseLaw baseMean hbaseMean
    priorVariance hsourceFactor
  have hbaseFalse : ∀ᵐ publicBase ∂selectedBaseLaw, False := by
    filter_upwards [hbest, hnoReport, htakeValue, hallTake] with publicBase hbestAt
      hnoReportAt htakeValueAt hallTakeAt
    let scoreWeight := gaussianSignalWeight priorVariance
      (M.noiseVariance testFeature : ℝ)
    let priorWeight := gaussianSignalPriorWeight priorVariance
      (M.noiseVariance testFeature : ℝ)
    have hweight : 0 < scoreWeight := by
      simpa [scoreWeight] using
        (gaussianSignalWeight_pos hpriorVariance hnoiseVariance)
    have hden : priorVariance + (M.noiseVariance testFeature : ℝ) ≠ 0 := by
      linarith
    have hmeanValue : priorWeight * baseMean publicBase +
        scoreWeight * baseMean publicBase = baseMean publicBase := by
      dsimp [priorWeight, scoreWeight, gaussianSignalPriorWeight,
        gaussianSignalWeight]
      field_simp [hden]
      ring
    have hstrictBelow : ∀ latentSkill,
        latentSkill < baseMean publicBase ->
          (∫ score, E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase) <
            E.source.noReportPayoff publicBase := by
      intro latentSkill hbelow
      rw [htakeValueAt latentSkill, hnoReportAt]
      calc
        priorWeight * baseMean publicBase + scoreWeight * latentSkill <
            priorWeight * baseMean publicBase + scoreWeight * baseMean publicBase := by
              nlinarith
        _ = baseMean publicBase := hmeanValue
    have hchosen : ∀ᵐ latentSkill ∂skillKernel publicBase,
        E.source.takeDecision latentSkill publicBase = true ->
          E.source.noReportPayoff publicBase ≤
            ∫ score, E.source.reportedPayoff publicBase score
              ∂E.source.testLaw latentSkill publicBase := hbestAt.1
    have htailExcluded : ∀ᵐ latentSkill ∂skillKernel publicBase,
        latentSkill ∉ Set.Iio (baseMean publicBase) := by
      filter_upwards [hallTakeAt, hchosen] with latentSkill htake hbest
      intro hbelow
      exact (not_le_of_gt (hstrictBelow latentSkill hbelow)) (hbest htake)
    have htailZero : skillKernel publicBase (Set.Iio (baseMean publicBase)) = 0 := by
      simpa using (ae_iff.mp htailExcluded)
    have htailPositive : 0 < skillKernel publicBase
        (Set.Iio (baseMean publicBase)) := by
      rw [show skillKernel publicBase = gaussianReal (baseMean publicBase)
          priorVariance.toNNReal by
        exact gaussianLocationKernel_apply baseMean hbaseMean priorVariance.toNNReal
          publicBase]
      exact lg21_gaussianReal_Iio_pos (baseMean publicBase)
        (baseMean publicBase)
        (ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance))
    exact (ne_of_gt htailPositive) htailZero
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noAccessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessNoAccessEvent
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let localNoAccessLaw := lg21NormalizedRestriction rawLaw
    (noAccessEvent ∩ regionEvent)
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hlocalNoAccessPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive M testFeature region
        hnoAccess hregionPositive)
  letI : IsProbabilityMeasure localNoAccessLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (noAccessEvent ∩ regionEvent)
      (ne_of_gt hlocalNoAccessPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure localNoAccessLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hselectedBaseLaw : localNoAccessLaw.map base = selectedBaseLaw := by
    simpa [rawLaw, noAccessEvent, regionEvent, localNoAccessLaw, base,
      selectedBaseLaw] using
      (E.localNoAccessBaseLaw_eq_selectedBase region hregion hregionPositive
        hnoAccess baseLaw baseMean hbaseMean priorVariance hsourceFactor)
  letI : IsProbabilityMeasure selectedBaseLaw := by
    rw [← hselectedBaseLaw]
    exact Measure.isProbabilityMeasure_map hbase.aemeasurable
  have hselectedZero : selectedBaseLaw Set.univ = 0 := by
    simpa using (ae_iff.mp hbaseFalse)
  have hselectedOne : selectedBaseLaw Set.univ = 1 :=
    IsProbabilityMeasure.measure_univ
  rw [hselectedOne] at hselectedZero
  norm_num at hselectedZero

/-- The literal source factorization and feasible pre-score best response
force positive no-taking mass on almost every Gaussian latent-skill fibre.
This is the semantic complement required by the finite-cutoff closeout. -/
theorem ae_positive_noTakeFibres_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean priorVariance
          (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂baseLaw,
      0 < gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal publicBase
        {latentSkill | E.source.takeDecision latentSkill publicBase = false} := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let rawBase : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let rawSkill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    lg21ContinuousPopulationSkill
  let rawBaseSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    lg21HiddenAccessBaseSkillObservation testFeature
  let skillKernel := gaussianLocationKernel baseMean hbaseMean priorVariance.toNNReal
  let noTakeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    {baseSkill | E.source.takeDecision baseSkill.2 baseSkill.1 = false}
  let zeroRegion : Set (LG21NonTestFeature Feature testFeature -> ℝ) :=
    {publicBase | selectionMass skillKernel noTakeEvent publicBase = 0}
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean priorVariance.toNNReal)
  have hrawBase : Measurable rawBase := by
    simpa [rawBase] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrawSkill : Measurable rawSkill := by
    simpa [rawSkill] using (measurable_fst.comp measurable_snd)
  have hrawBaseSkill : Measurable rawBaseSkill := by
    simpa [rawBaseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have htakeAction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      E.source.takeDecision baseSkill.2 baseSkill.1) := by
    simpa using
      (E.source.takeDecision_measurable.comp (measurable_snd.prodMk measurable_fst))
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    change MeasurableSet
      ((fun baseSkill : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        E.source.takeDecision baseSkill.2 baseSkill.1) ⁻¹' ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage htakeAction
  have hzeroRegion : MeasurableSet zeroRegion := by
    change MeasurableSet {publicBase |
      selectionMass skillKernel noTakeEvent publicBase = 0}
    exact (measurableSet_singleton 0).preimage
      (selectionMass_measurable hnoTakeEvent)
  have hrawBaseSkillFactor : rawLaw.map rawBaseSkill =
      baseLaw ⊗ₘ skillKernel := by
    simpa [rawLaw, rawBaseSkill, skillKernel] using
      (lg21ReportRequiredBaseDependentTail_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
        M testFeature baseLaw baseMean hbaseMean priorVariance
        (M.noiseVariance testFeature : ℝ) hsourceFactor)
  have hrawBaseMarginal : rawLaw.map rawBase = baseLaw := by
    calc
      rawLaw.map rawBase = (rawLaw.map rawBaseSkill).map Prod.fst := by
        rw [Measure.map_map measurable_fst hrawBaseSkill]
        rfl
      _ = (baseLaw ⊗ₘ skillKernel).map Prod.fst := by
        rw [hrawBaseSkillFactor]
      _ = baseLaw := by
        exact Measure.fst_compProd _ _
  have hzeroRegionNull : baseLaw zeroRegion = 0 := by
    by_contra hzeroRegionNotNull
    have hzeroRegionPositive : 0 < baseLaw zeroRegion :=
      pos_iff_ne_zero.mpr hzeroRegionNotNull
    let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature zeroRegion
    have hregionPositive : 0 < rawLaw regionEvent := by
      rw [show regionEvent = rawBase ⁻¹' zeroRegion by rfl,
        ← Measure.map_apply hrawBase hzeroRegion, hrawBaseMarginal]
      exact hzeroRegionPositive
    let target : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
      (zeroRegion ×ˢ Set.univ) ∩ noTakeEvent
    have htarget : MeasurableSet target :=
      (hzeroRegion.prod MeasurableSet.univ).inter hnoTakeEvent
    have htargetZero : (baseLaw ⊗ₘ skillKernel) target = 0 := by
      rw [Measure.compProd_apply htarget]
      apply lintegral_eq_zero_of_ae_eq_zero
      exact Filter.Eventually.of_forall (fun publicBase => by
        change skillKernel publicBase (Prod.mk publicBase ⁻¹' target) = 0
        by_cases hmem : publicBase ∈ zeroRegion
        · have hfibre : Prod.mk publicBase ⁻¹' target =
            selectedFiber noTakeEvent publicBase := by
              ext latentSkill
              simp [target, selectedFiber, hmem]
          rw [hfibre]
          change selectionMass skillKernel noTakeEvent publicBase = 0
          exact hmem
        · have hfibre : Prod.mk publicBase ⁻¹' target = ∅ := by
              ext latentSkill
              simp [target, hmem]
          rw [hfibre]
          simp)
    have hrawNoTakeZero : rawLaw
        (rawBase ⁻¹' zeroRegion ∩
          {student | E.source.takeDecision (rawSkill student)
            (rawBase student) = false}) = 0 := by
      have hpreimage : rawBaseSkill ⁻¹' target =
          rawBase ⁻¹' zeroRegion ∩
            {student | E.source.takeDecision (rawSkill student)
              (rawBase student) = false} := by
        ext student
        simp [rawBaseSkill, rawBase, rawSkill, target, noTakeEvent,
          lg21HiddenAccessBaseSkillObservation,
          lg21ContinuousPopulationSkill]
      rw [← hpreimage, ← Measure.map_apply hrawBaseSkill htarget,
        hrawBaseSkillFactor]
      exact htargetZero
    have hregionNoTakeZero : rawLaw
        (regionEvent ∩ E.source.activeNoTakeEvent) = 0 := by
      apply measure_mono_null _ hrawNoTakeZero
      intro student hmember
      rcases hmember with ⟨hregionMember, hactive⟩
      change rawBase student ∈ zeroRegion at hregionMember
      exact ⟨hregionMember, by
        simpa [rawSkill, rawBase,
          LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
          lg21HiddenAccessStudentTake, lg21ContinuousPopulationSkill] using hactive.2⟩
    exact E.local_activeNoTake_zero_impossible_of_preScoreBestResponse
      zeroRegion hzeroRegion hregionPositive hnoAccess hregionNoTakeZero
      baseLaw baseMean hbaseMean priorVariance hpriorVariance hnoiseVariance
      hsourceFactor
  have hzeroAE : ∀ᵐ publicBase ∂baseLaw, publicBase ∉ zeroRegion := by
    simpa only [ae_iff, not_not] using hzeroRegionNull
  filter_upwards [hzeroAE] with publicBase hnotZero
  have hpositive : 0 < selectionMass skillKernel noTakeEvent publicBase :=
    pos_iff_ne_zero.mpr hnotZero
  simpa [skillKernel, selectionMass, selectedFiber, noTakeEvent] using hpositive

end LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

end

end LG21TestOptionalPolicies
