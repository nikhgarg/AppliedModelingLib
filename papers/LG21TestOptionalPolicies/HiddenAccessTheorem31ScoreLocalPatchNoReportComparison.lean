import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeNoReportPBOBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31ScoreLocalPatchEntry

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The literal `X = 0` value induced by the score-local patch is no larger
than the incumbent value.  Both values are first identified on their attained
source branches and then transported through the positive no-access component
to the common public-base law. -/
theorem lg21HiddenAccess_scoreLocalPatch_candidateNoReport_le_incumbent_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    ∀ᵐ student ∂(lg21ContinuousGaussianPopulationLaw M).restrict
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessAllTake testFeature)
        (lg21HiddenAccessRawPosteriorScoreLocalPatch E.reportDecision
          E.noReportPayoff baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ))),
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature
        (lg21HiddenAccessRawPosteriorScoreLocalPatch E.reportDecision
          E.noReportPayoff baseMean hbaseMean baseVariance
            (M.noiseVariance testFeature : ℝ))
        (lg21HiddenAccessStudentBase testFeature student.2) ≤
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) := by
  classical
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let rawObservation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let patch := lg21HiddenAccessRawPosteriorScoreLocalPatch
    E.reportDecision E.noReportPayoff baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  let currentSelection :=
    lg21HiddenAccessPublicNoReportSelection testFeature E.reportDecision
  let patchSelection := lg21HiddenAccessPublicNoReportSelection testFeature patch
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := measure_ne_top _ _
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrawObservation : Measurable rawObservation := by
    simpa [rawObservation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ)) :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  have hbaseMap : rawLaw.map base = baseLaw := by
    calc
      rawLaw.map base = (rawLaw.map rawObservation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hrawObservation]
        rfl
      _ = (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)).map Prod.fst := by
        rw [show rawLaw.map rawObservation = baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) by
          simpa [rawLaw, rawObservation] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)).fst = baseLaw
        rw [Measure.fst_compProd]
  have hscoreValueMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      scoreValue pair.1 pair.2) := by
    rw [show (fun pair :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        scoreValue pair.1 pair.2) =
        (fun pair =>
          gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) * pair.2 +
            gaussianSignalPriorWeight baseVariance (M.noiseVariance testFeature : ℝ) *
              baseMean pair.1) by
        funext pair
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          pair.1 pair.2]
    fun_prop
  have hpatchMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => patch pair.1 pair.2) := by
    apply lg21HiddenAccessScoreLocalReportPatch_measurable
    · exact E.reportDecision_measurable
    · exact lg21ScoreLocalPromotion_measurable E.noReportPayoff scoreValue
        E.noReportPayoff_measurable hscoreValueMeasurable
  have hcurrentBaseAC : baseLaw ≪
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) E.reportDecision).map Prod.fst := by
    exact lg21HiddenAccessAllTake_baseLaw_absolutelyContinuous_arbitraryNoReport
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hsourceFactor E.reportDecision
      E.reportDecision_measurable hnoAccessFinite haccessFinite
  have hpatchBaseAC : baseLaw ≪
      (lg21HiddenAccessRawCandidateNoReportBaseSkillLaw M testFeature
        (lg21HiddenAccessAllTake testFeature) patch).map Prod.fst := by
    exact lg21HiddenAccessAllTake_baseLaw_absolutelyContinuous_arbitraryNoReport
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hsourceFactor patch hpatchMeasurable
      hnoAccessFinite haccessFinite
  have hincumbentAttained :=
    E.noReportPayoff_eq_allTakeRawCandidate_condDistribMean_ae
      hnoAccess hactiveNoTakeZero
  have hcurrentValueAttained :=
    lg21HiddenAccessAllTakeLiteralCandidate_noReportValue_eq_publicScoreNormalizedKernelMean_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hsourceFactor E.reportDecision
      E.reportDecision_measurable hnoAccessFinite haccessFinite
  have hpatchValueAttained :=
    lg21HiddenAccessAllTakeLiteralCandidate_noReportValue_eq_publicScoreNormalizedKernelMean_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hsourceFactor patch hpatchMeasurable
      hnoAccessFinite haccessFinite
  have hincumbentBase := hcurrentBaseAC.ae_le hincumbentAttained
  have hcurrentValueBase := hcurrentBaseAC.ae_le hcurrentValueAttained
  have hpatchValueBase := hpatchBaseAC.ae_le hpatchValueAttained
  have hcurrentFormula : ∀ᵐ publicBase ∂baseLaw,
      E.noReportPayoff publicBase =
        ((M.accessLaw {false}).toReal *
            (∫ score, scoreValue publicBase score ∂
              gaussianReal (baseMean publicBase)
                (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal) +
          (M.accessLaw {true}).toReal *
            (∫ score in {score | (publicBase, score) ∈ currentSelection},
              scoreValue publicBase score ∂
                gaussianReal (baseMean publicBase)
                  (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)) /
          ((M.accessLaw {false}).toReal + (M.accessLaw {true}).toReal *
            (gaussianReal (baseMean publicBase)
              (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
              {score | (publicBase, score) ∈ currentSelection}).toReal) := by
    filter_upwards [hincumbentBase, hcurrentValueBase] with publicBase hincumbent hvalue
    rw [hincumbent, hvalue]
    simpa [currentSelection, scoreValue] using
      (lg21HiddenAccessPublicScoreNormalizedKernel_mean_eq_posteriorScoreMixture
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        hbaseVariance hnoiseVariance
        (lg21HiddenAccessPublicNoReportSelection testFeature E.reportDecision)
        (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
          E.reportDecision E.reportDecision_measurable)
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite
        publicBase)
  have hpatchFormula : ∀ᵐ publicBase ∂baseLaw,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature patch publicBase =
        ((M.accessLaw {false}).toReal *
            (∫ score, scoreValue publicBase score ∂
              gaussianReal (baseMean publicBase)
                (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal) +
          (M.accessLaw {true}).toReal *
            (∫ score in {score | (publicBase, score) ∈ patchSelection},
              scoreValue publicBase score ∂
                gaussianReal (baseMean publicBase)
                  (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)) /
          ((M.accessLaw {false}).toReal + (M.accessLaw {true}).toReal *
            (gaussianReal (baseMean publicBase)
              (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
              {score | (publicBase, score) ∈ patchSelection}).toReal) := by
    filter_upwards [hpatchValueBase] with publicBase hvalue
    rw [hvalue]
    simpa [patchSelection, scoreValue] using
      (lg21HiddenAccessPublicScoreNormalizedKernel_mean_eq_posteriorScoreMixture
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        hbaseVariance hnoiseVariance
        (lg21HiddenAccessPublicNoReportSelection testFeature patch)
        (lg21HiddenAccessPublicNoReportSelection_measurable testFeature
          patch hpatchMeasurable)
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite
        publicBase)
  have hbaseComparison : ∀ᵐ publicBase ∂baseLaw,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature patch publicBase ≤
        E.noReportPayoff publicBase := by
    filter_upwards [hcurrentFormula, hpatchFormula] with publicBase hcurrent hpatch
    have hcurrentSet : MeasurableSet {score : ℝ |
        E.reportDecision publicBase score = false} := by
      exact (measurableSet_singleton false).preimage
        (E.reportDecision_measurable.comp (measurable_const.prodMk measurable_id))
    have hscoreAt : Measurable (scoreValue publicBase) := by
      simpa [scoreValue] using hscoreValueMeasurable.comp
        (measurable_const.prodMk measurable_id)
    have hintegrable : Integrable (scoreValue publicBase)
        (gaussianReal (baseMean publicBase)
          (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal) := by
      exact lg21_optional_rawGaussianPosteriorMean_integrable_under_test
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
        publicBase (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
        (baseMean publicBase)
    have hnoAccessReal : 0 < (M.accessLaw {false}).toReal :=
      ENNReal.toReal_pos (ne_of_gt hnoAccess) hnoAccessFinite
    have haccessReal : 0 ≤ (M.accessLaw {true}).toReal := ENNReal.toReal_nonneg
    have hmixture := lg21_scoreLocalPatch_mixtureMean_le_incumbent
      (gaussianReal (baseMean publicBase)
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
      (scoreValue publicBase) hscoreAt hintegrable
      {score : ℝ | E.reportDecision publicBase score = false} hcurrentSet
      (M.accessLaw {false}).toReal (M.accessLaw {true}).toReal
      (E.noReportPayoff publicBase) hnoAccessReal haccessReal (by
        simpa [currentSelection, scoreValue] using hcurrent)
    have hpatchFiber : {score : ℝ | (publicBase, score) ∈ patchSelection} =
        lg21ScoreLocalPatchRetained
          {score : ℝ | E.reportDecision publicBase score = false}
          (scoreValue publicBase) (E.noReportPayoff publicBase) := by
      ext score
      simp [patchSelection, patch, scoreValue,
        lg21HiddenAccessPublicNoReportSelection, mem_setOf_eq,
        lg21HiddenAccessRawPosteriorScoreLocalPatch,
        lg21HiddenAccessScoreLocalReportPatch_eq_false_iff,
        lg21ScoreLocalPatchRetained, mem_inter_iff, mem_setOf_eq]
    rw [hpatch, hpatchFiber]
    exact hmixture
  have hrawComparison : ∀ᵐ student ∂rawLaw,
      lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature patch
        (base student) ≤ E.noReportPayoff (base student) := by
    have hbaseComparisonMap : ∀ᵐ publicBase ∂rawLaw.map base,
        lg21HiddenAccessAllTakeCandidateNoReportValue M hnoAccess testFeature patch
          publicBase ≤ E.noReportPayoff publicBase := by
      rw [hbaseMap]
      exact hbaseComparison
    exact ae_of_ae_map hbase.aemeasurable hbaseComparisonMap
  exact ae_restrict_of_ae (by
    simpa [rawLaw, base, patch] using hrawComparison)

end

end LG21TestOptionalPolicies
