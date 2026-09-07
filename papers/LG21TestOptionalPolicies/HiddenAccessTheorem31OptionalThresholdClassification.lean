import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalThresholdCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31PopulationMassTransport
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeTransport
import LG21TestOptionalPolicies.OptionalFibrewisePositiveMassUnraveling

/-!
# Literal optional score-threshold classification for LG21 Theorem 3.1

This module derives the post-score cutoff from the source's literal action
laws.  It does not assume a cutoff representation: the two best-response
directions come respectively from the attained reporter PBO and the stable
score-local entry exclusion.  The Gaussian score law removes only the
measure-zero indifference graph.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Under the literal hidden-access source model, stable optional reporting is
almost everywhere the finite raw-Gaussian posterior cutoff rule on the actual
positive-access `(base, score)` population. -/
theorem lg21HiddenAccess_optional_reportDecision_eq_rawPosteriorCutoff_ae_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    ∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      E.reportDecision publicScore.1 publicScore.2 =
        decide (affineCutoff
          (gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1)
          (gaussianSignalWeight baseVariance
            (M.noiseVariance testFeature : ℝ))
          (E.noReportPayoff publicScore.1) ≤ publicScore.2) := by
  classical
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
  let baseScoreSkill := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let scoreValue := lg21OptionalRawGaussianPosteriorMean
    baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
  let reportEvent := lg21HiddenAccessOptionalReportEvent testFeature
    E.takeDecision E.reportDecision
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  letI : IsMarkovKernel scoreKernel := by
    simpa [scoreKernel] using
      (gaussianLocationKernel_isMarkov baseMean hbaseMean
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ))
  have hbaseScore : Measurable baseScore := by
    simpa [baseScore] using
      lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hbaseScoreSkill : Measurable baseScoreSkill := by
    simpa [baseScoreSkill] using
      lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature
  have hscoreValue : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      scoreValue profile.1 profile.2) := by
    rw [show (fun profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        scoreValue profile.1 profile.2) =
        (fun profile =>
          gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) *
              profile.2 +
            gaussianSignalPriorWeight baseVariance
              (M.noiseVariance testFeature : ℝ) * baseMean profile.1) by
        funext profile
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          profile.1 profile.2]
    fun_prop
  have hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature -> ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < rawLaw
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : rawLaw
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess := by
    intro region hregion hpositive hzero
    exact lg21HiddenAccess_sourceLocalCandidateEntry_of_zeroReporterBaseRegion
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E region hregion (by simpa [rawLaw] using hpositive)
      (by simpa [rawLaw] using hzero)
  have hactiveNoTakeZero : rawLaw E.activeNoTakeEvent = 0 := by
    simpa [rawLaw] using
      (lg21HiddenAccess_optional_allTake_and_positiveWithholding_of_literalSourceStability
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E hreportBest hstable).1
  have hreporterPositive : 0 < rawLaw reportEvent := by
    simpa [rawLaw, reportEvent, lg21HiddenAccessActualReportEvent] using
      (E.actualReportEvent_positive_of_stable hnoAccess hstable hentry)
  have haccessFactor :
      accessLaw.map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          rawLaw.map (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
            simpa [accessLaw, rawLaw,
              lg21HiddenAccessBaseScoreSkillObservation] using
              (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                M haccess testFeature).symm
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, joint] using hsourceFactor
  have hreportValueRestricted :=
    E.reportedPayoff_eq_rawGaussianPosterior_ae_on_actualReport
      hactiveNoTakeZero hreporterPositive baseLaw baseMean hbaseMean
      baseVariance hbaseVariance htestNoiseVariance haccessFactor
  have hreportEventMeasurable : MeasurableSet reportEvent := by
    simpa [reportEvent] using
      (lg21HiddenAccessOptionalReportEvent_measurable testFeature
        E.takeDecision E.reportDecision E.takeDecision_measurable
        E.reportDecision_measurable)
  rw [ae_restrict_iff' hreportEventMeasurable] at hreportValueRestricted
  have hreportValueRaw : ∀ᵐ student ∂rawLaw,
      student ∈ reportEvent ->
        E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) =
        scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
    simpa [rawLaw, reportEvent, scoreValue] using hreportValueRestricted
  have haccessAC : accessLaw ≪ rawLaw := by
    change (rawLaw accessEvent)⁻¹ • rawLaw.restrict accessEvent ≪ rawLaw
    exact Measure.smul_absolutelyContinuous.trans
      Measure.absolutelyContinuous_restrict
  have hreportValueAccess := haccessAC.ae_le hreportValueRaw
  have htakeAccess : ∀ᵐ student ∂accessLaw,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true := by
    simpa [accessLaw, rawLaw] using
      E.access_take_ae_of_activeNoTake_measure_zero hactiveNoTakeZero
  have haccessTrue : ∀ᵐ student ∂accessLaw, student.1 = true := by
    change ∀ᵐ student ∂lg21NormalizedRestriction rawLaw accessEvent,
      student.1 = true
    apply lg21NormalizedRestriction_ae_mem rawLaw accessEvent
    · change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
        student.1 = true}
      exact (measurableSet_singleton true).preimage measurable_fst
    · exact measure_ne_top _ _
  have hreportBestAccess : ∀ᵐ student ∂accessLaw,
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true ->
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
    simpa [accessLaw, baseScore, lg21HiddenAccessAccessBaseScoreLaw] using
      (ae_of_ae_map hbaseScore.aemeasurable
        (E.optionalReportBestResponse_ae hreportBest).1)
  have hchosenAccess : ∀ᵐ student ∂accessLaw,
      E.reportDecision (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true ->
        E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := by
    filter_upwards [hreportBestAccess, hreportValueAccess, htakeAccess,
      haccessTrue] with student hbest hvalue htake haccessTrue hreport
    have hreportEvent : student ∈ reportEvent := by
      rcases student with ⟨access, primitive⟩
      change lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        E.reportDecision (access, primitive) = true
      have htake' : lg21HiddenAccessStudentTake testFeature E.takeDecision
          primitive = true := by
        simpa [lg21HiddenAccessStudentTake, lg21ContinuousPopulationSkill] using htake
      have hreport' : lg21HiddenAccessStudentReport testFeature E.reportDecision
          primitive = true := by
        simpa [lg21HiddenAccessStudentReport] using hreport
      cases access <;>
        simp_all [lg21HiddenAccessOptionalObservedAction]
    calc
      E.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) ≤
          E.reportedPayoff (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := hbest hreport
      _ = scoreValue (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2) := hvalue hreportEvent
  have hchosenSet : MeasurableSet {profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
      E.reportDecision profile.1 profile.2 = true ->
        E.noReportPayoff profile.1 ≤ scoreValue profile.1 profile.2} := by
    have hreport : MeasurableSet {profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
        E.reportDecision profile.1 profile.2 = true} :=
      (measurableSet_singleton true).preimage E.reportDecision_measurable
    have hle : MeasurableSet {profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
        E.noReportPayoff profile.1 ≤ scoreValue profile.1 profile.2} :=
      measurableSet_le
        (E.noReportPayoff_measurable.comp measurable_fst) hscoreValue
    have hset : {profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
        E.reportDecision profile.1 profile.2 = true ->
          E.noReportPayoff profile.1 ≤ scoreValue profile.1 profile.2} =
        {profile | ¬ E.reportDecision profile.1 profile.2 = true} ∪
          {profile | E.noReportPayoff profile.1 ≤ scoreValue profile.1 profile.2} := by
      ext profile
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro himp
        by_cases hreport : E.reportDecision profile.1 profile.2 = true
        · exact Or.inr (himp hreport)
        · left
          exact hreport
      · rintro (hnotReport | hle) hreport
        · exact (hnotReport hreport).elim
        · exact hle
    rw [hset]
    exact hreport.compl.union hle
  have hchosenBaseScore : ∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      E.reportDecision publicScore.1 publicScore.2 = true ->
        E.noReportPayoff publicScore.1 ≤ scoreValue publicScore.1 publicScore.2 := by
    change ∀ᵐ publicScore ∂accessLaw.map baseScore,
      E.reportDecision publicScore.1 publicScore.2 = true ->
        E.noReportPayoff publicScore.1 ≤ scoreValue publicScore.1 publicScore.2
    rw [MeasureTheory.ae_map_iff hbaseScore.aemeasurable hchosenSet]
    simpa [baseScore] using hchosenAccess
  let gainReport : (LG21NonTestFeature Feature testFeature -> ℝ) → ℝ → Bool :=
    fun publicBase score => decide
      (E.reportDecision publicBase score = true ∨
        scoreValue publicBase score ≤ E.noReportPayoff publicBase)
  have hgainReportMeasurable : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      gainReport profile.1 profile.2) := by
    apply measurable_to_bool
    have hreport : MeasurableSet {profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
        E.reportDecision profile.1 profile.2 = true} :=
      (measurableSet_singleton true).preimage E.reportDecision_measurable
    have hle : MeasurableSet {profile :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ |
        scoreValue profile.1 profile.2 ≤ E.noReportPayoff profile.1} :=
      measurableSet_le hscoreValue
        (E.noReportPayoff_measurable.comp measurable_fst)
    convert hreport.union hle using 1
    ext profile
    simp [gainReport]
  have hstrictGainZero :=
    lg21HiddenAccess_accessNoReport_rawPosteriorGain_measure_zero_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable
  have hstrictGainEvent :
      lg21HiddenAccessAccessNoReportStrictGainEvent testFeature E.reportDecision
        E.noReportPayoff scoreValue =
      lg21HiddenAccessAccessNoReportEvent testFeature gainReport := by
    ext student
    rcases student with ⟨access, primitive⟩
    simp only [lg21HiddenAccessAccessNoReportStrictGainEvent,
      lg21HiddenAccessAccessNoReportEvent, Set.mem_inter_iff,
      Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨haccess, hnoReport⟩, hgain⟩
      refine ⟨haccess, ?_⟩
      have hnoReport' : E.reportDecision
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = false := by
        simpa [lg21HiddenAccessStudentReport] using hnoReport
      simp [lg21HiddenAccessStudentReport, gainReport, hnoReport',
        not_le.mpr hgain]
    · rintro ⟨haccess, hcombined⟩
      have hnot : ¬ (E.reportDecision
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = true ∨
        scoreValue (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) ≤
          E.noReportPayoff (lg21HiddenAccessStudentBase testFeature primitive)) := by
        simpa [lg21HiddenAccessStudentReport, gainReport] using hcombined
      refine ⟨⟨haccess, ?_⟩, ?_⟩
      · have hreportFalse : E.reportDecision
          (lg21HiddenAccessStudentBase testFeature primitive)
          (lg21HiddenAccessStudentScore testFeature primitive) = false := by
          cases hreport : E.reportDecision
            (lg21HiddenAccessStudentBase testFeature primitive)
            (lg21HiddenAccessStudentScore testFeature primitive) <;>
            simp_all
        simpa [lg21HiddenAccessStudentReport] using hreportFalse
      · exact lt_of_not_ge (fun hle => hnot (Or.inr hle))
  have hgainNoReportZero : rawLaw
      (lg21HiddenAccessAccessNoReportEvent testFeature gainReport) = 0 := by
    rw [← hstrictGainEvent]
    simpa [rawLaw, scoreValue] using hstrictGainZero
  have hgainAllReport : ∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      gainReport publicScore.1 publicScore.2 = true := by
    exact lg21HiddenAccess_allReport_ae_of_accessNoReport_mass_zero
      M haccess testFeature gainReport hgainReportMeasurable
      (by simpa [rawLaw] using hgainNoReportZero)
  have hunchosenBaseScore : ∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      ¬ E.reportDecision publicScore.1 publicScore.2 = true ->
        scoreValue publicScore.1 publicScore.2 ≤ E.noReportPayoff publicScore.1 := by
    filter_upwards [hgainAllReport] with publicScore hgain hnotReport
    simp [gainReport, hnotReport] at hgain
    exact hgain
  have hbest : NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessBaseScoreLaw M testFeature)
      (fun publicScore => E.reportDecision publicScore.1 publicScore.2 = true)
      (fun publicScore => scoreValue publicScore.1 publicScore.2)
      (fun publicScore => E.noReportPayoff publicScore.1) :=
    ⟨hchosenBaseScore, hunchosenBaseScore⟩
  have hscoreMarginal : joint.map Prod.fst = scoreKernel := by
    ext publicBase target htarget
    rw [Kernel.map_apply _ measurable_fst,
      gaussianSignalJointKernel_apply,
      Measure.map_map measurable_fst (by fun_prop)]
    rw [show Prod.fst ∘ (fun pair : ℝ × ℝ =>
        (pair.1 + pair.2, pair.1)) = gaussianSignalScore by rfl]
    rw [show scoreKernel publicBase = gaussianReal (baseMean publicBase)
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal by
      exact gaussianLocationKernel_apply baseMean hbaseMean
        (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal publicBase]
    rw [gaussianSignalPair_score_marginal (baseMean publicBase) baseVariance
      (M.noiseVariance testFeature : ℝ) hbaseVariance htestNoiseVariance]
  have haccessBaseScoreFactor :
      lg21HiddenAccessAccessBaseScoreLaw M testFeature = baseLaw ⊗ₘ scoreKernel := by
    let dropSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ->
          (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun profile => (profile.1, profile.2.1)
    have hdropSkill : Measurable dropSkill := by
      exact measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    calc
      lg21HiddenAccessAccessBaseScoreLaw M testFeature =
          (accessLaw.map baseScoreSkill).map dropSkill := by
            rw [Measure.map_map hdropSkill hbaseScoreSkill]
            rfl
      _ = (rawLaw.map baseScoreSkill).map dropSkill := by
            rw [lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
              M haccess testFeature]
      _ = (baseLaw ⊗ₘ joint).map dropSkill := by
            rw [show rawLaw.map baseScoreSkill = baseLaw ⊗ₘ joint by
              simpa [rawLaw, baseScoreSkill, joint] using hsourceFactor]
      _ = baseLaw ⊗ₘ joint.map Prod.fst := by
            change (baseLaw ⊗ₘ joint).map (Prod.map id Prod.fst) = _
            rw [← Measure.compProd_map measurable_fst]
      _ = baseLaw ⊗ₘ scoreKernel := by rw [hscoreMarginal]
  have hscoreVariance : 0 < baseVariance + (M.noiseVariance testFeature : ℝ) := by
    linarith
  have hscoreVarianceNN :
      (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hscoreVariance)
  have htie : lg21HiddenAccessAccessBaseScoreLaw M testFeature
      {publicScore |
        scoreValue publicScore.1 publicScore.2 = E.noReportPayoff publicScore.1} = 0 := by
    rw [haccessBaseScoreFactor]
    exact lg21_fibrewise_strictMono_graph_null baseLaw scoreKernel
      (fun publicScore => scoreValue publicScore.1 publicScore.2)
      E.noReportPayoff hscoreValue E.noReportPayoff_measurable
      (fun publicBase =>
        lg21_optional_rawGaussianPosteriorMean_strictMono
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          hbaseVariance htestNoiseVariance publicBase)
      (fun publicBase score => by
        rw [show scoreKernel publicBase =
          gaussianReal (baseMean publicBase)
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal by
          exact gaussianLocationKernel_apply baseMean hbaseMean
            (baseVariance + (M.noiseVariance testFeature : ℝ)).toNNReal publicBase]
        exact gaussianReal_singleton_eq_zero (baseMean publicBase)
          hscoreVarianceNN score)
  have hweight : 0 < gaussianSignalWeight baseVariance
      (M.noiseVariance testFeature : ℝ) :=
    gaussianSignalWeight_pos hbaseVariance htestNoiseVariance
  have hthreshold : ∀ publicScore :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ,
      E.noReportPayoff publicScore.1 ≤ scoreValue publicScore.1 publicScore.2 ↔
        affineCutoff
          (gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1)
          (gaussianSignalWeight baseVariance
            (M.noiseVariance testFeature : ℝ))
          (E.noReportPayoff publicScore.1) ≤ publicScore.2 := by
    intro publicScore
    rw [show scoreValue publicScore.1 publicScore.2 =
        gaussianSignalWeight baseVariance (M.noiseVariance testFeature : ℝ) *
            publicScore.2 +
          gaussianSignalPriorWeight baseVariance
            (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1 by
        exact lg21_optional_rawGaussianPosteriorMean_eq_affine
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
          publicScore.1 publicScore.2]
    simpa [add_comm] using
      (threshold_le_affine_iff_cutoff_le
        (intercept := gaussianSignalPriorWeight baseVariance
          (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1)
        (slope := gaussianSignalWeight baseVariance
          (M.noiseVariance testFeature : ℝ))
        (threshold := E.noReportPayoff publicScore.1)
        (x := publicScore.2) hweight)
  exact bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
    (fun publicScore => E.reportDecision publicScore.1 publicScore.2)
    hbest hthreshold htie

end

end LG21TestOptionalPolicies
