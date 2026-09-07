import LG21TestOptionalPolicies.OptionalAllNoReporterGlobalSource
import LG21TestOptionalPolicies.RecalibratedBranchMemberEntry

/-!
# Literal positive-mass entry at the optional all-no-reporter endpoint

The source-facing object here is a candidate *branch*, not a replacement
whole-population equilibrium.  It keeps both candidate action branches
positive, derives each branch's PBO from its selected literal source law, and
checks the changed report branch's members after that recalibration.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability

/-- The literal report event selected by an optional-reporting candidate. -/
def lg21OptionalCandidateSourceReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score : Omega -> ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Set Omega :=
  {omega | candidate.reportDecision (base omega) (score omega) = true}

/-- The literal no-report event selected by an optional-reporting candidate. -/
def lg21OptionalCandidateSourceNoReportEvent
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega -> Base) (score : Omega -> ℝ)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Set Omega :=
  {omega | candidate.reportDecision (base omega) (score omega) = false}

/-- Candidate report PBO on its own selected, positive-mass action law. -/
def LG21OptionalCandidateReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive :
      0 < sourceLaw (lg21OptionalCandidateSourceReportEvent base score candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalCandidateSourceReportEvent base score candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalCandidateSourceReportEvent base score candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedValue publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Candidate no-report PBO on its own selected, positive-mass action law. -/
def LG21OptionalCandidateNoReportPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (hpositive :
      0 < sourceLaw (lg21OptionalCandidateSourceNoReportEvent base score candidate)) : Prop :=
  let actionLaw :=
    (lg21NormalizedRestriction sourceLaw
      (lg21OptionalCandidateSourceNoReportEvent base score candidate)).map
        (fun omega => (base omega, (score omega, skill omega)))
  letI : IsProbabilityMeasure
      (lg21NormalizedRestriction sourceLaw
        (lg21OptionalCandidateSourceNoReportEvent base score candidate)) :=
    lg21NormalizedRestriction_isProbability sourceLaw _
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map hpublic.aemeasurable
  letI : IsFiniteMeasure actionLaw := by
    exact ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ scoreSkill, scoreSkill.2 ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/--
The exact source-facing certificate needed to refute a null reporter branch.
It retains the two selected PBO obligations separately from the branch-member
Definition-1 response check.  It intentionally says nothing about nonmembers
of the candidate branch.
-/
def LG21OptionalRecalibratedSourceBranchEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Prop :=
  ∃ hreportPositive :
      0 < sourceLaw (lg21OptionalCandidateSourceReportEvent base score candidate),
    ∃ hnoReportPositive :
      0 < sourceLaw (lg21OptionalCandidateSourceNoReportEvent base score candidate),
      LG21OptionalCandidateReportPBO sourceLaw base score skill hpublic candidate
        hreportPositive ∧
        LG21OptionalCandidateNoReportPBO sourceLaw base score skill hpublic candidate
          hnoReportPositive ∧
          PositiveMassBranchMembersBestRespond sourceLaw
            (lg21OptionalCandidateSourceReportEvent base score candidate)
            candidate
            (fun P omega =>
              P.noReportValue (base omega) ≤
                P.reportedValue (base omega) (score omega)) ∧
            LG21OptionalGlobalPositiveMassEntry sourceLaw base skill candidate

/--
The high-score candidate's report action is a weak best response wherever it
is taken.  This is the score-stage member test only; it does not assert a
whole-profile equilibrium.
-/
theorem lg21_optional_fullBaseCandidate_report_action_weakly_bestResponds
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    ∀ publicBase score,
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
          publicBase score = true ->
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).noReportValue
          publicBase ≤
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportedValue
          publicBase score := by
  intro publicBase score hreport
  have hge : anchor ≤ score := by
    simpa [lg21OptionalFullBaseRawGaussianHighScoreCandidate,
      lg21OptionalHighScoreCandidateReports] using hreport
  have hanchor :=
    lg21_optional_fullBaseCandidate_noReport_lt_reported_at_anchor
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor publicBase
  have hstrict := lg21_optional_rawGaussianPosteriorMean_strictMono
    baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance publicBase
  have hmono := hstrict.monotone hge
  change lg21OptionalFullBaseNoReportValue
      baseMean hbaseMean baseVariance noiseVariance anchor publicBase ≤
    lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance noiseVariance publicBase score
  exact le_trans (le_of_lt hanchor) hmono

/-- The high-score candidate passes the report-branch member test a.e. -/
theorem lg21_optional_fullBaseCandidate_report_members_bestRespond
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) (base : Omega -> Base) (score : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score)
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ) :
    PositiveMassBranchMembersBestRespond sourceLaw
      (lg21OptionalCandidateSourceReportEvent base score
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor))
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor)
      (fun P omega =>
        P.noReportValue (base omega) ≤
          P.reportedValue (base omega) (score omega)) := by
  have hevent : MeasurableSet
      (lg21OptionalCandidateSourceReportEvent base score
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor)) := by
    change MeasurableSet
      ((fun omega =>
        (lg21OptionalFullBaseRawGaussianHighScoreCandidate
          baseMean hbaseMean baseVariance noiseVariance anchor).reportDecision
            (base omega) (score omega)) ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage
      ((lg21OptionalFullBaseRawGaussianHighScoreCandidate_reportDecision_measurable
        baseMean hbaseMean baseVariance noiseVariance anchor).comp
          (hbase.prodMk hscore))
  rw [PositiveMassBranchMembersBestRespond, ae_restrict_iff' hevent]
  exact Filter.Eventually.of_forall fun omega hreport =>
    lg21_optional_fullBaseCandidate_report_action_weakly_bestResponds
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor (base omega) (score omega) hreport

/--
The literal full-base Gaussian candidate has both selected PBO identities and
passes the recalibrated report-branch member test.  This is the complete
positive-mass entry certificate for the optional all-no-reporter endpoint;
it is deliberately not a replacement whole-population equilibrium.
-/
theorem lg21_optional_fullBaseGaussian_recalibratedSourceBranchEntry_of_factorization
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (anchor : ℝ)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :
    LG21OptionalRecalibratedSourceBranchEntry sourceLaw base score skill
      (hbase.prodMk (hscore.prodMk hskill))
      (lg21OptionalFullBaseRawGaussianHighScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance anchor) := by
  let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance anchor
  have hreportPositive :
      0 < sourceLaw (lg21OptionalCandidateSourceReportEvent base score candidate) := by
    simpa only [lg21OptionalCandidateSourceReportEvent, candidate] using
      (lg21_optional_fullBaseCandidate_sourceReport_positive_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor hsourceFactor)
  have hnoReportPositive :
      0 < sourceLaw (lg21OptionalCandidateSourceNoReportEvent base score candidate) := by
    simpa only [lg21OptionalCandidateSourceNoReportEvent, candidate] using
      (lg21_optional_fullBaseCandidate_sourceNoReport_positive_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor hsourceFactor)
  refine ⟨hreportPositive, hnoReportPositive, ?_, ?_, ?_, ?_⟩
  · simpa only [LG21OptionalCandidateReportPBO,
      lg21OptionalCandidateSourceReportEvent, candidate] using
      (lg21_optional_fullBaseCandidate_reportedValue_eq_condDistribMean_ae_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor hsourceFactor)
  · simpa only [LG21OptionalCandidateNoReportPBO,
      lg21OptionalCandidateSourceNoReportEvent, candidate] using
      (lg21_optional_fullBaseCandidate_sourceNoReportValue_eq_condDistribMean_ae_of_factorization
        sourceLaw base score skill hbase hscore hskill baseLaw
        baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance anchor hsourceFactor)
  · simpa only [candidate] using
      (lg21_optional_fullBaseCandidate_report_members_bestRespond
        sourceLaw base score hbase hscore baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance anchor)
  · exact lg21_optional_globalEntry_of_fullBaseGaussianCandidate
      sourceLaw base skill baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor

/-- The full literal public observation used by optional-report action branches. -/
def lg21ContinuousPopulationFullPublicObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) :=
  fun student =>
    (lg21ContinuousPopulationBase testFeature student,
      (lg21ContinuousPopulationFeature testFeature student,
        lg21ContinuousPopulationSkill student))

/-- The literal optional-report public observation is measurable. -/
theorem lg21ContinuousPopulationFullPublicObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21ContinuousPopulationFullPublicObservation testFeature) := by
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk
    (hscore.prodMk hskill)

/--
The literal positive-access LG21 population supplies the full recalibrated
candidate branch at a zero-reporter endpoint.  The returned data keeps the
entire non-test base profile in every selected law.
-/
theorem lg21ContinuousGaussianAccessPopulation_optional_allNoReporter_recalibratedSourceBranchEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (anchor : ℝ) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean),
      IsProbabilityMeasure baseLaw ∧ 0 < baseVariance ∧
        LG21OptionalRecalibratedSourceBranchEntry
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          lg21ContinuousPopulationSkill
          (lg21ContinuousPopulationFullPublicObservation_measurable testFeature)
          (lg21OptionalFullBaseRawGaussianHighScoreCandidate
            baseMean hbaseMean baseVariance
              (M.noiseVariance testFeature : ℝ) anchor) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  rcases
      lg21ContinuousGaussianAccessPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean,
    hbaseLaw, hbaseVariance, ?_⟩
  simpa only [lg21ContinuousPopulationFullPublicObservation] using
    (lg21_optional_fullBaseGaussian_recalibratedSourceBranchEntry_of_factorization
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)
      hbaseVariance htestNoiseVariance anchor hsourceFactor)

end

end LG21TestOptionalPolicies
