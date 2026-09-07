import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeHighScoreCandidate
import LG21TestOptionalPolicies.OptionalSourceLocalRecalibratedEntry

/-!
# Source-local candidate construction for LG21 Theorem 3.1

This module builds the literal source-timed local-entry witness used when a
positive public-base region has no current reporters.  It patches both source
actions outside the selected region and keeps the candidate's PBOs on the
literal raw action branches.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- Replace only the report action of the all-take/high-score candidate while
keeping its Gaussian experiment and literal candidate values.  The
integrability field is proved for the supplied measurable action rather than
silently inherited from the original cutoff action. -/
noncomputable def lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2)) :
    LG21OptionalCandidateBranchData ℝ Base ℝ := by
  let canonical := lg21HiddenAccessAllTakeMeanGapScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance
    noAccessMass accessMass hnoAccessFinite haccessFinite gap
  refine {
    testLaw := canonical.testLaw
    testLaw_isProbability := canonical.testLaw_isProbability
    reportDecision := candidateReport
    reportedValue := canonical.reportedValue
    noReportValue := canonical.noReportValue
    continuationValue_integrable := ?_ }
  intro latentSkill publicBase
  letI : IsProbabilityMeasure (canonical.testLaw latentSkill publicBase) :=
    canonical.testLaw_isProbability latentSkill publicBase
  letI : IsFiniteMeasure (canonical.testLaw latentSkill publicBase) := ⟨by simp⟩
  have hdecision : Measurable (fun score : ℝ =>
      candidateReport publicBase score) := by
    exact hcandidateReport.comp (measurable_const.prodMk measurable_id)
  have hreported : Integrable (canonical.reportedValue publicBase)
      (canonical.testLaw latentSkill publicBase) := by
    simpa [canonical] using
      (lg21_optional_rawGaussianPosteriorMean_integrable_under_test
        baseMean hbaseMean baseVariance noiseVariance publicBase
        noiseVariance.toNNReal latentSkill)
  have hnoReport : Integrable (fun _score : ℝ =>
      canonical.noReportValue publicBase)
      (canonical.testLaw latentSkill publicBase) :=
    integrable_const _
  have hreportSet : MeasurableSet {score : ℝ |
      candidateReport publicBase score = true} :=
    (measurableSet_singleton true).preimage hdecision
  have hnoReportSet : MeasurableSet {score : ℝ |
      candidateReport publicBase score = false} :=
    (measurableSet_singleton false).preimage hdecision
  have hsplit : (fun score : ℝ =>
      if candidateReport publicBase score then
        canonical.reportedValue publicBase score
      else canonical.noReportValue publicBase) =
      {score : ℝ | candidateReport publicBase score = true}.indicator
        (canonical.reportedValue publicBase) +
      {score : ℝ | candidateReport publicBase score = false}.indicator
        (fun _score => canonical.noReportValue publicBase) := by
    funext score
    by_cases hreport : candidateReport publicBase score = true
    · simp [Set.indicator, hreport]
    · simp [Set.indicator, hreport]
  rw [hsplit]
  exact (hreported.indicator hreportSet).add
    (hnoReport.indicator hnoReportSet)

@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction_testLaw
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (latentSkill : ℝ) (publicBase : Base) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
      candidateReport hcandidateReport).testLaw latentSkill publicBase =
      gaussianReal latentSkill noiseVariance.toNNReal := by
  rfl

@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction_reportedValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (publicBase : Base) (score : ℝ) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
      candidateReport hcandidateReport).reportedValue publicBase score =
      lg21OptionalRawGaussianPosteriorMean
        baseMean hbaseMean baseVariance noiseVariance publicBase score := by
  rfl

@[simp] theorem lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction_noReportValue
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) (gap : ℝ)
    [IsMarkovKernel
      (gaussianSignalJointKernel
        baseMean hbaseMean baseVariance noiseVariance)]
    (candidateReport : Base -> ℝ -> Bool)
    (hcandidateReport : Measurable (fun pair : Base × ℝ =>
      candidateReport pair.1 pair.2))
    (publicBase : Base) :
    (lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction
      baseMean hbaseMean baseVariance noiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite gap
      candidateReport hcandidateReport).noReportValue publicBase =
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        noAccessMass accessMass hnoAccessFinite haccessFinite gap).noReportValue
          publicBase := by
  rfl

/-- Every positive public-base region with no current literal reporters has a
source-timed local candidate entry.  The candidate uses the all-take,
positive-gap action inside the region and exactly the current source actions
outside it; both candidate PBOs are evaluated on the resulting literal raw
action branches. -/
noncomputable def lg21HiddenAccess_sourceLocalCandidateEntry_of_zeroReporterBaseRegion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hcurrentReporterZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region ∩
        lg21HiddenAccessActualReportEvent E) = 0) :
    LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess := by
  classical
  have hfactorization :=
    lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance
  let baseLaw := Classical.choose hfactorization
  let hfactorization₁ := Classical.choose_spec hfactorization
  let baseMean := Classical.choose hfactorization₁
  let hfactorization₂ := Classical.choose_spec hfactorization₁
  let baseVariance := Classical.choose hfactorization₂
  let hfactorization₃ := Classical.choose_spec hfactorization₂
  let hbaseMean := Classical.choose hfactorization₃
  let hfactorization₄ := Classical.choose_spec hfactorization₃
  have hbaseLaw : IsProbabilityMeasure baseLaw := hfactorization₄.1
  have hbaseVariance : 0 < baseVariance := hfactorization₄.2.1
  have hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) :=
    hfactorization₄.2.2
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let noiseVariance : ℝ := (M.noiseVariance testFeature : ℝ)
  letI : IsMarkovKernel
      (gaussianSignalJointKernel baseMean hbaseMean baseVariance noiseVariance) := by
    simpa [noiseVariance] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsFiniteMeasure M.accessLaw := ⟨by simp⟩
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := measure_ne_top _ _
  have hnoiseVariance : 0 < noiseVariance := by
    simpa [noiseVariance] using htestNoiseVariance
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let score : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21HiddenAccessStudentScore testFeature student.2
  let skill : Bool × (ℝ × (Feature -> ℝ)) -> ℝ :=
    fun student => lg21ContinuousPopulationSkill student
  let canonicalCandidate := lg21HiddenAccessAllTakeMeanGapScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite (1 : ℝ)
  let candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool :=
    lg21OptionalLocalRegionTake region E.takeDecision
  let candidateReport :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
    lg21OptionalLocalRegionReport region E.reportDecision
      canonicalCandidate.reportDecision
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hscore : Measurable score := by
    simpa [score] using
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
  have hskill : Measurable skill := by
    simpa [skill] using (measurable_fst.comp measurable_snd)
  have hcurrentTakeRaw : Measurable (fun student =>
      E.takeDecision (skill student) (base student)) :=
    E.takeDecision_measurable.comp (hskill.prodMk hbase)
  have hcurrentReportRaw : Measurable (fun student =>
      E.reportDecision (base student) (score student)) :=
    E.reportDecision_measurable.comp (hbase.prodMk hscore)
  have hcanonicalReportMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      canonicalCandidate.reportDecision pair.1 pair.2) := by
    simpa [canonicalCandidate] using
      (lg21HiddenAccessMeanGapReport_measurable testFeature baseMean hbaseMean (1 : ℝ))
  have hcandidateTakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidateTake pair.1 pair.2) := by
    simpa [candidateTake] using
      (lg21OptionalLocalRegionTake_measurable
        (fun pair : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) => pair.2)
        (fun pair : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) => pair.1)
        region hregion E.takeDecision E.takeDecision_measurable measurable_snd)
  have hcandidateReportMeasurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2) := by
    simpa [candidateReport] using
      (lg21OptionalLocalRegionReport_measurable
        (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => pair.1)
        (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ => pair.2)
        region hregion E.reportDecision canonicalCandidate.reportDecision
        E.reportDecision_measurable hcanonicalReportMeasurable measurable_fst)
  let candidate := lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction
    baseMean hbaseMean baseVariance noiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite (1 : ℝ)
    candidateReport hcandidateReportMeasurable
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let canonicalReportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ))
  let canonicalNoReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessAllTake testFeature)
    (lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ))
  let actualReportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    candidateTake candidateReport
  let actualNoReportEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    candidateTake candidateReport
  let changedTesterEvent := lg21HiddenAccessCandidateChangedTesterEvent E candidateTake
  let changedEvent := lg21HiddenAccessCandidateChangedActionEvent E
    candidateTake candidateReport
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalRegion : ∀ᵐ student ∂localLaw, base student ∈ region := by
    simpa [rawLaw, localLaw, base, regionEvent] using
      (lg21NormalizedRestriction_ae_mem rawLaw regionEvent
        hregionEvent (measure_ne_top _ _))
  have htakeLocal :
      (fun student => candidateTake (skill student) (base student)) =ᵐ[localLaw]
        fun _ => true := by
    filter_upwards [hlocalRegion] with student hmem
    simp [candidateTake, lg21OptionalLocalRegionTake, hmem]
  have hreportLocal :
      (fun student => candidateReport (base student) (score student)) =ᵐ[localLaw]
        fun student => canonicalCandidate.reportDecision (base student) (score student) := by
    filter_upwards [hlocalRegion] with student hmem
    simp [candidateReport, lg21OptionalLocalRegionReport, hmem]
  have hactualReportEventAE : actualReportEvent =ᵐ[localLaw]
      canonicalReportEvent := by
    filter_upwards [htakeLocal, hreportLocal] with student htake hreport
    apply propext
    dsimp [actualReportEvent, canonicalReportEvent,
      lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessAllTake]
    change
      (if student.1 = true then
          if candidateTake student.2.1
              (lg21HiddenAccessStudentBase testFeature student.2) = true then
            candidateReport (lg21HiddenAccessStudentBase testFeature student.2)
              (lg21HiddenAccessStudentScore testFeature student.2)
          else false
        else false) = true ↔
      (if student.1 = true then
          lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
            (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)
        else false) = true
    have htake' : candidateTake student.2.1 (base student) = true := by
      simpa [skill] using htake
    have hreport' : candidateReport (base student) (score student) =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          (base student) (score student) := by
      simpa [canonicalCandidate] using hreport
    have htakeRaw : candidateTake student.2.1
        (lg21HiddenAccessStudentBase testFeature student.2) = true := by
      simpa [base] using htake'
    have hreportRaw : candidateReport
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
      simpa [base, score] using hreport'
    by_cases haccess : student.1 = true <;>
      simp [haccess, htakeRaw, hreportRaw]
  have hactualNoReportEventAE : actualNoReportEvent =ᵐ[localLaw]
      canonicalNoReportEvent := by
    filter_upwards [htakeLocal, hreportLocal] with student htake hreport
    apply propext
    dsimp [actualNoReportEvent, canonicalNoReportEvent,
      lg21HiddenAccessRawCandidateNoReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessAllTake]
    change
      (if student.1 = true then
          if candidateTake student.2.1
              (lg21HiddenAccessStudentBase testFeature student.2) = true then
            candidateReport (lg21HiddenAccessStudentBase testFeature student.2)
              (lg21HiddenAccessStudentScore testFeature student.2)
          else false
        else false) = false ↔
      (if student.1 = true then
          lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
            (lg21HiddenAccessStudentBase testFeature student.2)
            (lg21HiddenAccessStudentScore testFeature student.2)
        else false) = false
    have htake' : candidateTake student.2.1 (base student) = true := by
      simpa [skill] using htake
    have hreport' : candidateReport (base student) (score student) =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          (base student) (score student) := by
      simpa [canonicalCandidate] using hreport
    have htakeRaw : candidateTake student.2.1
        (lg21HiddenAccessStudentBase testFeature student.2) = true := by
      simpa [base] using htake'
    have hreportRaw : candidateReport
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          (lg21HiddenAccessStudentBase testFeature student.2)
          (lg21HiddenAccessStudentScore testFeature student.2) := by
      simpa [base, score] using hreport'
    by_cases haccess : student.1 = true <;>
      simp [haccess, htakeRaw, hreportRaw]
  have hcanonicalReportPositive : 0 < localLaw canonicalReportEvent := by
    simpa [localLaw, canonicalReportEvent, canonicalCandidate] using
      (lg21HiddenAccessAllTakeMeanGap_localCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean (1 : ℝ)
        baseVariance noiseVariance hbaseVariance hnoiseVariance hsourceFactor
        region hregion hregionPositive)
  have hcanonicalNoReportPositive : 0 < localLaw canonicalNoReportEvent := by
    have hpositive :=
      lg21HiddenAccess_localCandidateNoReport_positive_of_noAccess
        M testFeature region hregion hregionPositive hnoAccess
        canonicalCandidate.reportDecision hcanonicalReportMeasurable
    have hevent :
        lg21HiddenAccessCandidateNoReportEvent testFeature
          canonicalCandidate.reportDecision = canonicalNoReportEvent := by
      simpa [canonicalCandidate, canonicalNoReportEvent] using
        (lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReportEvent_eq
          testFeature baseMean hbaseMean baseVariance noiseVariance
          (M.accessLaw {false}) (M.accessLaw {true})
          hnoAccessFinite haccessFinite (1 : ℝ))
    rw [hevent] at hpositive
    exact hpositive
  have hactualReportPositive : 0 < localLaw actualReportEvent := by
    rw [measure_congr hactualReportEventAE]
    exact hcanonicalReportPositive
  have hactualNoReportPositive : 0 < localLaw actualNoReportEvent := by
    rw [measure_congr hactualNoReportEventAE]
    exact hcanonicalNoReportPositive
  have hcanonicalReportPBO :=
    lg21HiddenAccessAllTakeMeanGap_localSourceTimedReportPBO
      M haccess testFeature baseLaw baseMean hbaseMean (1 : ℝ)
      baseVariance noiseVariance hbaseVariance hnoiseVariance hsourceFactor
      region hregion hregionPositive hnoAccessFinite haccessFinite
      hcanonicalReportPositive
  have hcanonicalNoReportPBO :=
    lg21HiddenAccessAllTakeMeanGap_localSourceTimedNoReportPBO
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean (1 : ℝ)
      baseVariance noiseVariance hsourceFactor
      region hregion hregionPositive hnoAccessFinite haccessFinite
      hcanonicalNoReportPositive
  have hreportNormalized :
      lg21NormalizedRestriction localLaw actualReportEvent =
        lg21NormalizedRestriction localLaw canonicalReportEvent :=
    lg21_optional_normalizedRestriction_congr_ae localLaw hactualReportEventAE
  have hnoReportNormalized :
      lg21NormalizedRestriction localLaw actualNoReportEvent =
        lg21NormalizedRestriction localLaw canonicalNoReportEvent :=
    lg21_optional_normalizedRestriction_congr_ae localLaw hactualNoReportEventAE
  have hreportNormalized' :
      lg21NormalizedRestriction (lg21HiddenAccessLocalRawLaw M testFeature region)
        (lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake candidateReport) =
      lg21NormalizedRestriction (lg21HiddenAccessLocalRawLaw M testFeature region)
        (lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature)
          (lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ))) := by
    exact hreportNormalized
  have hnoReportNormalized' :
      lg21NormalizedRestriction (lg21HiddenAccessLocalRawLaw M testFeature region)
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake candidateReport) =
      lg21NormalizedRestriction (lg21HiddenAccessLocalRawLaw M testFeature region)
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessAllTake testFeature)
          (lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ))) := by
    exact hnoReportNormalized
  have hcanonicalCandidate : canonicalCandidate =
      lg21HiddenAccessAllTakeMeanGapScoreCandidate
        baseMean hbaseMean baseVariance noiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite (1 : ℝ) := rfl
  have hactualReportPBO : LG21HiddenAccessSourceTimedCandidateReportPBOOn
      M testFeature region hregionPositive candidateTake candidateReport candidate
      hactualReportPositive := by
    have hvalue : candidate.reportedValue = canonicalCandidate.reportedValue := by
      rfl
    simpa only [LG21HiddenAccessSourceTimedCandidateReportPBOOn,
      hvalue, hcanonicalCandidate, hreportNormalized'] using hcanonicalReportPBO
  have hactualNoReportPBO : LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
      M testFeature region hregionPositive candidateTake candidateReport candidate
      hactualNoReportPositive := by
    have hvalue : candidate.noReportValue = canonicalCandidate.noReportValue := by
      rfl
    simpa only [LG21HiddenAccessSourceTimedCandidateNoReportPBOOn,
      hvalue, hcanonicalCandidate, hnoReportNormalized'] using hcanonicalNoReportPBO
  have hcanonicalReportEventEq : canonicalReportEvent =
      {student | student.1 = true ∧
        baseMean (base student) + (1 : ℝ) ≤ score student} := by
    simpa [canonicalReportEvent, base, score] using
      (lg21HiddenAccessAllTakeMeanGap_rawCandidateReportEvent_eq
        testFeature baseMean (1 : ℝ))
  have hcanonicalReportEventMeasurable : MeasurableSet canonicalReportEvent := by
    rw [hcanonicalReportEventEq]
    have haccess : MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
        student.1 = true} :=
      (measurableSet_singleton true).preimage measurable_fst
    exact haccess.inter (measurableSet_le
      ((hbaseMean.comp hbase).add measurable_const) hscore)
  have hcandidateReportInside : ∀ student, base student ∈ region ->
      candidateReport (base student) (score student) =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          (base student) (score student) := by
    intro student hmem
    simp [candidateReport, lg21OptionalLocalRegionReport,
      canonicalCandidate, lg21HiddenAccessMeanGapReport, hmem]
  have hcandidateTakeInside : ∀ student, base student ∈ region ->
      candidateTake (skill student) (base student) = true := by
    intro student hmem
    simp [candidateTake, lg21OptionalLocalRegionTake, hmem]
  have hcanonicalReportInsideActual : ∀ student, base student ∈ region ->
      student ∈ canonicalReportEvent -> student ∈ actualReportEvent := by
    intro student hmem hcanonical
    rw [hcanonicalReportEventEq] at hcanonical
    have htake := hcandidateTakeInside student hmem
    have hreportDecision := hcandidateReportInside student hmem
    have hreport : candidateReport (base student) (score student) = true := by
      rw [hreportDecision]
      simp [lg21HiddenAccessMeanGapReport, hcanonical.2]
    dsimp [actualReportEvent, lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport]
    have htakeRaw : candidateTake student.2.1
        (lg21HiddenAccessStudentBase testFeature student.2) = true := by
      simpa [skill, base, lg21ContinuousPopulationSkill] using htake
    have hreportRaw : candidateReport
        (lg21HiddenAccessStudentBase testFeature student.2)
        (lg21HiddenAccessStudentScore testFeature student.2) = true := by
      simpa [base, score] using hreport
    simp [hcanonical.1, htakeRaw, hreportRaw]
  have hcurrentReportEventEq : lg21HiddenAccessActualReportEvent E =
      {student | student.1 = true ∧
        E.takeDecision (skill student) (base student) = true ∧
        E.reportDecision (base student) (score student) = true} := by
    ext student
    dsimp [lg21HiddenAccessActualReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport]
    by_cases haccess : student.1 = true <;>
      simp [haccess, skill, base, score, lg21ContinuousPopulationSkill]
  have hactualCandidateReportEventEq : actualReportEvent =
      {student | student.1 = true ∧
        candidateTake (skill student) (base student) = true ∧
        candidateReport (base student) (score student) = true} := by
    ext student
    dsimp [actualReportEvent, lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport]
    by_cases haccess : student.1 = true <;>
      simp [haccess, skill, base, score, lg21ContinuousPopulationSkill]
  have hchangedRawPositive : 0 < rawLaw changedEvent := by
    by_contra hnotPositive
    have hchangedZero : rawLaw changedEvent = 0 :=
      le_antisymm (not_lt.mp hnotPositive) (zero_le _)
    have hunionZero : rawLaw
        (changedEvent ∪ (regionEvent ∩ lg21HiddenAccessActualReportEvent E)) = 0 := by
      apply measure_union_null hchangedZero
      simpa [rawLaw, regionEvent] using hcurrentReporterZero
    have hsubset : regionEvent ∩ canonicalReportEvent ⊆
        changedEvent ∪ (regionEvent ∩ lg21HiddenAccessActualReportEvent E) := by
      intro student hstudent
      rcases hstudent with ⟨hregionMem, hcanonical⟩
      change base student ∈ region at hregionMem
      rw [hcanonicalReportEventEq] at hcanonical
      by_cases htake : E.takeDecision (skill student) (base student) = false
      · left
        left
        change student.1 = true ∧
          E.takeDecision (skill student) (base student) = false ∧
          candidateTake (skill student) (base student) = true
        exact ⟨hcanonical.1, htake,
          hcandidateTakeInside student hregionMem⟩
      · have htakeTrue : E.takeDecision (skill student) (base student) = true := by
          cases hdecision : E.takeDecision (skill student) (base student) with
          | false => exact False.elim (htake hdecision)
          | true => rfl
        by_cases hreport : E.reportDecision (base student) (score student) = false
        · left
          right
          refine ⟨?_, ?_⟩
          · exact hcanonicalReportInsideActual student hregionMem (by
              rw [hcanonicalReportEventEq]
              exact hcanonical)
          · intro hactual
            rw [hcurrentReportEventEq] at hactual
            exact Bool.noConfusion (hreport.symm.trans hactual.2.2)
        · right
          refine ⟨?_, ?_⟩
          · change base student ∈ region
            exact hregionMem
          · have hreportTrue : E.reportDecision (base student) (score student) = true := by
              cases hdecision : E.reportDecision (base student) (score student) with
              | false => exact False.elim (hreport hdecision)
              | true => rfl
            rw [hcurrentReportEventEq]
            exact ⟨hcanonical.1, htakeTrue, hreportTrue⟩
    have hcanonicalRawZero : rawLaw (regionEvent ∩ canonicalReportEvent) = 0 :=
      measure_mono_null hsubset hunionZero
    have hcanonicalLocalZero : localLaw canonicalReportEvent = 0 := by
      rw [show localLaw = lg21NormalizedRestriction rawLaw regionEvent by rfl,
        lg21NormalizedRestriction_apply rawLaw hcanonicalReportEventMeasurable]
      have hintersectionZero : rawLaw (canonicalReportEvent ∩ regionEvent) = 0 := by
        simpa [inter_comm] using hcanonicalRawZero
      rw [hintersectionZero]
      simp
    exact (ne_of_gt hcanonicalReportPositive) hcanonicalLocalZero
  have hchangedInside : changedEvent ⊆ regionEvent := by
    intro student hchanged
    by_contra houtside
    change base student ∉ region at houtside
    have htakeOutside : candidateTake (skill student) (base student) =
        E.takeDecision (skill student) (base student) := by
      simp [candidateTake, lg21OptionalLocalRegionTake, houtside]
    have hreportOutside : candidateReport (base student) (score student) =
        E.reportDecision (base student) (score student) := by
      simp [candidateReport, lg21OptionalLocalRegionReport, houtside]
    rcases hchanged with hchanged | hchanged
    · change student.1 = true ∧
        E.takeDecision (skill student) (base student) = false ∧
        candidateTake (skill student) (base student) = true at hchanged
      rw [htakeOutside] at hchanged
      exact Bool.noConfusion (hchanged.2.1.symm.trans hchanged.2.2)
    · rcases hchanged with ⟨hreport, hnotActual⟩
      apply hnotActual
      rw [hcurrentReportEventEq]
      change student ∈ actualReportEvent at hreport
      rw [hactualCandidateReportEventEq] at hreport
      change student.1 = true ∧
        E.takeDecision (skill student) (base student) = true ∧
        E.reportDecision (base student) (score student) = true
      change student.1 = true ∧
        candidateTake (skill student) (base student) = true ∧
        candidateReport (base student) (score student) = true at hreport
      rw [htakeOutside, hreportOutside] at hreport
      exact hreport
  have hchangedIntersectionPositive : 0 < rawLaw (regionEvent ∩ changedEvent) :=
    lt_of_lt_of_le hchangedRawPositive (measure_mono (by
      intro student hchanged
      exact ⟨hchangedInside hchanged, hchanged⟩))
  have hchangedPositive : 0 < localLaw changedEvent := by
    change 0 < lg21NormalizedRestriction rawLaw regionEvent changedEvent
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw regionEvent changedEvent
      hregionEvent hchangedIntersectionPositive
  have hcanonicalReportMembers : PositiveMassBranchMembersBestRespond localLaw
      canonicalReportEvent canonicalCandidate
      (fun P student => P.noReportValue (base student) ≤
        P.reportedValue (base student) (score student)) := by
    rw [PositiveMassBranchMembersBestRespond]
    refine (ae_restrict_iff' hcanonicalReportEventMeasurable).2 ?_
    filter_upwards with student hmember
    rw [hcanonicalReportEventEq] at hmember
    simpa [canonicalCandidate] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_noReport_le_reported_of_threshold_le
        baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess haccess
        hnoAccessFinite haccessFinite (1 : ℝ) (by norm_num)
        (base student) (score student) hmember.2)
  have hactualReportMembers : PositiveMassBranchMembersBestRespond localLaw
      actualReportEvent candidate
      (fun P student => P.noReportValue (base student) ≤
        P.reportedValue (base student) (score student)) := by
    rw [PositiveMassBranchMembersBestRespond] at hcanonicalReportMembers ⊢
    simpa [candidate, canonicalCandidate] using
      (ae_restrict_congr_set hactualReportEventAE).mpr hcanonicalReportMembers
  have hcandidateTakeRaw : Measurable (fun student =>
      candidateTake (skill student) (base student)) :=
    hcandidateTakeMeasurable.comp (hskill.prodMk hbase)
  have hchangedTesterEventMeasurable : MeasurableSet changedTesterEvent := by
    change MeasurableSet {student | student.1 = true ∧
      E.takeDecision (skill student) (base student) = false ∧
      candidateTake (skill student) (base student) = true}
    exact ((measurableSet_singleton true).preimage measurable_fst).inter
      (((measurableSet_singleton false).preimage hcurrentTakeRaw).inter
        ((measurableSet_singleton true).preimage hcandidateTakeRaw))
  have hchangedTesterInside : ∀ student, student ∈ changedTesterEvent ->
      base student ∈ region := by
    intro student hchanged
    apply hchangedInside
    left
    exact hchanged
  have hcandidateExpectedEq : ∀ latentSkill publicBase,
      publicBase ∈ region ->
      lg21OptionalCandidateTestExpectedValue candidate latentSkill publicBase =
        lg21OptionalCandidateTestExpectedValue canonicalCandidate latentSkill publicBase := by
    intro latentSkill publicBase hmem
    unfold lg21OptionalCandidateTestExpectedValue
    apply integral_congr_ae
    filter_upwards with score
    have hreportEq : candidate.reportDecision publicBase score =
        canonicalCandidate.reportDecision publicBase score := by
      change candidateReport publicBase score =
        lg21HiddenAccessMeanGapReport testFeature baseMean (1 : ℝ)
          publicBase score
      simp [candidateReport, lg21OptionalLocalRegionReport,
        canonicalCandidate, lg21HiddenAccessMeanGapReport, hmem]
    have hreportedValue : candidate.reportedValue publicBase score =
        canonicalCandidate.reportedValue publicBase score := by
      rfl
    have hnoReportValue : candidate.noReportValue publicBase =
        canonicalCandidate.noReportValue publicBase := by
      rfl
    unfold lg21OptionalCandidateContinuationValue
    rw [hreportEq, hreportedValue, hnoReportValue]
  have htesterGain : ∀ᵐ student ∂localLaw.restrict changedTesterEvent,
      candidate.noReportValue (base student) <
        lg21OptionalCandidateTestExpectedValue candidate
          (skill student) (base student) := by
    rw [ae_restrict_iff' hchangedTesterEventMeasurable]
    filter_upwards with student hchanged
    have hinside := hchangedTesterInside student hchanged
    rw [hcandidateExpectedEq (skill student) (base student) hinside]
    simpa [candidate, canonicalCandidate] using
      (lg21HiddenAccessAllTakeMeanGapScoreCandidate_pointwise_test_gain
        baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess haccess
        hnoAccessFinite haccessFinite (1 : ℝ) (by norm_num)
        (skill student) (base student))
  have hagreeOutside : ∀ᵐ student ∂rawLaw, base student ∉ region ->
      candidateTake (skill student) (base student) =
        E.takeDecision (skill student) (base student) ∧
      candidateReport (base student) (score student) =
        E.reportDecision (base student) (score student) := by
    filter_upwards with student
    intro houtside
    constructor
    · simp [candidateTake, lg21OptionalLocalRegionTake, houtside]
    · simp [candidateReport, lg21OptionalLocalRegionReport, houtside]
  refine {
    region := region
    region_measurable := hregion
    region_positive := hregionPositive
    candidateTake := candidateTake
    candidateReport := candidateReport
    candidate := candidate
    candidate_test_law := by
      intro latentSkill publicBase
      rw [E.raw_test_law]
      simp [candidate,
        lg21HiddenAccessAllTakeMeanGapScoreCandidateWithReportAction,
        lg21HiddenAccessAllTakeMeanGapScoreCandidate, noiseVariance]
    candidate_report_action := rfl
    candidate_take_measurable := hcandidateTakeMeasurable
    candidate_report_measurable := hcandidateReportMeasurable
    candidate_agrees_outside_region := by
      simpa [rawLaw, base, score, skill] using hagreeOutside
    candidate_changed_action_positive := by
      simpa [localLaw, changedEvent] using hchangedPositive
    candidate_report_positive := by
      simpa [localLaw, actualReportEvent] using hactualReportPositive
    candidate_noReport_positive := by
      simpa [localLaw, actualNoReportEvent] using hactualNoReportPositive
    candidate_report_pbo := hactualReportPBO
    candidate_noReport_pbo := hactualNoReportPBO
    candidate_report_members_best_respond := by
      simpa [localLaw, actualReportEvent, base, score] using hactualReportMembers
    candidate_tester_strict_gain := by
      simpa [localLaw, changedTesterEvent, candidate, base, skill] using htesterGain }

end

end LG21TestOptionalPolicies
