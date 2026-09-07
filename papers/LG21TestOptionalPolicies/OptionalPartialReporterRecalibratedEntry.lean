import LG21TestOptionalPolicies.OptionalSourceLocalRecalibratedEntry

/-!
# Recalibrated entry from a partial optional reporter profile

This module extends the approved positive-mass candidate semantics to a
profile that already has some reporters.  A candidate need only certify the
members moved to its positive report branch; it is not asserted to be a
replacement equilibrium for every predecessor action.  Both of the
candidate's action branches retain their own literal selected-law PBOs.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- A literal positive-mass entry that changes a positive set of current
nonreporters into reporters and recalibrates both candidate branches.  The
candidate may replace the predecessor's other report decisions; only its own
positive report branch is subjected to the approved member-response test. -/
def LG21OptionalSourcePositiveMassRecalibratedReportEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (candidateTake : ℝ -> Base -> Bool) (candidateReport : Base -> ℝ -> Bool)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ) : Prop :=
  Measurable (fun omega => candidateTake (skill omega) (base omega)) ∧
    Measurable (fun omega => candidateReport (base omega) (score omega)) ∧
    (fun omega => candidateTake (skill omega) (base omega)) =ᵐ[sourceLaw]
      (fun omega => currentTake (skill omega) (base omega)) ∧
    0 < sourceLaw
      (lg21OptionalSourceChangedToReportForActionEvent base score skill
        currentTake currentReport candidateTake candidateReport) ∧
    ∃ hreportPositive :
        0 < sourceLaw
          (lg21OptionalSourceReportEvent base score skill candidateTake candidateReport),
      ∃ hnoReportPositive :
          0 < sourceLaw
            (lg21OptionalSourceNoReportEvent base score skill
              candidateTake candidateReport),
        LG21OptionalSequentialCandidateReportPBOForAction
          sourceLaw base score skill hpublic candidateTake candidateReport candidate
            hreportPositive ∧
          LG21OptionalSequentialCandidateNoReportPBOForAction
            sourceLaw base score skill hpublic candidateTake candidateReport candidate
              hnoReportPositive ∧
          PositiveMassBranchMembersBestRespond sourceLaw
            (lg21OptionalSourceReportEvent base score skill
              candidateTake candidateReport)
            candidate
            (fun P omega =>
              P.noReportValue (base omega) ≤
                P.reportedValue (base omega) (score omega))

/-- Stability against every literal positive-mass, recalibrated report entry.
This is the candidate-PBO reading of a known decision function: the candidate
is evaluated under its own selected action laws rather than under a
predecessor or null-history PBO. -/
def LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool) : Prop :=
  ∀ candidateTake candidateReport candidate,
    ¬ LG21OptionalSourcePositiveMassRecalibratedReportEntry
      sourceLaw base score skill hpublic currentTake currentReport
        candidateTake candidateReport candidate

/-- Report-branch recalibration stability restricted to candidates that keep
the source equilibrium's fixed test law. -/
def LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntryForTestLaw
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hpublic : Measurable (fun omega => (base omega, (score omega, skill omega))))
    (fixedTestLaw : ℝ -> Base -> Measure ℝ)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool) : Prop :=
  ∀ candidateTake candidateReport candidate,
    (∀ latentSkill publicBase,
      candidate.testLaw latentSkill publicBase =
        fixedTestLaw latentSkill publicBase) ->
    ¬ LG21OptionalSourcePositiveMassRecalibratedReportEntry
      sourceLaw base score skill hpublic currentTake currentReport
        candidateTake candidateReport candidate

/-- Every positive-mass set of real scores contains a positive-mass lower
bounded tail.  This is a countable-cover fact and does not assume a cutoff
representation for the predecessor decision rule. -/
theorem lg21_exists_highScoreTail_of_positive_mass
    {Omega : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega) (score : Omega -> ℝ) (event : Set Omega)
    (hpositive : 0 < sourceLaw event) :
    ∃ anchor : ℝ, 0 < sourceLaw (event ∩ {omega | anchor ≤ score omega}) := by
  let tails : ℕ -> Set Omega := fun n =>
    event ∩ {omega | -(n : ℝ) ≤ score omega}
  have hcover : event ⊆ ⋃ n, tails n := by
    intro omega homega
    rcases exists_nat_ge (-score omega) with ⟨n, hn⟩
    apply Set.mem_iUnion.2
    refine ⟨n, ?_⟩
    change omega ∈ event ∧ -(n : ℝ) ≤ score omega
    exact ⟨homega, by linarith⟩
  have hunionPositive : 0 < sourceLaw (⋃ n, tails n) :=
    lt_of_lt_of_le hpositive (measure_mono hcover)
  rcases exists_measure_pos_of_not_measure_iUnion_null
      (μ := sourceLaw) (s := tails) (ne_of_gt hunionPositive) with
    ⟨n, hn⟩
  exact ⟨-(n : ℝ), by simpa [tails] using hn⟩

/-- The explicit full-base Gaussian high-score candidate refutes stability
whenever a positive-mass current no-report set reaches one of its score
tails.  It keeps both candidate action laws positive and derives each PBO
from that candidate's literal selected population. -/
theorem lg21_optional_not_stable_of_positive_noReport_highScoreTail
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (hallTake : ∀ᵐ omega ∂sourceLaw,
      currentTake (skill omega) (base omega) = true)
    (anchor : ℝ)
    (htail : 0 < sourceLaw
      ({omega | currentReport (base omega) (score omega) = false} ∩
        {omega | anchor ≤ score omega})) :
    ¬ LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
        currentTake currentReport := by
  let candidate := lg21OptionalFullBaseRawGaussianHighScoreCandidate
    baseMean hbaseMean baseVariance noiseVariance anchor
  let candidateTake : ℝ -> Base -> Bool := fun _ _ => true
  let candidateReport : Base -> ℝ -> Bool := candidate.reportDecision
  have hcertificate :=
    lg21_optional_fullBaseGaussian_sequentialSourceCertificate_of_factorization
      sourceLaw base score skill hbase hscore hskill baseLaw
      baseMean hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance anchor hsourceFactor
  dsimp only at hcertificate
  rcases hcertificate with
    ⟨hreportPositive, hnoReportPositive, hreportPBO, hnoReportPBO,
      hreportMembers, _hglobalEntry⟩
  have hcandidateTakeMeasurable : Measurable (fun omega =>
      candidateTake (skill omega) (base omega)) := by
    simpa [candidateTake] using (measurable_const : Measurable fun _ : Omega => true)
  have hcandidateReportMeasurable : Measurable (fun omega =>
      candidateReport (base omega) (score omega)) := by
    simpa [candidateReport, candidate] using
      ((lg21OptionalFullBaseRawGaussianHighScoreCandidate_reportDecision_measurable
        baseMean hbaseMean baseVariance noiseVariance anchor).comp
          (hbase.prodMk hscore))
  have htakeAgreement :
      (fun omega => candidateTake (skill omega) (base omega)) =ᵐ[sourceLaw]
        fun omega => currentTake (skill omega) (base omega) := by
    filter_upwards [hallTake] with omega htake
    simp [candidateTake, htake]
  have htailSubset :
      ({omega | currentReport (base omega) (score omega) = false} ∩
        {omega | anchor ≤ score omega}) ⊆
        lg21OptionalSourceChangedToReportForActionEvent base score skill
          currentTake currentReport candidateTake candidateReport := by
    intro omega homega
    rcases homega with ⟨hnoReport, htailScore⟩
    refine ⟨by simp [candidateTake], ?_, Or.inr hnoReport⟩
    change lg21OptionalHighScoreCandidateReports anchor (score omega) = true
    change anchor ≤ score omega at htailScore
    simpa [lg21OptionalHighScoreCandidateReports] using htailScore
  have hchangedPositive : 0 < sourceLaw
      (lg21OptionalSourceChangedToReportForActionEvent base score skill
        currentTake currentReport candidateTake candidateReport) :=
    lt_of_lt_of_le htail (measure_mono htailSubset)
  intro hstable
  apply hstable candidateTake candidateReport candidate
  refine ⟨hcandidateTakeMeasurable, hcandidateReportMeasurable,
    htakeAgreement, hchangedPositive, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [candidateTake, candidateReport, candidate] using hreportPositive
  · simpa [candidateTake, candidateReport, candidate] using hnoReportPositive
  · simpa [candidateTake, candidateReport, candidate] using hreportPBO
  · simpa [candidateTake, candidateReport, candidate] using hnoReportPBO
  · simpa [candidateTake, candidateReport, candidate] using hreportMembers

/-- A positive literal current no-report population is incompatible with the
recalibrated-entry stability semantics.  The candidate is obtained from a
positive high-score subevent, not from a supplied counterfactual payoff. -/
theorem lg21_optional_no_positive_currentNoReport_of_recalibratedEntry_stable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      sourceLaw.map (fun omega => (base omega, (score omega, skill omega))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
    (currentTake : ℝ -> Base -> Bool) (currentReport : Base -> ℝ -> Bool)
    (hallTake : ∀ᵐ omega ∂sourceLaw,
      currentTake (skill omega) (base omega) = true)
    (hstable : LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntry
      sourceLaw base score skill (hbase.prodMk (hscore.prodMk hskill))
        currentTake currentReport) :
    ¬ 0 < sourceLaw {omega | currentReport (base omega) (score omega) = false} := by
  intro hpositive
  rcases lg21_exists_highScoreTail_of_positive_mass sourceLaw score
      {omega | currentReport (base omega) (score omega) = false} hpositive with
    ⟨anchor, htail⟩
  exact (lg21_optional_not_stable_of_positive_noReport_highScoreTail
    sourceLaw base score skill hbase hscore hskill baseLaw
    baseMean hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
    hsourceFactor currentTake currentReport hallTake anchor htail) hstable

end

end LG21TestOptionalPolicies
