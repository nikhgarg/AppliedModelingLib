import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Positive-mass active entry at the optional zero-reporter endpoint

This module supplies the sequential counterpart of the report-required
active-entry certificate.  It does not give a null reporter fibre an invented
payoff.  Instead, it evaluates a candidate positive-mass testing/reporting
profile with that candidate's own report and no-report PBOs.

If a candidate's report PBO is strictly increasing, its planned high-score
reports improve on its candidate no-report PBO, and every latent skill has a
positive chance of reaching that score region, then testing has strictly
positive continuation value for every candidate type.  Consequently the
all-no-action endpoint has a positive-mass active entry witness.  The
candidate need not already be a whole-population equilibrium: the closure
tests the changed positive-mass branch and its members against the PBO induced
by that candidate action profile.  The future source bridge must derive the
candidate PBO identities from the literal population and action events; this
file does not name or assume a cutoff equilibrium.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set

/-! ## Minimal candidate branch data -/

/--
The data needed to evaluate one positive-mass optional-reporting candidate.
It is intentionally not an equilibrium structure: an entry witness tests a
candidate's own action branches and conditional means, and makes no claim
that nonmembers already best respond to that candidate profile.
-/
structure LG21OptionalCandidateBranchData
    (Skill Base Test : Type*) [MeasurableSpace Test] where
  testLaw : Skill → Base → Measure Test
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  reportDecision : Base → Test → Bool
  reportedValue : Base → Test → ℝ
  noReportValue : Base → ℝ
  continuationValue_integrable :
    ∀ skill base,
      Integrable
        (fun test =>
          if reportDecision base test then
            reportedValue base test
          else
            noReportValue base)
        (testLaw skill base)

/-- Candidate continuation value after the test draw. -/
def lg21OptionalCandidateContinuationValue
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (candidate : LG21OptionalCandidateBranchData Skill Base Test)
    (base : Base) (test : Test) : ℝ :=
  if candidate.reportDecision base test then
    candidate.reportedValue base test
  else
    candidate.noReportValue base

/-- Candidate's ex-ante value from testing before the score is drawn. -/
def lg21OptionalCandidateTestExpectedValue
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (candidate : LG21OptionalCandidateBranchData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  ∫ test, lg21OptionalCandidateContinuationValue candidate base test
    ∂candidate.testLaw skill base

/-! ## Semantic active-entry certificates -/

/-- A positive-mass optional-testing entry evaluated under a candidate's
recalibrated public-action PBOs. -/
def LG21OptionalPositiveMassEntry
    {Skill Base Test : Type*} [MeasurableSpace Skill] [MeasurableSpace Test]
    (skillLaw : Measure Skill) (entrant : Set Skill)
    (candidate : LG21OptionalCandidateBranchData Skill Base Test)
    (base : Base) : Prop :=
  0 < skillLaw entrant ∧
    ∀ skill, skill ∈ entrant →
      candidate.noReportValue base <
        lg21OptionalCandidateTestExpectedValue candidate skill base

/-- The all-no-reporter endpoint has an active entry when some candidate
testing/reporting profile gives a positive-mass group a strict take gain. -/
def LG21OptionalAllNoReportHasActiveEntry
    {Skill Base Test : Type*} [MeasurableSpace Skill] [MeasurableSpace Test]
    (skillLaw : Measure Skill)
    (candidate : LG21OptionalCandidateBranchData Skill Base Test)
    (base : Base) : Prop :=
  ∃ entrant, LG21OptionalPositiveMassEntry skillLaw entrant candidate base

/-! ## Candidate report gain implies active entry -/

/--
Under a candidate profile's own planned report actions, every score strictly
above an anchor is reported and strictly valuable.  The candidate only has to
make its actual report actions weakly worthwhile; this is an entry witness,
not a claim that all nonmembers already best respond to the candidate. Positive
upper-tail probability then makes testing strictly valuable ex ante. The proof
uses the candidate continuation value directly and makes no assumption about
the shape or name of `reportDecision`.
-/
theorem lg21_optional_positiveMassEntry_of_candidate_report_gain
    {Skill Base Test : Type*} [MeasurableSpace Skill] [MeasurableSpace Test]
    [Preorder Test]
    (skillLaw : Measure Skill) (entrant : Set Skill)
    (hentrantPositive : 0 < skillLaw entrant)
    (candidate : LG21OptionalCandidateBranchData Skill Base Test)
    (base : Base)
    (hreportedWeakGain : ∀ test,
      candidate.reportDecision base test = true →
        candidate.noReportValue base ≤ candidate.reportedValue base test)
    (hstrict : StrictMono (candidate.reportedValue base))
    (anchor : Test)
    (hanchor : candidate.noReportValue base < candidate.reportedValue base anchor)
    (hreportsAboveAnchor : ∀ test, anchor < test →
      candidate.reportDecision base test = true)
    (hupperTail : ∀ skill,
      0 < candidate.testLaw skill base (Set.Ioi anchor)) :
    LG21OptionalPositiveMassEntry skillLaw entrant candidate base := by
  refine ⟨hentrantPositive, ?_⟩
  intro skill _hentrant
  letI : IsProbabilityMeasure (candidate.testLaw skill base) :=
    candidate.testLaw_isProbability skill base
  let gain : Test → ℝ := fun test =>
    lg21OptionalCandidateContinuationValue candidate base test -
      candidate.noReportValue base
  have hgain_nonneg : ∀ test, 0 ≤ gain test := by
    intro test
    by_cases hreport : candidate.reportDecision base test = true
    · have hle := hreportedWeakGain test hreport
      simpa [gain, lg21OptionalCandidateContinuationValue, hreport]
        using sub_nonneg.mpr hle
    · have hreportFalse : candidate.reportDecision base test = false := by
        cases hdecision : candidate.reportDecision base test
        · rfl
        · exact False.elim (hreport hdecision)
      simp [gain, lg21OptionalCandidateContinuationValue, hreportFalse]
  have hgain_integrable : Integrable gain (candidate.testLaw skill base) := by
    exact (candidate.continuationValue_integrable skill base).sub
      (integrable_const (candidate.noReportValue base))
  have hpositiveGain :
      0 < candidate.testLaw skill base (Function.support gain) := by
    apply lt_of_lt_of_le (hupperTail skill)
    apply measure_mono
    intro test htest
    have hvalue : candidate.noReportValue base <
        candidate.reportedValue base test :=
      lt_trans hanchor (hstrict htest)
    have hreport : candidate.reportDecision base test = true :=
      hreportsAboveAnchor test htest
    change gain test ≠ 0
    simp [gain, lg21OptionalCandidateContinuationValue, hreport,
      sub_ne_zero.mpr (ne_of_gt hvalue)]
  have hintegral_pos : 0 < ∫ test, gain test ∂candidate.testLaw skill base :=
    (integral_pos_iff_support_of_nonneg hgain_nonneg hgain_integrable).2
      hpositiveGain
  have hgain_identity :
      (∫ test, gain test ∂candidate.testLaw skill base) =
        lg21OptionalCandidateTestExpectedValue candidate skill base -
          candidate.noReportValue base := by
    have hcontinuation : Integrable
        (fun test => lg21OptionalCandidateContinuationValue candidate base test)
        (candidate.testLaw skill base) := by
      simpa [lg21OptionalCandidateContinuationValue] using
        candidate.continuationValue_integrable skill base
    calc
      (∫ test, gain test ∂candidate.testLaw skill base) =
          (∫ test, lg21OptionalCandidateContinuationValue candidate base test
            ∂candidate.testLaw skill base) -
            (∫ _test, candidate.noReportValue base
              ∂candidate.testLaw skill base) := by
            exact integral_sub hcontinuation
              (integrable_const (candidate.noReportValue base))
      _ = lg21OptionalCandidateTestExpectedValue candidate skill base -
          candidate.noReportValue base := by
            simp [lg21OptionalCandidateTestExpectedValue]
  rw [hgain_identity] at hintegral_pos
  linarith

/--
For a Gaussian candidate test law, strict candidate report gain at one score
already gives a positive-mass active entry.  The entrant set is arbitrary:
the result applies in particular to a high-skill candidate cohort selected
from the literal source population.
-/
theorem lg21_optional_positiveMassEntry_of_candidate_gaussian_report_gain
    {Base : Type*}
    (skillLaw : Measure ℝ) (entrant : Set ℝ)
    (hentrantPositive : 0 < skillLaw entrant)
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (base : Base) (noiseVariance : NNReal) (hvariance : noiseVariance ≠ 0)
    (htestLaw : ∀ skill,
      candidate.testLaw skill base = gaussianReal skill noiseVariance)
    (hreportedWeakGain : ∀ score,
      candidate.reportDecision base score = true →
        candidate.noReportValue base ≤ candidate.reportedValue base score)
    (hstrict : StrictMono (candidate.reportedValue base))
    (anchor : ℝ)
    (hanchor : candidate.noReportValue base < candidate.reportedValue base anchor)
    (hreportsAboveAnchor : ∀ score, anchor < score →
      candidate.reportDecision base score = true) :
    LG21OptionalPositiveMassEntry skillLaw entrant candidate base := by
  apply lg21_optional_positiveMassEntry_of_candidate_report_gain
    skillLaw entrant hentrantPositive candidate base hreportedWeakGain hstrict anchor hanchor
    hreportsAboveAnchor
  intro skill
  rw [htestLaw skill]
  exact lg21_gaussianReal_Ioi_pos skill anchor hvariance

/--
If the candidate skill law is a probability law, the preceding result supplies
an all-population positive-mass entry witness.  This is the semantic closure
used at an all-no-reporter profile; no null reporter PBO is ever queried.
-/
theorem lg21_optional_allNoReport_has_positiveMass_entry_of_candidate_gaussian_report_gain
    {Base : Type*}
    (skillLaw : Measure ℝ) [IsProbabilityMeasure skillLaw]
    (candidate : LG21OptionalCandidateBranchData ℝ Base ℝ)
    (base : Base) (noiseVariance : NNReal) (hvariance : noiseVariance ≠ 0)
    (htestLaw : ∀ skill,
      candidate.testLaw skill base = gaussianReal skill noiseVariance)
    (hreportedWeakGain : ∀ score,
      candidate.reportDecision base score = true →
        candidate.noReportValue base ≤ candidate.reportedValue base score)
    (hstrict : StrictMono (candidate.reportedValue base))
    (anchor : ℝ)
    (hanchor : candidate.noReportValue base < candidate.reportedValue base anchor)
    (hreportsAboveAnchor : ∀ score, anchor < score →
      candidate.reportDecision base score = true) :
    LG21OptionalAllNoReportHasActiveEntry skillLaw candidate base := by
  refine ⟨Set.univ, ?_⟩
  apply lg21_optional_positiveMassEntry_of_candidate_gaussian_report_gain
    skillLaw Set.univ ?_ candidate base noiseVariance hvariance htestLaw
    hreportedWeakGain hstrict anchor hanchor hreportsAboveAnchor
  simpa using (zero_lt_one : (0 : ENNReal) < 1)

end

end LG21TestOptionalPolicies
