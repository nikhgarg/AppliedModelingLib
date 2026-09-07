import AppliedModelingLib.Markets.Matching.DeferredAcceptance
import AppliedModelingLib.Markets.Matching.ManyToOne

/-!
# Paper-Facing Theorems: Gale-Shapley 1962

This file contains the foundational one-to-one marriage endpoints and the
cloned-seat stable-existence construction.  Full source completion, including
the arbitrary-quota Theorem 2 and the checked source-procedure bridges, lives in
the paper's `SourceCompletion`, `BatchedProcedure`,
`ManyToOneOptimality`, and `ExactCollegeBatchedProcedure` modules.
-/

namespace GS62CollegeAdmissions
open AppliedModelingLib.Matching

/-! ## Paper-facing definitions -/

/--
Gale-Shapley strict marriage domain: equal-size one-to-one markets with strict
preferences and every potential pair acceptable.  The paper assumes strict
rankings and no unmatched agents in the marriage story; positivity encodes the
absence of an outside option in the reusable optional-partner API.
-/
def gs_strict_marriage_domain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  MenStrictPreferenceProfile val_m ∧
    WomenStrictPreferenceProfile val_w ∧
    AllPairsAcceptable val_m val_w

/-- Paper-facing stable marriage predicate. -/
def gs_stable_marriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  IsStable val_m val_w mu

/-- Paper-facing complete marriage predicate. -/
def gs_complete_marriage {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    (∀ w, ∃ m, mu.w_match w = some m)

/--
Applicant/proposer optimality among stable matchings: every proposer weakly
prefers this stable matching to any other stable matching.
-/
def gs_applicant_optimal_stable_marriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  gs_stable_marriage val_m val_w mu ∧
    ∀ mu', gs_stable_marriage val_m val_w mu' →
      ∀ m, valM val_m m (mu'.m_match m) ≤ valM val_m m (mu.m_match m)

/-! ## Deferred-acceptance endpoints -/

/-- Deferred acceptance produces a stable matching for any finite preferences. -/
theorem gs_deferredAcceptance_stable
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    gs_stable_marriage val_m val_w (deferredAcceptance val_m val_w) :=
  da_produces_stable_matching val_m val_w

/--
On Gale-Shapley's strict equal-size marriage domain, deferred acceptance
matches every participant.
-/
theorem gs_deferredAcceptance_complete_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    gs_complete_marriage (deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨_hstrictM, _hstrictW, hacceptable⟩
  exact deferredAcceptance_complete_of_card_eq_all_pairs_acceptable
    val_m val_w hcard hacceptable

/--
On the strict marriage domain, the proposing-side deferred-acceptance outcome is
proposer-optimal among stable matchings.
-/
theorem gs_deferredAcceptance_applicant_optimal_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    gs_applicant_optimal_stable_marriage val_m val_w
      (deferredAcceptance val_m val_w) := by
  rcases hdomain with ⟨hstrictM, hstrictW, hacceptable⟩
  refine ⟨gs_deferredAcceptance_stable val_m val_w, ?_⟩
  intro mu hstable m
  exact da_is_men_optimal_of_strict_preferences
    val_m val_w hstrictM hstrictW hacceptable mu hstable m

/-! ## Source-numbered wrappers -/

/--
Gale-Shapley Theorem 1, marriage form: there always exists a stable set of
marriages.  The Lean statement uses the explicit strict, complete, equal-size
source domain.
-/
theorem paper_gs62_theorem1_stable_marriage_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : gs_strict_marriage_domain val_m val_w) :
    ∃ mu : Assignment M W,
      gs_stable_marriage val_m val_w mu ∧ gs_complete_marriage mu := by
  exact ⟨deferredAcceptance val_m val_w,
    gs_deferredAcceptance_stable val_m val_w,
    gs_deferredAcceptance_complete_on_strict_marriage_domain
      val_m val_w hcard hdomain⟩

/--
Gale-Shapley quota-one college-admissions existence wrapper.  Applicants are the
proposing side and colleges are the accepting side; quota one reduces the college
admissions story to the marriage model.
-/
theorem paper_gs62_college_admissions_quota_one_stable_assignment_exists
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcard : Fintype.card Applicants = Fintype.card Colleges)
    (hdomain : gs_strict_marriage_domain val_applicant val_college) :
    ∃ mu : Assignment Applicants Colleges,
      gs_stable_marriage val_applicant val_college mu ∧
        gs_complete_marriage mu :=
  paper_gs62_theorem1_stable_marriage_exists
    val_applicant val_college hcard hdomain

/--
Quota-one college-admissions stability in the reusable many-to-one API.  This is
the first formal bridge toward general college quotas and hospitals/residents:
ordinary one-to-one deferred acceptance embeds as a stable quota-one
many-to-one assignment.
-/
theorem paper_gs62_college_admissions_quota_one_manyToOne_stable_assignment_exists
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    ∃ mu : ManyToOneAssignment Applicants Colleges,
      ManyToOne.IsStable val_applicant val_college
        (fun _ : Colleges => 1) mu := by
  exact ⟨ManyToOneAssignment.ofOneToOne
      (deferredAcceptance val_applicant val_college),
    ManyToOne.isStable_of_oneToOne_stable_quota_one
      val_applicant val_college
      (deferredAcceptance val_applicant val_college)
      (da_produces_stable_matching val_applicant val_college)⟩

/--
Gale-Shapley college-admissions existence theorem with arbitrary finite quotas.
Colleges with quota `q c` are represented by `q c` cloned seats, deferred
acceptance is run in the induced one-to-one market, and the resulting seat
assignment is collapsed back to college rosters.
-/
theorem paper_gs62_college_admissions_stable_assignment_exists
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) :
    ∃ mu : ManyToOneAssignment Applicants Colleges,
      ManyToOne.IsStable val_applicant val_college quota mu := by
  exact ⟨ManyToOne.deferredAcceptanceManyToOne quota val_applicant val_college,
    ManyToOne.deferredAcceptanceManyToOne_stable quota val_applicant val_college⟩

/--
Quota-one specialization of Gale-Shapley Theorem 2, retained as a useful
marriage corollary.  The arbitrary-quota source theorem is proved in
`ManyToOneOptimality.lean`.
-/
theorem paper_gs62_theorem2_deferred_acceptance_applicant_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hcard : Fintype.card Applicants = Fintype.card Colleges)
    (hdomain : gs_strict_marriage_domain val_applicant val_college) :
    ∃ mu : Assignment Applicants Colleges,
      gs_complete_marriage mu ∧
        gs_applicant_optimal_stable_marriage val_applicant val_college mu := by
  exact ⟨deferredAcceptance val_applicant val_college,
    gs_deferredAcceptance_complete_on_strict_marriage_domain
      val_applicant val_college hcard hdomain,
    gs_deferredAcceptance_applicant_optimal_on_strict_marriage_domain
      val_applicant val_college hdomain⟩

end GS62CollegeAdmissions
