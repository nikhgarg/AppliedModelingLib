import GS62CollegeAdmissions.BatchedProcedure
import GS62CollegeAdmissions.ExactCollegeBatchedProcedure
import GS62CollegeAdmissions.SourceStability

/-!
# Gale--Shapley 1962 source model and operational support

This module holds reusable source-model vocabulary and proved operational
bridges.  It is deliberately separate from `PaperInterface.lean`: that file
contains only the five expanded `Spec : Prop` declarations that a reviewer
compares against the selected raw paper source.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

open AppliedModelingLib.Matching

/-- The strict, complete marriage domain used by the paper's first theorem. -/
def strictMarriageDomain {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) : Prop :=
  MenStrictPreferenceProfile val_m ∧
    WomenStrictPreferenceProfile val_w ∧
      AllPairsAcceptable val_m val_w

/-- A complete marriage together with a mutually preferred current alternative. -/
def unstableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  ((∀ m, ∃ w, mu.m_match m = some w) ∧
    ∀ w, ∃ m, mu.w_match w = some m) ∧
    ∃ m w,
      valM val_m m (mu.m_match m) < val_m m w ∧
        valW val_w w (mu.w_match w) < val_w w m

/-- The completed operational marriage-stability convention used by the runner. -/
def stableMarriage {M W : Type*}
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (mu : Assignment M W) : Prop :=
  (∀ m, 0 ≤ valM val_m m (mu.m_match m)) ∧
    (∀ w, 0 ≤ valW val_w w (mu.w_match w)) ∧
      ∀ m w, valM val_m m (mu.m_match m) < val_m m w →
        valW val_w w (mu.w_match w) < val_w w m → False

/-- A marriage assigning every participant on both sides. -/
def completeMarriage {M W : Type*} (mu : Assignment M W) : Prop :=
  (∀ m, ∃ w, mu.m_match m = some w) ∧
    ∀ w, ∃ m, mu.w_match w = some m

/-- The finite strict college-admissions preference domain. -/
def strictCollegeAdmissionsDomain {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  gs_strict_college_admissions_domain val_applicant val_college

/-- A quota-feasible college assignment. -/
def feasibleCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_feasible_college_assignment quota mu

/-- The literal, currently-assigned replacement pair displayed on page 10. -/
def replacementPairCollegeInstability {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62ReplacementPair val_applicant val_college mu

/-- The literal page-10 no-replacement stability condition. -/
def literalStableCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62LiteralStableCollegeAssignment val_applicant val_college mu

/-- The completed standard stability convention used by the checked procedure. -/
def stableCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs62StandardStableCollegeAssignment quota val_applicant val_college mu

/-- The literal source's unstable-assignment predicate. -/
def unstableCollegeAssignment {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  replacementPairCollegeInstability val_applicant val_college mu

/-- Literal page-10 applicant optimality in the fixed-quota assignment domain. -/
def literalApplicantOptimalCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  feasibleCollegeAssignment quota mu ∧
    gs62LiteralStableCollegeAssignment val_applicant val_college mu ∧
      ∀ nu, feasibleCollegeAssignment quota nu →
        gs62LiteralStableCollegeAssignment val_applicant val_college nu →
          ∀ a,
            ManyToOne.valApplicant val_applicant a (nu.app_match a) ≤
              ManyToOne.valApplicant val_applicant a (mu.app_match a)

/-- Applicant optimality under the completed standard convention. -/
def applicantOptimalCollegeAssignment {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  gs_applicant_optimal_college_assignment quota val_applicant val_college mu

/-- Responsive college optimality under the completed standard convention. -/
def responsiveCollegeOptimalAssignment {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : ManyToOneAssignment Applicants Colleges) : Prop :=
  ManyToOneOptimality.gs_responsive_college_optimal_assignment
    quota val_applicant val_college mu

/-- The source batched procedure's printed finite-stage termination bound. -/
theorem marriage_batched_stage_bound
    {A : Type*} [Fintype A] [DecidableEq A]
    (val_m : A → A → ℝ) (val_w : A → A → ℝ)
    (hnonempty : 0 < Fintype.card A)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ m, IsActiveMan val_m
      (gsStateAfterBatches val_m val_w
        (gsBatchedStageBound (Fintype.card A))) m := by
  exact paper_gs62_batched_stage_bound
    val_m val_w rfl hnonempty hdomain.2.2

/-- The source waiting-list terminal assignment agrees with applicant-proposing DA. -/
theorem college_waiting_list_agrees_with_applicant_da
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1 hdomain.1.1 =
      ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_eq_applicant_da
    quota val_applicant val_college hdomain

/-- The checked waiting-list output is stable under the explicit completed convention. -/
theorem college_waiting_list_procedure_stable
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    stableCollegeAssignment quota val_applicant val_college
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1 hdomain.1.1) :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_stable
    quota val_applicant val_college hdomain

/-- The role-inverted source procedure is uniquely responsive-college optimal. -/
theorem inverted_college_proposing_unique_responsive_college_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    let mu := ManyToOneOptimality.collegeProposingManyToOne
      quota val_applicant val_college hdomain.1.2
    responsiveCollegeOptimalAssignment quota val_applicant val_college mu ∧
      ∀ nu, responsiveCollegeOptimalAssignment quota val_applicant
        val_college nu → nu = mu := by
  exact
    GS62CollegeAdmissions.ManyToOneOptimality.paper_gs62_inverted_college_proposing_responsive_outcome_unique
      quota val_applicant val_college hdomain

end PaperInterface
end GS62CollegeAdmissions
