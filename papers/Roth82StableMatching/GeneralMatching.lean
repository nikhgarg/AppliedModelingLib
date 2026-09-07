import Roth82StableMatching.SourceProcedures
import GS62CollegeAdmissions.PaperInterface
import Mathlib.Data.Fintype.Sum

/-!
# Roth's quota and dummy-agent extension

Roth uses the marriage model as a representation of the strict general
matching problem.  This file makes the two representation steps explicit:

* arbitrary institution quotas use the responsive many-to-one model and the
  source top-`q` waiting-list runner; and
* an optional-partner assignment is completed to a balanced marriage by adding
  one personal dummy on the opposite side for every real agent.

The many-to-one specialization is the individual/institution case singled out
by the source immediately after the general-model discussion.
-/

namespace Roth82StableMatching

open AppliedModelingLib.Matching

/-! ## Dummy completion of optional assignments -/

/--
Complete a partial one-to-one assignment by pairing each unmatched real agent
with a personal dummy.  If `m` and `w` are matched, their two unused personal
dummies are paired with one another.
-/
def paper_dummy_completion_equiv {M W : Type*} (mu : Assignment M W) :
    (M ⊕ W) ≃ (W ⊕ M) where
  toFun
    | Sum.inl m =>
        match mu.m_match m with
        | some w => Sum.inl w
        | none => Sum.inr m
    | Sum.inr w =>
        match mu.w_match w with
        | some m => Sum.inr m
        | none => Sum.inl w
  invFun
    | Sum.inl w =>
        match mu.w_match w with
        | some m => Sum.inl m
        | none => Sum.inr w
    | Sum.inr m =>
        match mu.m_match m with
        | some w => Sum.inr w
        | none => Sum.inl m
  left_inv x := by
    cases x with
    | inl m =>
        cases hm : mu.m_match m with
        | none => simp [hm]
        | some w =>
            have hw : mu.w_match w = some m := (mu.consistent_m m w).1 hm
            simp [hm, hw]
    | inr w =>
        cases hw : mu.w_match w with
        | none => simp [hw]
        | some m =>
            have hm : mu.m_match m = some w := (mu.consistent_m m w).2 hw
            simp [hm, hw]
  right_inv y := by
    cases y with
    | inl w =>
        cases hw : mu.w_match w with
        | none => simp [hw]
        | some m =>
            have hm : mu.m_match m = some w := (mu.consistent_m m w).2 hw
            simp [hm, hw]
    | inr m =>
        cases hm : mu.m_match m with
        | none => simp [hm]
        | some w =>
            have hw : mu.w_match w = some m := (mu.consistent_m m w).1 hm
            simp [hm, hw]

/-- The complete marriage assignment induced by the dummy completion. -/
def paper_dummy_completion {M W : Type*} (mu : Assignment M W) :
    Assignment (M ⊕ W) (W ⊕ M) :=
  let e := paper_dummy_completion_equiv mu
  { m_match := fun x => some (e x)
    w_match := fun y => some (e.symm y)
    consistent_m := by
      intro x y
      simp only [Option.some.injEq]
      simpa [eq_comm] using e.apply_eq_iff_eq_symm_apply }

/-- Real pairs are preserved exactly by dummy completion. -/
theorem paper_dummy_completion_real_pair_iff {M W : Type*}
    (mu : Assignment M W) (m : M) (w : W) :
    (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inl w) ↔
      mu.m_match m = some w := by
  cases hm : mu.m_match m <;>
    simp [paper_dummy_completion, paper_dummy_completion_equiv, hm]

/-- A real man is assigned his personal dummy exactly when he is unmatched. -/
theorem paper_dummy_completion_man_dummy_iff {M W : Type*}
    (mu : Assignment M W) (m : M) :
    (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inr m) ↔
      mu.m_match m = none := by
  cases hm : mu.m_match m <;>
    simp [paper_dummy_completion, paper_dummy_completion_equiv, hm]

/-- A real woman is assigned her personal dummy exactly when she is unmatched. -/
theorem paper_dummy_completion_woman_dummy_iff {M W : Type*}
    (mu : Assignment M W) (w : W) :
    (paper_dummy_completion mu).w_match (Sum.inl w) = some (Sum.inr w) ↔
      mu.w_match w = none := by
  cases hw : mu.w_match w <;>
    simp [paper_dummy_completion, paper_dummy_completion_equiv, hw]

/-- Every real or dummy agent is matched in the completed marriage. -/
theorem paper_dummy_completion_complete {M W : Type*}
    (mu : Assignment M W) :
    (∀ x, ∃ y, (paper_dummy_completion mu).m_match x = some y) ∧
      ∀ y, ∃ x, (paper_dummy_completion mu).w_match y = some x := by
  constructor
  · intro x
    exact ⟨paper_dummy_completion_equiv mu x, rfl⟩
  · intro y
    exact ⟨(paper_dummy_completion_equiv mu).symm y, rfl⟩

/-- The two dummy-completed sides have equal finite cardinality. -/
theorem paper_dummy_completion_balanced {M W : Type*}
    [Fintype M] [Fintype W] :
    Fintype.card (M ⊕ W) = Fintype.card (W ⊕ M) := by
  simp [add_comm]

/-! ## Responsive arbitrary-quota matching -/

namespace GeneralQuota

open GS62CollegeAdmissions

abbrev QuotaAssignment (Applicants Colleges : Type*) :=
  ManyToOneAssignment Applicants Colleges

/-- Strict responsive individual/institution domain used by Roth's extension. -/
def strictDomain {Applicants Colleges : Type*}
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ) : Prop :=
  gs_strict_college_admissions_domain val_applicant val_college

/-- Feasibility means that no institution exceeds its arbitrary quota. -/
def feasible {Applicants Colleges : Type*}
    (quota : Colleges → ℕ) (mu : QuotaAssignment Applicants Colleges) : Prop :=
  gs_feasible_college_assignment quota mu

/-- Responsive quota stability, including individual rationality. -/
def stable {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : QuotaAssignment Applicants Colleges) : Prop :=
  gs_stable_college_assignment quota val_applicant val_college mu

/-- Applicant-side optimality among every stable quota assignment. -/
def applicantOptimal {Applicants Colleges : Type*}
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (mu : QuotaAssignment Applicants Colleges) : Prop :=
  gs_applicant_optimal_college_assignment quota val_applicant val_college mu

/-- The source top-`q` waiting-list outcome. -/
noncomputable def batchedApplicantOutcome
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictDomain val_applicant val_college) :
    QuotaAssignment Applicants Colleges :=
  ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
    quota val_applicant val_college hdomain.2.1 hdomain.1.1

/--
The quota footnote's batched waiting-list runner is a checked refinement of
the cloned-seat deferred-acceptance procedure.
-/
theorem batchedApplicantOutcome_refines_applicant_da
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictDomain val_applicant val_college) :
    batchedApplicantOutcome quota val_applicant val_college hdomain =
      ManyToOneOptimality.refinedDeferredAcceptanceManyToOne
        quota val_applicant val_college hdomain.1.2 :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_eq_applicant_da
    quota val_applicant val_college hdomain

/--
Roth's general-quota extension of Theorems 1 and 2 in the responsive
individual/institution model: the batched outcome is stable and applicant
optimal, and the role-inverted procedure yields the unique responsive
institution-optimal stable assignment.
-/
theorem stable_and_both_side_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictDomain val_applicant val_college) :
    stable quota val_applicant val_college
        (batchedApplicantOutcome quota val_applicant val_college hdomain) ∧
      applicantOptimal quota val_applicant val_college
        (batchedApplicantOutcome quota val_applicant val_college hdomain) ∧
      ∃! mu : QuotaAssignment Applicants Colleges,
        ManyToOneOptimality.gs_college_optimal_college_assignment
            quota val_applicant val_college hdomain.1.2 mu ∧
          ManyToOneOptimality.gs_responsive_college_optimal_assignment
            quota val_applicant val_college mu := by
  refine ⟨?_, ?_, ?_⟩
  · exact GS62CollegeAdmissions.PaperInterface.college_waiting_list_procedure_stable
      quota val_applicant val_college hdomain
  · exact
      ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_applicant_optimal
      quota val_applicant val_college hdomain
  · exact
      ManyToOneOptimality.paper_gs62_inverted_college_proposing_unique_college_optimal
        quota val_applicant val_college hdomain

end GeneralQuota

end Roth82StableMatching
