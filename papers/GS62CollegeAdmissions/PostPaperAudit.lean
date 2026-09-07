import GS62CollegeAdmissions.ProofInterface

/-!
# Post-paper audit: Gale--Shapley 1962

Lean-side endpoint ledger for Gale and Shapley's *College Admissions and the
Stability of Marriage*.

Every endpoint below delegates to the proved paper route imported by
`PaperInterface.lean`. This file is an auxiliary compile receipt, not the
paper's review surface; the review surface is `PaperInterface.lean` itself.

The pinned ignored scan is `source.pdf`, SHA-256
`953a8123e8120a86b17ae3de92cb51abb5aed420fe11b97fe2a666a8e637d09b`.
All printed pages 9--15 were inspected directly.  Normal coverage consists of
the two displayed college definitions, the prose marriage-instability
definition, and Theorems 1 and 2.  The wrappers below additionally compile a
few procedure-support endpoints without promoting examples or unnumbered
prose consequences into normal named-theory targets.
-/

namespace GS62CollegeAdmissions
namespace PostPaperAudit

open AppliedModelingLib.Matching
open PaperInterface

/-- Audit endpoint for Theorem 1. -/
theorem theorem1
    {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : strictMarriageDomain val_m val_w) :
    ∃ mu : Assignment M W,
      ¬ unstableMarriage val_m val_w mu ∧ completeMarriage mu :=
  by
    rcases GS62CollegeAdmissions.paper_gs62_theorem1_stable_marriage_exists
      val_m val_w hcard hdomain with ⟨mu, hstable, hcomplete⟩
    refine ⟨mu, ?_, hcomplete⟩
    intro hunstable
    rcases hunstable with ⟨hcomplete', hblocking⟩
    rcases hblocking with ⟨m, w, hcomparisons⟩
    exact hstable.2.2 m w hcomparisons.1 hcomparisons.2

/-- Audit endpoint for the printed batched-stage bound. -/
theorem exact_marriage_stage_bound
    {A : Type*} [Fintype A] [DecidableEq A]
    (val_m : A → A → ℝ) (val_w : A → A → ℝ)
    (hnonempty : 0 < Fintype.card A)
    (hdomain : strictMarriageDomain val_m val_w) :
    ¬ ∃ m, IsActiveMan val_m
      (gsStateAfterBatches val_m val_w
        (gsBatchedStageBound (Fintype.card A))) m :=
  marriage_batched_stage_bound val_m val_w hnonempty hdomain

/-- Audit endpoint for the source top-`q` waiting-list simulation. -/
theorem college_waiting_list_bridge
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
  college_waiting_list_agrees_with_applicant_da
    quota val_applicant val_college hdomain

/-- Audit endpoint for arbitrary-quota Theorem 2. -/
theorem theorem2
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : strictCollegeAdmissionsDomain val_applicant val_college) :
    applicantOptimalCollegeAssignment quota val_applicant val_college
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        quota val_applicant val_college hdomain.2.1 hdomain.1.1) :=
  ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_applicant_optimal
    quota val_applicant val_college hdomain

/--
Audit endpoint for the inverted unique college-optimal outcome under the
explicit responsive cloned-seat roster convention.
-/
theorem inverted_responsive_college_optimal
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
        val_college nu → nu = mu :=
  inverted_college_proposing_unique_responsive_college_optimal
    quota val_applicant val_college hdomain

/--
On the two-applicant/one-seat boundary market, the exact Section 4 waiting-list
procedure assigns the seat to the college's preferred applicant.  This gives a
runner-level counterexample to treating the earlier literal two-assignee
replacement condition as Theorem 2's comparison class.
-/
theorem raw_literal_boundary_source_procedure_eq_preferred_assignment :
    ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        gs62RawLiteralBoundaryQuota
        gs62RawLiteralBoundaryApplicantValue
        gs62RawLiteralBoundaryCollegeValue
        (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.2.1)
        (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.1.1) =
      gs62RawLiteralBoundaryPreferredAssignment := by
  let mu := ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
    gs62RawLiteralBoundaryQuota
    gs62RawLiteralBoundaryApplicantValue
    gs62RawLiteralBoundaryCollegeValue
    (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.2.1)
    (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.1.1)
  have hstable : ManyToOne.IsStable
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundaryQuota mu := by
    dsimp [mu]
    exact ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_stable
      gs62RawLiteralBoundaryQuota
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      gs62RawLiteralBoundary_strictCollegeAdmissionsDomain
  have hOne : mu.app_match 1 = some 0 := by
    cases hmatch : mu.app_match 1 with
    | some c =>
        fin_cases c
        simpa using hmatch
    | none =>
        have hpreference : ManyToOne.valApplicant
            gs62RawLiteralBoundaryApplicantValue 1 (mu.app_match 1) <
            gs62RawLiteralBoundaryApplicantValue 1 0 := by
          norm_num [ManyToOne.valApplicant, hmatch,
            gs62RawLiteralBoundaryApplicantValue]
        have hnotOne : 1 ∉ mu.college_roster 0 := by
          intro hmem
          have : mu.app_match 1 = some 0 :=
            (mu.consistent 1 0).mpr hmem
          simp [hmatch] at this
        by_cases hzero : 0 ∈ mu.college_roster 0
        · exact (hstable.2.2.2 1 0 hpreference
            (Or.inr ⟨0, hzero, by
              norm_num [gs62RawLiteralBoundaryCollegeValue]⟩)).elim
        · have hempty : mu.college_roster 0 = ∅ := by
            ext a
            fin_cases a <;> simp [hzero, hnotOne]
          exact (hstable.2.2.2 1 0 hpreference
            (Or.inl ⟨by
              norm_num [gs62RawLiteralBoundaryCollegeValue], by
              simp [hempty, gs62RawLiteralBoundaryQuota]⟩)).elim
  have hZero : mu.app_match 0 = none := by
    cases hmatch : mu.app_match 0 with
    | none => rfl
    | some c =>
        fin_cases c
        have hzero : 0 ∈ mu.college_roster 0 :=
          (mu.consistent 0 0).mp (by simpa using hmatch)
        have hone : 1 ∈ mu.college_roster 0 :=
          (mu.consistent 1 0).mp hOne
        have hEq : (0 : Fin 2) = 1 :=
          (Finset.card_le_one.mp (hstable.1 0)) 0 hzero 1 hone
        norm_num at hEq
  apply ManyToOneOptimality.manyToOneAssignment_eq_of_app_match
  intro a
  change mu.app_match a = gs62RawLiteralBoundaryPreferredAssignment.app_match a
  fin_cases a
  · simp [hZero, gs62RawLiteralBoundaryPreferredAssignment]
  · simp [hOne, gs62RawLiteralBoundaryPreferredAssignment]

/--
The actual Section 4 output in the boundary market is not applicant-optimal
under the literal printed comparison class.  Theorem 2 therefore requires the
completed stability convention rather than the raw page-10 predicate alone.
-/
theorem raw_literal_boundary_source_procedure_not_literal_optimal :
    Not (gs62RawLiteralApplicantOptimal
      gs62RawLiteralBoundaryApplicantValue
      gs62RawLiteralBoundaryCollegeValue
      (ExactCollegeBatchedProcedure.sourceWaitingListFinalAssignment
        gs62RawLiteralBoundaryQuota
        gs62RawLiteralBoundaryApplicantValue
        gs62RawLiteralBoundaryCollegeValue
        (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.2.1)
        (gs62RawLiteralBoundary_strictCollegeAdmissionsDomain.1.1))) := by
  rw [raw_literal_boundary_source_procedure_eq_preferred_assignment]
  exact gs62RawLiteralBoundaryPreferredAssignment_not_rawLiteralApplicantOptimal

end PostPaperAudit
end GS62CollegeAdmissions
