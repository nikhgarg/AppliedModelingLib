import GS62CollegeAdmissions.PaperInterface

/-!
# Proof endpoints: Gale--Shapley 1962

This module holds the compiled endpoint for each source-facing `Spec` in
`PaperInterface.lean`.  It is intentionally separate from the paper review
surface: reviewers compare the raw source excerpts only with the corresponding
expanded `Spec`; these theorems supply proof evidence for those specifications.
-/

namespace GS62CollegeAdmissions
namespace PaperInterface

open AppliedModelingLib.Matching

theorem unstableMarriage_iff_source_definition :
    ∀ {M W : Type*}
      (val_m : M → W → ℝ) (val_w : W → M → ℝ)
      (mu : Assignment M W),
      unstableMarriage val_m val_w mu ↔
        unstableMarriage_iff_source_definitionSpec val_m val_w mu := by
  intro M W val_m val_w mu
  rfl

theorem unstableCollegeAssignment_iff_source_definition :
    ∀ {Applicants Colleges : Type*}
      (val_applicant : Applicants → Colleges → ℝ)
      (val_college : Colleges → Applicants → ℝ)
      (mu : ManyToOneAssignment Applicants Colleges),
      unstableCollegeAssignment val_applicant val_college mu ↔
        unstableCollegeAssignment_iff_source_definitionSpec
          val_applicant val_college mu := by
  intro Applicants Colleges val_applicant val_college mu
  rfl

theorem literalApplicantOptimalCollegeAssignment_iff_source_definition :
    ∀ {Applicants Colleges : Type*}
      (quota : Colleges → ℕ)
      (val_applicant : Applicants → Colleges → ℝ)
      (val_college : Colleges → Applicants → ℝ)
      (mu : ManyToOneAssignment Applicants Colleges),
      literalApplicantOptimalCollegeAssignment quota val_applicant val_college mu ↔
        literalApplicantOptimalCollegeAssignment_iff_source_definitionSpec
          quota val_applicant val_college mu := by
  intro Applicants Colleges quota val_applicant val_college mu
  rfl

theorem theorem1_stable_marriage_exists :
    theorem1_stable_marriage_existsSpec := by
  intro M W _ _ _ _ val_m val_w hcard hmen hwomen hmenacceptable hwomenacceptable
  have hdomain : strictMarriageDomain val_m val_w :=
    ⟨hmen, hwomen, hmenacceptable, hwomenacceptable⟩
  rcases paper_gs62_theorem1_stable_marriage_exists
      val_m val_w hcard hdomain with ⟨mu, hstable, hcomplete⟩
  refine ⟨mu, ?_, hcomplete⟩
  intro hunstable
  rcases hunstable with ⟨hcomplete', hblocking⟩
  rcases hblocking with ⟨m0, w0, hcomparisons⟩
  exact hstable.2.2 m0 w0 hcomparisons.1 hcomparisons.2

theorem section4_waiting_list_terminal_stability :
    section4_waiting_list_terminal_stabilitySpec := by
  intro Applicants Colleges _ _ _ _ quota val_applicant val_college
    happlicant_strict hcollege_strict
  let hdomain : gs_strict_college_admissions_domain val_applicant val_college :=
    ⟨happlicant_strict, hcollege_strict⟩
  constructor
  · exact ExactCollegeBatchedProcedure.sourceWaitingListFinalState_terminated
      quota val_applicant val_college hcollege_strict.1 happlicant_strict.1
  · have hstable :=
      ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_stable
        quota val_applicant val_college hdomain
    simpa [applicantOptimalCollegeAssignment,
      gs_stable_college_assignment,
      AppliedModelingLib.Matching.ManyToOne.IsStable,
      AppliedModelingLib.Matching.ManyToOneAssignment.RespectsQuota,
      AppliedModelingLib.Matching.ManyToOne.CollegeWouldAccept] using hstable

theorem theorem2_applicant_optimality :
    theorem2_applicant_optimalitySpec := by
  intro Applicants Colleges _ _ _ _ quota val_applicant val_college
    happlicant_strict hcollege_strict nu hnu
  let hdomain : gs_strict_college_admissions_domain val_applicant val_college :=
    ⟨happlicant_strict, hcollege_strict⟩
  have hoptimal :=
    ExactCollegeBatchedProcedure.paper_gs62_source_waiting_list_assignment_applicant_optimal
      quota val_applicant val_college hdomain
  simpa [applicantOptimalCollegeAssignment,
    gs_applicant_optimal_college_assignment,
    gs_stable_college_assignment,
    AppliedModelingLib.Matching.ManyToOne.IsStable,
    AppliedModelingLib.Matching.ManyToOneAssignment.RespectsQuota,
    AppliedModelingLib.Matching.ManyToOne.CollegeWouldAccept] using hoptimal.2 nu hnu

end PaperInterface
end GS62CollegeAdmissions
