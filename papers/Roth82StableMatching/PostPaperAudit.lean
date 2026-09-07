import Roth82StableMatching.PaperInterface

/-!
# Post-Paper Audit: Roth 1982 Stable Matching

This ledger exposes source-numbered final endpoints for the post-verification
audit. For the compact human-facing statement surface, read
`PaperInterface.lean`. Each declaration here is intentionally a thin alias to
the paper-facing theorem proved in `MainTheorems.lean`.

The endpoints include the strict marriage theorems, source-stage algorithm
refinements, responsive arbitrary-quota extension, dummy-agent completion,
indexed serial procedure, and the Section 6 numerical witness.
-/

namespace Roth82StableMatching
open AppliedModelingLib.Matching

namespace PostPaperAudit

/-! ## Source-model and procedure completion endpoints -/

/-- Audit endpoint for the source's men-proposing batched-stage procedure. -/
theorem audit_roth82_batched_da_refines_outcome
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : PaperInterface.strictMarriageDomain val_m val_w) :
    PaperInterface.sourceBatchedMenDeferredAcceptance val_m val_w =
      PaperInterface.menDeferredAcceptance val_m val_w :=
  PaperInterface.sourceBatchedMenDeferredAcceptance_refines
    val_m val_w hcard hdomain

/-- Audit endpoint for the source's women-proposing batched-stage procedure. -/
theorem audit_roth82_women_batched_da_refines_outcome
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : PaperInterface.strictMarriageDomain val_m val_w) :
    PaperInterface.sourceBatchedWomenDeferredAcceptance val_m val_w =
      PaperInterface.womenDeferredAcceptance val_m val_w :=
  PaperInterface.sourceBatchedWomenDeferredAcceptance_refines
    val_m val_w hcard hdomain

/-- Audit endpoint for Roth's arbitrary-quota extension of Theorems 1 and 2. -/
theorem audit_roth82_general_quota_stable_and_both_side_optimal
    {Applicants Colleges : Type*}
    [Fintype Applicants] [Fintype Colleges]
    [DecidableEq Applicants] [DecidableEq Colleges]
    (quota : Colleges → ℕ)
    (val_applicant : Applicants → Colleges → ℝ)
    (val_college : Colleges → Applicants → ℝ)
    (hdomain : PaperInterface.strictQuotaDomain val_applicant val_college) :
    PaperInterface.stableQuotaAssignment quota val_applicant val_college
        (PaperInterface.quotaBatchedDeferredAcceptance
          quota val_applicant val_college hdomain) ∧
      PaperInterface.applicantOptimalQuotaAssignment quota val_applicant val_college
        (PaperInterface.quotaBatchedDeferredAcceptance
          quota val_applicant val_college hdomain) ∧
      ∃! mu : PaperInterface.quotaAssignment Applicants Colleges,
        GS62CollegeAdmissions.ManyToOneOptimality.gs_college_optimal_college_assignment
            quota val_applicant val_college hdomain.1.2 mu ∧
          GS62CollegeAdmissions.ManyToOneOptimality.gs_responsive_college_optimal_assignment
            quota val_applicant val_college mu :=
  PaperInterface.generalQuota_stable_and_both_side_optimal
    quota val_applicant val_college hdomain

/-- Audit endpoint for the optional-outcome/dummy-agent representation. -/
theorem audit_roth82_dummy_agents_complete_optional_assignment
    {M W : Type*} [Fintype M] [Fintype W] (mu : Assignment M W) :
    Fintype.card (M ⊕ W) = Fintype.card (W ⊕ M) ∧
      ((∀ x, ∃ y, (paper_dummy_completion mu).m_match x = some y) ∧
        ∀ y, ∃ x, (paper_dummy_completion mu).w_match y = some x) ∧
      (∀ m w,
        (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inl w) ↔
          mu.m_match m = some w) ∧
      (∀ m,
        (paper_dummy_completion mu).m_match (Sum.inl m) = some (Sum.inr m) ↔
          mu.m_match m = none) ∧
      ∀ w,
        (paper_dummy_completion mu).w_match (Sum.inl w) = some (Sum.inr w) ↔
          mu.w_match w = none :=
  PaperInterface.dummyAgents_complete_optional_assignment mu

/-- Audit endpoint for the indexed top-remaining serial-dictatorship step. -/
theorem audit_roth82_serial_choice_best_remaining {n : ℕ}
    (val_m : Fin n → Fin n → ℝ) (i : Fin n) (w : Fin n)
    (hw : w ∈ PaperInterface.serialRemainingWomen val_m i) :
    val_m i w ≤ val_m i (PaperInterface.serialChoice val_m i) :=
  PaperInterface.serialChoice_best_remaining val_m i w hw

/-- Audit endpoint for the exact Section 6 beneficial-bystander example. -/
theorem audit_roth82_section6_beneficial_bystander_example :
    PaperInterface.sourceBatchedMenDeferredAcceptance theorem3MenProfile
        theorem3WomenProfilePrime = theorem3OutcomeY ∧
      PaperInterface.sourceBatchedMenDeferredAcceptance
        paper_roth82_section6_reported_men theorem3WomenProfilePrime =
          theorem3OutcomeX ∧
      paper_matching_valM theorem3MenProfile 1
          (theorem3OutcomeY.m_match 1) =
        paper_matching_valM theorem3MenProfile 1
          (theorem3OutcomeX.m_match 1) ∧
      paper_matching_valM theorem3MenProfile 0
          (theorem3OutcomeY.m_match 0) <
        paper_matching_valM theorem3MenProfile 0
          (theorem3OutcomeX.m_match 0) ∧
      paper_matching_valM theorem3MenProfile 2
          (theorem3OutcomeY.m_match 2) <
        paper_matching_valM theorem3MenProfile 2
          (theorem3OutcomeX.m_match 2) :=
  PaperInterface.section6_beneficial_bystander_example

/-- Audit endpoint for Roth Theorem 1: existence of a stable outcome. -/
theorem audit_roth82_theorem1_stable_outcome_exists
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) :
    ∃ mu : Assignment M W, paper_is_stable val_m val_w mu :=
  paper_roth82_theorem1_stable_outcome_exists val_m val_w

/--
Audit endpoint for Roth Theorem 1 on the equal-size strict marriage domain:
existence of a stable complete matching.
-/
theorem audit_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    ∃ mu : Assignment M W,
      paper_is_stable val_m val_w mu ∧ paper_is_complete_matching mu :=
  paper_roth82_theorem1_stable_complete_outcome_exists_on_strict_marriage_domain
    val_m val_w hcard hdomain

/--
Audit endpoint for Roth Theorem 2: men-optimal and women-optimal stable
outcomes on the strict marriage domain.
-/
theorem audit_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    (∃ mu : Assignment M W, paper_is_men_optimal val_m val_w mu) ∧
      (∃ mu : Assignment M W, paper_is_women_optimal val_m val_w mu) :=
  paper_roth82_theorem2_optimal_stable_outcomes_on_strict_marriage_domain
    val_m val_w hdomain

/--
Audit endpoint for Roth Theorem 3: no procedure stable on strict profiles is
truthful for both sides on strict profiles.
-/
theorem audit_roth82_theorem3_no_stable_truthful_procedure :
    ¬ ∃ mechanism :
      (Theorem3Agent → Theorem3Agent → ℝ) →
        (Theorem3Agent → Theorem3Agent → ℝ) →
          Assignment Theorem3Agent Theorem3Agent,
      paper_stable_matching_procedure_on_strict_profiles mechanism ∧
        paper_truthful_for_men_on_strict_profiles mechanism ∧
          paper_truthful_for_women_on_strict_profiles mechanism :=
  paper_roth82_theorem3_no_stable_truthful_procedure_on_strict_profiles

/--
Audit endpoint for Roth Theorem 4: the constructed serial-dictatorship route is
men-efficient on strict men-side profiles and strategyproof in the theorem's
stated senses.
-/
theorem audit_roth82_theorem4_serial_dictatorship_constructed {n : ℕ} :
    paper_efficient_matching_procedure_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_men_on_strict_men
        (paper_serial_dictatorship_mechanism (n := n)) ∧
      paper_truthful_for_women
        (paper_serial_dictatorship_mechanism (n := n)) :=
  paper_roth82_theorem4_serial_dictatorship_constructed

/--
Audit endpoint for Roth Lemma 1: a simple misrepresentation that leaves the
manipulator's named partner in the general report also gives the same partner
under the associated simple misrepresentation.
-/
theorem audit_roth82_lemma1_strict_simple_misrepresentation_same_partner
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ) (m : M)
    (report_m simple_report_m : W → ℝ) (wstar : W)
    (hdomainSimple :
      paper_strict_marriage_domain (Function.update val_m m simple_report_m) val_w)
    (hyPartner :
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m =
        some wstar)
    (hfirst : ∀ w, w ≠ wstar → simple_report_m w < simple_report_m wstar) :
    (deferredAcceptance (Function.update val_m m simple_report_m) val_w).m_match m =
      (deferredAcceptance (Function.update val_m m report_m) val_w).m_match m :=
  paper_roth82_lemma1_strict_simple_misrepresentation_same_partner
    val_m val_w m report_m simple_report_m wstar hdomainSimple hyPartner hfirst

/--
Audit endpoint for Roth Lemma 2: a simple misrepresentation by one man cannot
harm any other man on the strict marriage domain.
-/
theorem audit_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (m : M) (simple_report_m : W → ℝ) (ystar : W)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w)
    (hdomainReport :
      paper_strict_marriage_domain
        (Function.update val_m m simple_report_m) val_w)
    (hy :
      (deferredAcceptance
        (Function.update val_m m simple_report_m) val_w).m_match m =
          some ystar)
    (hweakM :
      paper_man_weakly_prefers_outcome val_m m
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w))
    (hfirst :
      paper_man_report_strictly_ranks_partner_first simple_report_m
        (some ystar)) :
    ∀ m',
      paper_man_weakly_prefers_outcome val_m m'
        (deferredAcceptance (Function.update val_m m simple_report_m) val_w)
        (deferredAcceptance val_m val_w) :=
  paper_roth82_lemma2_strict_simple_misrepresentation_no_men_harmed_on_strict_domain
    val_m val_w m simple_report_m ystar hcard hdomain hdomainReport hy hweakM hfirst

/--
Audit endpoint for Roth Theorem 5: the side-optimal deferred-acceptance
procedures are strategyproof for their proposing side on the equal-size strict
marriage domain.
-/
theorem audit_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W] :
    ∀ (val_m : M → W → ℝ) (val_w : W → M → ℝ),
      Fintype.card M = Fintype.card W →
        paper_strict_marriage_domain val_m val_w →
          (∀ (m : M) (report_m : W → ℝ),
            paper_matching_valM val_m m
                ((deferredAcceptance
                  (Function.update val_m m report_m) val_w).m_match m) ≤
              paper_matching_valM val_m m
                ((deferredAcceptance val_m val_w).m_match m)) ∧
          (∀ (w : W) (report_w : M → ℝ),
            paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m
                  (Function.update val_w w report_w)).w_match w) ≤
              paper_matching_valW val_w w
                ((paper_women_deferredAcceptance val_m val_w).w_match w)) :=
  paper_roth82_theorem5_optimal_side_truthful_on_strict_domain_of_card_eq

/--
Audit endpoint for Roth Corollary 5.1: women do not need to misrepresent their
first choices to obtain the best available manipulation outcome.
-/
theorem audit_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M] :
    paper_no_need_to_misrepresent_first_choice_for_women_on_strict_domain
      (deferredAcceptance (M := M) (W := W)) :=
  paper_roth82_corollary5_1_no_need_to_misrepresent_first_choice_on_strict_domain

/--
Audit endpoint for Roth Corollary 5.1, role-reversed: men under women-proposing
DA do not need to misrepresent their first choices to obtain the best available
manipulation outcome.
-/
theorem audit_roth82_corollary5_1_role_reversed_no_need_to_misrepresent_first_choice_on_strict_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty W] :
    paper_no_need_to_misrepresent_first_choice_for_men_on_strict_domain
      (paper_women_deferredAcceptance (M := M) (W := W)) :=
  paper_roth82_corollary5_1_role_reversed_no_need_to_misrepresent_first_choice_on_strict_domain

/--
Audit endpoint for Roth Theorem 6: no feasible outcome is strictly better for
all men than the men-optimal stable outcome.
-/
theorem audit_roth82_theorem6_on_strict_marriage_domain
    {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    [Nonempty M]
    (val_m : M → W → ℝ) (val_w : W → M → ℝ)
    (hcard : Fintype.card M = Fintype.card W)
    (hdomain : paper_strict_marriage_domain val_m val_w) :
    paper_weakly_pareto_optimal_for_men val_m (deferredAcceptance val_m val_w) :=
  paper_roth82_theorem6_on_strict_marriage_domain
    val_m val_w hcard hdomain

/--
Audit endpoint for Roth Theorem 7: for every `k > 1`, a procedure stable on
strict profiles admits a profitable strict-profile `k`th-choice
misrepresentation on some finite balanced market.
-/
theorem audit_roth82_theorem7_arbitrary_k :
    ∀ k, 1 < k →
      ∃ n : ℕ,
        paper_no_stable_procedure_avoids_strict_kth_choice_manipulation_on
          (Fin n) (Fin n) k :=
  paper_roth82_theorem7_arbitrary_k_on_strict_profiles

end PostPaperAudit

end Roth82StableMatching
