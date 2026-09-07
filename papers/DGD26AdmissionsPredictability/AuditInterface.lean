import DGD26AdmissionsPredictability.MainTheorems
import DGD26AdmissionsPredictability.Assumptions

/-!
# Audited Review Surface: Capacity Constraints Make Admissions Processes Less Predictable

This file exposes the current source-facing Lean surface for the paper. It is
ordered by the paper's definitions and early appendix results.
-/

namespace DGD26AdmissionsPredictability

open AppliedModelingLib.FiniteChoice

variable {α : Type*} [DecidableEq α]

/-! ## Source Definitions -/

/--
Paper choice functions over a finite applicant universe.
Source status: paper-facing source type row; row-local LLM validation pending.
-/
abbrev paper_choice_function :=
  PaperChoiceRule α

/--
Source convention: selected applicants are contained in the input set.
Source status: paper-facing source convention row; row-local LLM validation pending.
-/
abbrev paper_choice_function_feasible (C : PaperChoiceRule α) : Prop :=
  paper_feasible C

/-- Binary choice label `C(X)_i`, equal to one exactly for chosen applicants. -/
abbrev paper_definition_choice_label
    (C : PaperChoiceRule α) (X : Finset α) (x : α) : ℕ :=
  paperChoiceLabel C X x

/-- A predictor represents `C` when its label agrees on every offered applicant and pool. -/
abbrev paper_definition_ml_representation
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α) : Prop :=
  paperRepresentsChoice predicts C

/-- Pool-independent fixed-threshold score formula `1{s(x) ≥ t}`. -/
abbrev paper_definition_fixed_threshold_predictor
    (score : α → ℝ) (threshold : ℝ) : PaperPoolPredictor α :=
  paperFixedThresholdPredictor score threshold

/-- Cohort-dependent rank formula `1{s(x) ≥ t_q(X)}`. -/
noncomputable abbrev paper_definition_rank_threshold_predictor
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    PaperPoolPredictor α :=
  paperRankThresholdPredictor q score hinjective

/--
Definition q-Acceptance: `C` chooses exactly `min q |X|` applicants from each
finite applicant set `X`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_q_acceptance (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_q_acceptant q C

/--
Definition Choice Distance:
`r_C(X_1,X_2) = |X_1 ∩ C(X_2) \ C(X_1)| + |C(X_1) \ C(X_2)|`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_choice_distance
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  paper_choiceDistance C X₁ X₂

/--
Definition d-Instability: adding any fresh applicant changes at most `d`
existing applicant decisions.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_d_instability (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_d_unstable d C

/--
Definition tight d-Instability: `d` is the least instability bound.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_tight_d_instability
    (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_tightly_d_unstable d C

/--
Appendix Definition 0-Instability for all nested applicant sets.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_zero_instability (C : PaperChoiceRule α) : Prop :=
  paper_zero_unstable C

/--
Definition Substitutability:
`X_1 ⊆ X_2` implies `X_1 ∩ C(X_2) ⊆ C(X_1)`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_substitutability (C : PaperChoiceRule α) : Prop :=
  paper_substitutable C

/--
Appendix Definition Monotonicity: `X_1 ⊆ X_2` implies `C(X_1) ⊆ C(X_2)`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_monotonicity (C : PaperChoiceRule α) : Prop :=
  paper_monotonic C

/--
Appendix Definition Consistency:
if `C(X_2) ⊆ X_1 ⊆ X_2`, then `C(X_2)=C(X_1)`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_consistency (C : PaperChoiceRule α) : Prop :=
  paper_consistent C

/--
Appendix Definition Independence: every applicant is either always accepted
whenever available or always rejected whenever available.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_independence (C : PaperChoiceRule α) : Prop :=
  paper_independent C

/--
Definition total ordering over applicants.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_total_order (r : α → α → Prop) : Prop :=
  paper_total_order r

/--
Definition q-Representativeness: a single priority order explains choices.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_q_representativeness
    (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_q_representative q C

/--
Definition sequential composition of admissions queues.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_sequential_composition
    (Cs : List (PaperChoiceRule α)) : PaperChoiceRule α :=
  paper_sequential_composition Cs

/--
Definition borderline set: current admits displaced by some added applicant.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_borderline_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  paper_borderline_set C X

/--
Appendix waitlisted set: rejected applicants admitted after some removal.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_waitlisted_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  paper_waitlisted_set C X

/--
Main-text variability bound.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_variability_at_most m C

/--
Main-text exact variability: an upper bound with a witnessing pool.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_variability_exactly m C

/--
Nontriviality witness: some added applicant displaces an existing admit.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_has_displacement (C : PaperChoiceRule α) : Prop :=
  paper_has_displacement C

/--
Appendix general variability bound.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_general_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_general_variability_at_most m C

/--
Appendix exact general variability.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_general_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_general_variability_exactly m C

/-! ## Linear Assignment Appendix Definitions -/

/--
A finite-slot linear assignment.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_assignment
    (σ : Type*) [DecidableEq σ] :=
  LAP.Assignment α σ

/--
An applicant is assigned by a finite-slot assignment.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_assigned
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : LAP.Assignment α σ) (x : α) : Prop :=
  A.Assigned x

/--
Assignment feasibility for a finite applicant pool.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_assignment_feasible
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (A : LAP.Assignment α σ) : Prop :=
  A.Feasible X

/--
Applicants chosen by a finite-slot assignment: those assigned to some slot.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_chosen_set
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : LAP.Assignment α σ) : Finset α :=
  A.chosenSet

/--
Capacity filling for a finite assignment: below slot capacity all applicants
are assigned, and at or above slot capacity all slots are occupied.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_capacity_filling
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (A : LAP.Assignment α σ) : Prop :=
  A.CapacityFilling X

/--
Choice rule induced by choosing a finite-slot assignment for each pool.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_choice_rule
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) : PaperChoiceRule α :=
  LAP.Assignment.choiceRuleOfAssignment select

/--
A rejected applicant in the finite assignment model.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_rejected
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (A : LAP.Assignment α σ) (x : α) : Prop :=
  A.Rejected X x

/--
Primitive local optimality: no profitable feasible one-slot swap.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_no_profitable_one_slot_swap
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  A.NoProfitableOneSlotSwap X w

/--
Capacity-filling objective optimality used by the paper's fixed-slot LAP
results.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_objective_optimal
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  A.ObjectiveOptimal X w

/--
Slot-weight weak ordering in the finite assignment model.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_slot_at_least
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (a b : α) : Prop :=
  LAP.Assignment.SlotAtLeast w s a b

/--
Slot-weight strict ordering in the finite assignment model.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
abbrev paper_definition_lap_slot_below
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (a b : α) : Prop :=
  LAP.Assignment.SlotBelow w s a b

/-! ## Early Appendix Results -/

/--
The displayed choice-distance formula is the reusable finite-choice definition.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_choice_distance_formula
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) :
    choiceDistance C X₁ X₂ =
      ((X₁ ∩ C X₂) \ C X₁).card + (C X₁ \ C X₂).card := by
  simpa [paper_choiceDistance] using paper_choiceDistance_eq_library C X₁ X₂

/--
Substitutability is equivalent to the first choice-distance term vanishing.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_substitutability_term_statement
    (C : PaperChoiceRule α) :
    paper_definition_substitutability C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        ((X₁ ∩ C X₂) \ C X₁).card = 0 := by
  simpa [paper_definition_substitutability] using paper_substitutability_term C

/--
Monotonicity is equivalent to the second choice-distance term vanishing.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_monotonicity_term_statement
    (C : PaperChoiceRule α) :
    paper_definition_monotonicity C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        (C X₁ \ C X₂).card = 0 := by
  simpa [paper_definition_monotonicity] using paper_monotonicity_term C

/--
Zero instability is equivalent to substitutability and monotonicity.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_zero_distance_statement
    (C : PaperChoiceRule α) :
    paper_definition_zero_instability C ↔
      paper_definition_substitutability C ∧ paper_definition_monotonicity C := by
  simpa [paper_definition_zero_instability, paper_definition_substitutability,
    paper_definition_monotonicity] using
      paper_zero_distance_iff_substitutable_and_monotonic C

/--
Under feasibility, independence is equivalent to substitutability plus
monotonicity.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_independent_substitutable_monotonic_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C) :
    paper_definition_independence C ↔
      paper_definition_substitutability C ∧ paper_definition_monotonicity C := by
  simpa [paper_choice_function_feasible, paper_definition_independence,
    paper_definition_substitutability, paper_definition_monotonicity] using
      paper_independent_iff_substitutable_and_monotonic C hfeasible

/--
Under feasibility, independence is equivalent to zero instability.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_independent_zero_unstable_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C) :
    paper_definition_independence C ↔ paper_definition_zero_instability C := by
  simpa [paper_choice_function_feasible, paper_definition_independence,
    paper_definition_zero_instability] using
      paper_independent_iff_zero_unstable C hfeasible

/--
Choice distance satisfies the triangle inequality along nested applicant pools.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_choice_distance_triangle_statement
    (C : PaperChoiceRule α) {X₁ X₂ X₃ : Finset α}
    (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
    paper_definition_choice_distance C X₁ X₃ ≤
      paper_definition_choice_distance C X₁ X₂ +
        paper_definition_choice_distance C X₂ X₃ := by
  simpa [paper_definition_choice_distance] using
    paper_choice_distance_triangle C h₁₂ h₂₃

/--
A d-unstable choice function changes at most `d` times the number of newly
added applicants when expanding from `X` to `X ∪ S`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_choice_distance_multi_add_bound_statement
    {d : ℕ} {C : PaperChoiceRule α}
    (hunstable : paper_definition_d_instability d C)
    (X S : Finset α) :
    paper_definition_choice_distance C X (X ∪ S) ≤ d * (S \ X).card := by
  exact paper_choice_distance_multi_add_bound hunstable X S

/--
Every q-acceptant substitutable choice function is consistent.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_acceptant_substitutable_consistent_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C) :
    paper_definition_consistency C := by
  intro X₁ X₂ hchosen_subset hsubset
  exact paper_q_acceptant_substitutable_consistent
    (C := C) haccept hsub hchosen_subset hsubset

/--
Corrected removable-set lemma: if two applicant pools induce the same chosen
set under a feasible q-acceptant substitutable rule, then they have the same
borderline set.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_corrected_consistency_of_removable_sets_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂) :
    paper_definition_borderline_set C X₁ =
      paper_definition_borderline_set C X₂ := by
  exact paper_corrected_consistency_of_removable_sets
    (C := C) hfeasible haccept hsub hchoice

/--
Append/remove exchange helper: when removing `x` makes `y` newly chosen, the
new chosen set is exactly the old chosen set with `x` replaced by `y`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_waitlisted_witness_exact_exchange_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    {X : Finset α} {x y : α}
    (hxX : x ∈ X)
    (hy : y ∈ C (X.erase x) \ C X) :
    x ∈ C X ∧ (C X).card = q ∧
      C (X.erase x) = insert y ((C X).erase x) := by
  exact paper_waitlisted_witness_exact_exchange
    (C := C) hfeasible haccept hsub hxX hy

/--
Append/remove batch helper: a finite family of waitlisted applicants matched
to distinct removable admits becomes borderline after all matched admits are
removed.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_waitlisted_family_subset_borderline_after_matched_removals_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    {X W : Finset α} {mate : α → α}
    (hcardCX : (C X).card = q)
    (hWsubset : W ⊆ X \ C X)
    (hmate_chosen : ∀ y, y ∈ W → mate y ∈ C X)
    (hmate_inj : ∀ {y z}, y ∈ W → z ∈ W → mate y = mate z → y = z)
    (hmatch :
      ∀ y, y ∈ W →
        C (X.erase (mate y)) = insert y ((C X).erase (mate y))) :
    W ⊆ paper_definition_borderline_set C (X \ W.image mate) := by
  exact paper_waitlisted_family_subset_borderline_after_matched_removals
    (C := C) hfeasible haccept hsub hcardCX hWsubset hmate_chosen
    hmate_inj hmatch

/--
Append/remove cardinal bridge: every waitlisted set is no larger than the
borderline set at some reduced pool.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_waitlisted_set_card_le_some_borderline_set_card_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    (X : Finset α) :
    ∃ Y : Finset α,
      (paper_definition_waitlisted_set C X).card ≤
        (paper_definition_borderline_set C Y).card := by
  exact paper_waitlisted_set_card_le_some_borderline_set_card
    (C := C) hfeasible haccept hsub X

/--
Append/remove theorem, threshold form: for q-acceptant 1-unstable rules, the
appendix general variability upper bound is equivalent to the main-text
borderline-only upper bound.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_append_remove_variability_at_most_equivalence_statement
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C) :
    paper_definition_general_variability_at_most m C ↔
      paper_definition_variability_at_most m C := by
  exact paper_append_remove_variability_at_most_equivalence
    (C := C) hfeasible haccept hunstable

/--
Append/remove theorem, exact form: for q-acceptant 1-unstable rules, exact
appendix general variability is equivalent to exact main-text variability.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_append_remove_variability_exact_equivalence_statement
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C) :
    paper_definition_general_variability_exactly m C ↔
      paper_definition_variability_exactly m C := by
  exact paper_append_remove_variability_exact_equivalence
    (C := C) hfeasible haccept hunstable

/--
Append/remove exchange helper: when adding fresh `x` displaces `y`, the new
chosen set is exactly the old chosen set with `y` replaced by `x`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_borderline_witness_exact_exchange_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    (hunstable : paper_definition_d_instability 1 C)
    {X : Finset α} {x y : α}
    (hx : x ∉ X)
    (hy : y ∈ C X \ C (insert x X)) :
    x ∈ C (insert x X) ∧ (C X).card = q ∧
      C (insert x X) = insert x ((C X).erase y) := by
  exact paper_borderline_witness_exact_exchange
    (C := C) hfeasible haccept hsub hunstable hx hy

/--
No feasible choice function is both monotonic and q-acceptant when a positive
capacity faces an applicant pool larger than capacity.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_monotonicity_q_acceptance_incompatible_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hmono : paper_definition_monotonicity C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    False := by
  exact paper_monotonicity_q_acceptance_incompatible
    (C := C) hfeasible hmono haccept hqpos hUcard

/--
If a choice function is not substitutable, a single added applicant can cause a
previously rejected existing applicant to become accepted.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_non_substitutable_single_add_statement
    (C : PaperChoiceRule α)
    (hnot : ¬ paper_definition_substitutability C) :
    ∃ X x xstar,
      x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X := by
  exact paper_non_substitutable_single_add C hnot

/--
Substitutability implies 1-instability under feasibility and q-acceptance.
This is the forward direction of the appendix equivalence theorem.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_one_instability_of_substitutability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C) :
    paper_definition_d_instability 1 C := by
  exact paper_one_instability_of_q_acceptant_substitutable
    (C := C) hfeasible haccept hsub

/--
On the positive, nontrivial capacity domain, substitutability is equivalent
to exact one-instability: a one-step bound together with non-zero instability.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_substitutability_one_instability_equivalence_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    paper_definition_substitutability C ↔
      paper_definition_d_instability 1 C ∧ ¬ paper_definition_zero_instability C := by
  constructor
  · intro hsub
    exact ⟨(paper_substitutability_iff_one_instability_of_q_acceptant
        (C := C) hfeasible haccept).mp hsub,
      paper_no_zero_unstable_of_q_acceptant_nontrivial hfeasible haccept hqpos hUcard⟩
  · rintro ⟨hone, _⟩
    exact (paper_substitutability_iff_one_instability_of_q_acceptant
      (C := C) hfeasible haccept).mpr hone

/--
When `X` is already at capacity, adding a fresh applicant gives choice distance
`2n-1` if the fresh applicant is chosen and `2n` otherwise, where `n` is the
number of old choices displaced.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_calculating_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hx : x ∉ X) :
    paper_definition_choice_distance C X (insert x X) =
      if x ∈ C (insert x X) then
        2 * (C X \ C (insert x X)).card - 1
      else
        2 * (C X \ C (insert x X)).card := by
  exact paper_calculating_instability
    (C := C) hfeasible haccept hcard hx

/--
If a fresh insertion produces positive even choice distance, then the choice
function is inconsistent. The fresh applicant's nonselection is derived from
the displayed parity formula rather than assumed.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_even_instability_inconsistency_forward_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hpositive : 0 < paper_definition_choice_distance C X (insert x X))
    (heven : ∃ k, paper_definition_choice_distance C X (insert x X) = 2 * k) :
    ¬ paper_definition_consistency C := by
  exact paper_inconsistent_of_positive_even_insert_distance
    (C := C) hfeasible haccept hx hpositive heven

/--
Conversely, if a feasible q-acceptant choice function is inconsistent, then
some single fresh addition has positive even choice distance.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_even_instability_inconsistency_converse_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hnot : ¬ paper_definition_consistency C) :
    ∃ X x, x ∉ X ∧
      0 < paper_definition_choice_distance C X (insert x X) ∧
        ∃ k, paper_definition_choice_distance C X (insert x X) = 2 * k := by
  exact paper_exists_positive_even_distance_of_inconsistent
    (C := C) hfeasible haccept hnot

/--
Consistent q-acceptant choice functions cannot be tightly 2-unstable: any
2-instability bound improves to a 1-instability bound.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_no_consistent_tightly_two_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C)
    (hunstable : paper_definition_d_instability 2 C) :
    paper_definition_d_instability 1 C := by
  exact paper_no_consistent_tightly_two_instability
    (C := C) hfeasible haccept hcons hunstable

/--
Consistent q-acceptant choice functions cannot be tightly positive-even
unstable: any `2*k`-instability bound with `k > 0` improves to `2*k - 1`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_no_consistent_tightly_even_instability_statement
    {q k : ℕ} {C : PaperChoiceRule α}
    (hk : 0 < k)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C)
    (hunstable : paper_definition_d_instability (2 * k) C) :
    paper_definition_d_instability (2 * k - 1) C := by
  exact paper_no_consistent_tightly_even_instability
    (C := C) hk hfeasible haccept hcons hunstable

/--
Every q-acceptant choice function is at most `2q`-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_acceptant_two_q_instability_bound_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (haccept : paper_definition_q_acceptance q C) :
    paper_definition_d_instability (2 * q) C := by
  exact paper_q_acceptant_two_q_instability_bound haccept

/--
For every positive capacity with two disjoint q-sized applicant blocks and one
fresh trigger applicant, the switch construction is feasible, q-acceptant, and
tightly `2*q`-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_max_even_instability_family_statement
    {q : ℕ} {A B : Finset α} {z : α}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    paper_choice_function_feasible (switchEvenChoice q A B z) ∧
      paper_definition_q_acceptance q (switchEvenChoice q A B z) ∧
        paper_definition_tight_d_instability
          (2 * q) (switchEvenChoice q A B z) := by
  exact
    paper_tight_max_even_instability_family
      hqpos hAcard hBcard hdisj hzA hzB

/--
Complementary-group construction for the paper's odd tight-instability
examples: a trigger group layered over a consistent q-acceptant fallback rule
is tightly `(2*q - 1)`-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_max_odd_instability_family_statement
    {q : ℕ} {A B : Finset α} {z : α} {F : PaperChoiceRule α}
    (hAcard : A.card = q)
    (htrigger_card : (insert z B).card = q)
    (hdisj : Disjoint A (insert z B))
    (hFfeasible : paper_choice_function_feasible F)
    (hFaccept : paper_definition_q_acceptance q F)
    (hFconsistent : paper_definition_consistency F)
    (hFbase : F (A ∪ B) = A)
    (hzA : z ∉ A) (hzB : z ∉ B) :
    paper_choice_function_feasible (switchOddChoice q B z F) ∧
      paper_definition_q_acceptance q (switchOddChoice q B z F) ∧
        paper_definition_tight_d_instability
          (2 * q - 1) (switchOddChoice q B z F) := by
  exact
    paper_tight_max_odd_instability_family
      hAcard htrigger_card hdisj hFfeasible hFaccept hFconsistent
      hFbase hzA hzB

/--
For every `0 < n ≤ q`, there is a feasible q-acceptant choice rule that is
tightly `2*n`-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_padded_even_tight_instability_family_statement
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_choice_function_feasible (paddedEvenChoice q n) ∧
      paper_definition_q_acceptance q (paddedEvenChoice q n) ∧
        paper_definition_tight_d_instability (2 * n) (paddedEvenChoice q n) := by
  exact paper_padded_even_tight_instability_family hnpos hnq

/--
For every `0 < n ≤ q`, there is a feasible q-acceptant choice rule that is
tightly `2*n - 1`-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_padded_odd_tight_instability_family_statement
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_choice_function_feasible (paddedOddChoice q n) ∧
      paper_definition_q_acceptance q (paddedOddChoice q n) ∧
        paper_definition_tight_d_instability (2 * n - 1) (paddedOddChoice q n) := by
  exact paper_padded_odd_tight_instability_family hnpos hnq

/--
There exists a feasible q-acceptant rule that is tightly 1-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_one_instability_example_statement :
    paper_choice_function_feasible tightOneChoice ∧
      paper_definition_q_acceptance 1 tightOneChoice ∧
        paper_definition_tight_d_instability 1 tightOneChoice := by
  exact paper_tight_one_instability_example

/--
There exists a feasible q-acceptant rule that is tightly 2-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_two_instability_example_statement :
    paper_choice_function_feasible tightTwoChoice ∧
      paper_definition_q_acceptance 1 tightTwoChoice ∧
        paper_definition_tight_d_instability 2 tightTwoChoice := by
  exact paper_tight_two_instability_example

/--
There exists a feasible q-acceptant rule that is tightly 3-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_three_instability_example_statement :
    paper_choice_function_feasible tightThreeChoice ∧
      paper_definition_q_acceptance 2 tightThreeChoice ∧
        paper_definition_tight_d_instability 3 tightThreeChoice := by
  exact paper_tight_three_instability_example

/--
There exists a feasible q-acceptant rule that is tightly 4-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_four_instability_example_statement :
    paper_choice_function_feasible tightFourChoice ∧
      paper_definition_q_acceptance 2 tightFourChoice ∧
        paper_definition_tight_d_instability 4 tightFourChoice := by
  exact paper_tight_four_instability_example

/--
There exists a feasible q-acceptant rule that is tightly 5-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_tight_five_instability_example_statement :
    paper_choice_function_feasible tightFiveChoice ∧
      paper_definition_q_acceptance 3 tightFiveChoice ∧
        paper_definition_tight_d_instability 5 tightFiveChoice := by
  exact paper_tight_five_instability_example

/--
A q-representative choice function is q-acceptant by definition.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_q_acceptant_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_q_acceptance q C := by
  exact paper_q_representative_q_acceptant hrep

/--
A feasible q-representative choice function is substitutable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_substitutable_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_substitutability C := by
  exact paper_q_representative_substitutable
    (C := C) hfeasible hrep

/--
A feasible q-representative choice function is 1-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_one_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_d_instability 1 C := by
  exact paper_q_representative_one_instability
    (C := C) hfeasible hrep

/--
A q-representative rule with a real displacement is tightly 1-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_tightly_one_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hwitness : paper_definition_has_displacement C) :
    paper_definition_tight_d_instability 1 C := by
  exact paper_q_representative_tightly_one_instability
    (C := C) hfeasible hrep hwitness

/--
A feasible q-representative choice function has variability at most one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_variability_at_most_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_variability_at_most 1 C := by
  exact paper_q_representative_variability_at_most_one
    (C := C) hfeasible hrep

/--
Conversely, a feasible q-acceptant, 1-unstable choice function with
variability at most one is represented by a single total priority order.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_converse_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_at_most 1 C) :
    paper_definition_q_representativeness q C := by
  exact
    paper_q_representative_of_q_acceptant_one_instability_variability
      hfeasible haccept hunstable hvar

/--
Under feasibility, q-representativeness is equivalent to q-acceptance,
1-instability, and variability at most one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_characterization_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C) :
    paper_definition_q_representativeness q C ↔
      paper_definition_q_acceptance q C ∧
        paper_definition_d_instability 1 C ∧
          paper_definition_variability_at_most 1 C := by
  exact
    paper_q_representative_iff_q_acceptant_one_instability_variability
      hfeasible

/--
Nondegenerate exact q-representative characterization. The positive-capacity
and excess-applicant hypotheses repair the source's omitted degenerate cases.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_exact_characterization_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_q_representativeness q C ↔
      paper_definition_q_acceptance q C ∧
        paper_definition_d_instability 1 C ∧
          paper_definition_variability_exactly 1 C := by
  exact
    paper_q_representative_iff_q_acceptant_one_instability_exact_variability
      hfeasible hqpos hqlt

/--
Under q-acceptance and 1-instability, exact variability one is equivalent to a
single global applicant order in the nondegenerate regime.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_variability_one_iff_single_order_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_variability_exactly 1 C ↔
      paper_definition_q_representativeness q C := by
  exact paper_variability_exactly_one_iff_q_representative
    hfeasible haccept hunstable hqpos hqlt

/--
A feasible q-representative choice function has general variability at most
one: both its borderline and waitlisted sets have size at most one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_general_variability_at_most_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_general_variability_at_most 1 C := by
  exact paper_q_representative_general_variability_at_most_one
    (C := C) hfeasible hrep

/--
For q-acceptant, 1-unstable rules with variability at most one, the appendix
general variability definition is also bounded by one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_acceptant_one_instability_variability_general_variability_at_most_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_at_most 1 C) :
    paper_definition_general_variability_at_most 1 C := by
  exact
    paper_acceptant_one_instability_variability_general_variability_at_most_one
      (C := C) hfeasible haccept hunstable hvar

/--
A feasible q-representative choice function has exact general variability one
when some added applicant actually displaces an existing admit.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_general_variability_exactly_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hwitness : paper_definition_has_displacement C) :
    paper_definition_general_variability_exactly 1 C := by
  exact paper_q_representative_general_variability_exactly_one_of_displacement
    (C := C) hfeasible hrep hwitness

/--
For q-acceptant, 1-unstable rules with variability at most one, any real
displacement gives exact appendix general variability one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_acceptant_one_instability_variability_general_variability_exactly_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_at_most 1 C)
    (hwitness : paper_definition_has_displacement C) :
    paper_definition_general_variability_exactly 1 C := by
  exact
    paper_acceptant_one_instability_variability_general_variability_exactly_one_of_displacement
      (C := C) hfeasible haccept hunstable hvar hwitness

/--
A feasible q-representative choice function has exact variability one at
positive capacity when the finite applicant universe is strictly larger than
capacity. These are the necessary nondegeneracy conditions omitted in the
source statement.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_variability_exactly_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_variability_exactly 1 C := by
  exact paper_q_representative_variability_exactly_one_nontrivial
    (C := C) hfeasible hrep hqpos hqlt

/--
For a feasible q-representative rule at full capacity, if inserting a fresh
applicant changes the choice, the previous borderline set is the new waitlisted
set.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_q_representative_borderline_eq_waitlisted_after_changing_insert_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X) :
    paper_definition_borderline_set C X =
      paper_definition_waitlisted_set C (insert x X) := by
  exact paper_q_representative_borderline_eq_waitlisted_after_changing_insert
    (C := C) hfeasible hrep hx hchange

/--
Ranking-m bridge under the paper's one-queue characterization hypotheses: if a
feasible q-acceptant rule is 1-unstable and has exact variability one, then
a changing fresh insertion has the same previous borderline set as the new
waitlisted set.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X) :
    paper_definition_borderline_set C X =
      paper_definition_waitlisted_set C (insert x X) := by
  exact
    paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert
      (C := C) hfeasible haccept hunstable hvar.1 hx hchange

/-- For an offered applicant, the binary source label is one exactly when `x` belongs to `C(X)`. -/
theorem paper_choice_label_formula_statement
    (C : PaperChoiceRule α) (X : Finset α) (x : α) (hx : x ∈ X) :
    paper_definition_choice_label C X x = 1 ↔ x ∈ C X := by
  exact paperChoiceLabel_eq_one_iff C X x

/-- Exact fixed-threshold score formula for the induced choice rule. -/
theorem paper_fixed_threshold_formula_statement
    (score : α → ℝ) (threshold : ℝ) (X : Finset α) (x : α) :
    x ∈ paperFixedThresholdChoice score threshold X ↔
      x ∈ X ∧ paper_definition_fixed_threshold_predictor
        score threshold X x := by
  exact paperFixedThresholdChoice_mem_iff score threshold X x

/-- The fixed-threshold score formula represents its induced choice function. -/
theorem paper_fixed_threshold_represents_induced_choice_statement
    (score : α → ℝ) (threshold : ℝ) :
    paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold)
      (paperFixedThresholdChoice score threshold) := by
  exact paperFixedThresholdPredictor_represents score threshold

/--
The source's fixed-score, fixed-threshold classifier makes each applicant's
decision independently of the pool and therefore is zero-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_ml_independent_predictions_zero_unstable_statement
    (score : α → ℝ) (threshold : ℝ) :
    paper_definition_zero_instability
      (paperFixedThresholdChoice score threshold) := by
  exact paper_fixed_threshold_predictions_zero_unstable score threshold

/-- Any feasible choice rule represented by the fixed-threshold formula is zero-unstable. -/
theorem paper_ml_fixed_threshold_representation_zero_unstable_statement
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold) C) :
    paper_definition_zero_instability C := by
  exact paper_fixed_threshold_representation_zero_unstable
    score threshold hfeasible hrep

/-- The rank model has the displayed pool-specific threshold form. -/
theorem paper_rank_threshold_formula_statement
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hqpos : 0 < q) (X : Finset α) :
    ∃ threshold : ℝ, ∀ x ∈ X,
      (paper_definition_rank_threshold_predictor
          q score hinjective X x ↔ threshold ≤ score x) := by
  exact paperRankThresholdPredictor_threshold_formula
    q score hinjective hqpos X

/-- The rank-threshold formula represents its induced top-`q` choice rule. -/
theorem paper_rank_threshold_represents_induced_choice_statement
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective)
      (paperRankThresholdChoice q score hinjective) := by
  exact paperRankThresholdPredictor_represents q score hinjective

/--
The source's top-`q` score rule is 1-unstable and has variability at most one.
The injectivity premise makes explicit the source proof's score-embedding step.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_ml_rank_threshold_one_instability_variability_statement
    [Fintype α] (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score) :
    paper_definition_d_instability 1
        (paperRankThresholdChoice q score hinjective) ∧
      paper_definition_variability_at_most 1
        (paperRankThresholdChoice q score hinjective) := by
  exact paper_score_rank_threshold_one_instability_and_variability
    q score hinjective

/-- A feasible rule represented by the rank-threshold formula obeys both bounds. -/
theorem paper_ml_rank_threshold_representation_bounds_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective) C) :
    paper_definition_d_instability 1 C ∧
      paper_definition_variability_at_most 1 C := by
  exact paper_rank_threshold_representation_one_instability_and_variability
    q score hinjective hfeasible hrep

/--
In the nondegenerate regime the concrete score-rank rule is tightly
1-unstable and has exact variability one.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_ml_rank_threshold_exact_one_nontrivial_statement
    [Fintype α] (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_tight_d_instability 1
        (paperRankThresholdChoice q score hinjective) ∧
      paper_definition_variability_exactly 1
        (paperRankThresholdChoice q score hinjective) := by
  exact paper_score_rank_threshold_exact_one_nontrivial
    q score hinjective hqpos hqlt

/-- A represented nondegenerate rank-threshold choice has both bounds tightly. -/
theorem paper_ml_rank_threshold_representation_exact_one_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective) C)
    (hqpos : 0 < q) (hqlt : q < Fintype.card α) :
    paper_definition_tight_d_instability 1 C ∧
      paper_definition_variability_exactly 1 C := by
  exact paper_rank_threshold_representation_exact_one_nontrivial
    q score hinjective hfeasible hrep hqpos hqlt

/-- Some finite rank-threshold model realizes exact instability/variability one. -/
theorem paper_ml_rank_threshold_can_represent_exact_one_statement
    (q : ℕ) (hqpos : 0 < q) :
    ∃ (score : Fin (q + 1) → ℝ) (hinjective : Function.Injective score),
      paper_definition_tight_d_instability 1
          (paperRankThresholdChoice q score hinjective) ∧
        paper_definition_variability_exactly 1
          (paperRankThresholdChoice q score hinjective) := by
  exact paper_rank_threshold_can_represent_exact_one q hqpos

/--
Sequential composition of feasible choice functions is feasible.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_composition_feasible_statement
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_choice_function_feasible C) :
    paper_choice_function_feasible (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_composition_feasible hfeasible

/--
A sequential composition of feasible q-acceptant queues is q-acceptant, with
capacity equal to the sum of the queue capacities.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_composition_q_acceptant_statement
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hstages : List.Forall₂
      (fun q C =>
        paper_choice_function_feasible C ∧ paper_definition_q_acceptance q C)
      qs Cs) :
    paper_definition_q_acceptance qs.sum
      (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_composition_q_acceptant hstages

/--
Sequential composition of feasible substitutable choice functions is
substitutable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_composition_substitutable_statement
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_choice_function_feasible C)
    (hsub : ∀ C ∈ Cs, paper_definition_substitutability C) :
    paper_definition_substitutability (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_composition_substitutable hfeasible hsub

/--
Sequential composition of feasible q-acceptant 1-unstable queues has
variability bounded by the sum of the supplied queue variability bounds.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_additive_variability_bound_statement
    [Fintype α] {qms : List (ℕ × ℕ)} {Cs : List (PaperChoiceRule α)}
    (hstages : List.Forall₂
      (fun qm C =>
        paper_choice_function_feasible C ∧
          paper_definition_q_acceptance qm.1 C ∧
            paper_definition_d_instability 1 C ∧
              paper_definition_variability_at_most qm.2 C)
      qms Cs) :
    paper_definition_variability_at_most
      (qms.map Prod.snd).sum (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_additive_variability_bound hstages

/--
A sequential composition of feasible single-order queues has variability at
most the number of queues.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_q_representative_variability_bound_statement
    [Fintype α] {Cs : List (PaperChoiceRule α)}
    (hqueues :
      ∀ C ∈ Cs, ∃ q, paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C) :
    paper_definition_variability_at_most Cs.length
      (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_q_representative_variability_at_most_length hqueues

/--
A sequential composition of feasible q-representative queues is feasible,
q-acceptant at total capacity, 1-unstable, and has variability at most the
number of queues.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_q_representative_choice_properties_statement
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C =>
        paper_choice_function_feasible C ∧
          paper_definition_q_representativeness q C)
      qs Cs) :
    paper_choice_function_feasible (paper_definition_sequential_composition Cs) ∧
      paper_definition_q_acceptance qs.sum
        (paper_definition_sequential_composition Cs) ∧
        paper_definition_d_instability 1
          (paper_definition_sequential_composition Cs) ∧
          paper_definition_variability_at_most Cs.length
            (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_q_representative_choice_properties hqueues

/--
A nontrivial composition of `n` single-order queues realizes an exact
variability `m` with `1 ≤ m ≤ n`.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_sequential_q_representative_variability_range_statement
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C) qs Cs)
    (hqpos : 0 < qs.sum)
    (hqlt : qs.sum < Fintype.card α) :
    ∃ m, 1 ≤ m ∧ m ≤ Cs.length ∧
      paper_definition_variability_exactly m
        (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_q_representative_variability_range
    hqueues hqpos hqlt

/-- Abstract Screened/Open procedure used for the Proposition 2 source class. -/
abbrev paper_definition_screened_open_program_choice : PaperChoiceRule (Fin 2) :=
  paperScreenedOpenProgramChoice

/-- Abstract Screened/Open-with-DIA procedure used for the Proposition 2 source class. -/
abbrev paper_definition_screened_open_dia_program_choice : PaperChoiceRule (Fin 4) :=
  paperScreenedOpenDIAProgramChoice

/-- Abstract Educational Option procedure used for the Proposition 2 source class. -/
abbrev paper_definition_educational_option_program_choice : PaperChoiceRule (Fin 6) :=
  paperEducationalOptionProgramChoice

/-- Abstract Educational Option-with-DIA procedure used for the Proposition 2 source class. -/
abbrev paper_definition_educational_option_dia_program_choice : PaperChoiceRule (Fin 12) :=
  paperEducationalOptionDIAProgramChoice

/-- Source-facing Screened/Open procedure properties for Proposition 2. -/
theorem paper_screened_open_program_properties_statement :
    paper_choice_function_feasible paper_definition_screened_open_program_choice ∧
      paper_definition_q_acceptance 1 paper_definition_screened_open_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_program_choice ∧
      paper_definition_variability_exactly 1
        paper_definition_screened_open_program_choice := by
  exact paper_screened_open_program_properties

/-- Source-facing Screened/Open-with-DIA procedure properties for Proposition 2. -/
theorem paper_screened_open_dia_program_properties_statement :
    paper_choice_function_feasible paper_definition_screened_open_dia_program_choice ∧
      paper_definition_q_acceptance 2 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_variability_exactly 2
        paper_definition_screened_open_dia_program_choice := by
  exact paper_screened_open_dia_program_properties

/-- Source-facing Educational Option procedure properties for Proposition 2. -/
theorem paper_educational_option_program_properties_statement :
    paper_choice_function_feasible paper_definition_educational_option_program_choice ∧
      paper_definition_q_acceptance 3 paper_definition_educational_option_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_program_choice ∧
      paper_definition_variability_exactly 3
        paper_definition_educational_option_program_choice := by
  exact paper_educational_option_program_properties

/-- Source-facing Educational Option-with-DIA procedure properties for Proposition 2. -/
theorem paper_educational_option_dia_program_properties_statement :
    paper_choice_function_feasible paper_definition_educational_option_dia_program_choice ∧
      paper_definition_q_acceptance 6 paper_definition_educational_option_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_dia_program_choice ∧
      paper_definition_variability_exactly 6
        paper_definition_educational_option_dia_program_choice := by
  exact paper_educational_option_dia_program_properties

/-- Source-facing aggregate for the four Proposition 2 queue procedures. -/
theorem paper_program_classes_one_instability_statement :
    paper_definition_d_instability 1 paper_definition_screened_open_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_program_choice ∧
      paper_definition_d_instability 1
        paper_definition_educational_option_dia_program_choice := by
  exact paper_program_classes_one_instability

/--
If each applicant pool is assigned feasibly, the induced assignment choice rule
is feasible.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_selector_feasible_choice_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, paper_definition_lap_assignment_feasible X (select X)) :
    paper_choice_function_feasible
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_feasible_choice hfeas

/--
If each selected assignment is feasible and capacity-filling, the induced
choice rule is q-acceptant with capacity equal to the number of slots.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_selector_q_acceptant_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, paper_definition_lap_assignment_feasible X (select X))
    (hfill : ∀ X, paper_definition_lap_capacity_filling X (select X)) :
    paper_definition_q_acceptance (Fintype.card σ)
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_q_acceptant hfeas hfill

/--
Linear assignment instability: if each applicant pool is assigned by a unique
global optimum of the finite linear assignment objective, then the induced
choice rule is 1-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_one_instability_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ}
    (hwell : LAP.Assignment.WellPosedObjective w) :
    paper_definition_d_instability 1
      (paperLAPChoiceRule w hwell) := by
  exact paper_lap_well_posed_choice_one_instability hwell

/--
Conditional LAP 1-instability bridge: if the selected unique global optima
satisfy the single-addition exchange-preservation certificate, then the induced
choice rule is 1-unstable.
-/
theorem paper_lap_assignment_one_instability_from_exchange_preservation_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hpreserve : LAP.Assignment.SingleAddOldChosenPreservation w select) :
    paper_definition_d_instability 1
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_one_instability_of_exchange_preservation
    hselect hpreserve

/--
Lower-level conditional LAP 1-instability bridge: the matching exchange-repair
theorem implies the exchange-preservation certificate and hence 1-instability.
This proof-support row is kept auxiliary now that the unconditional unique-
global-optimum theorem is proved.
-/
theorem paper_lap_assignment_one_instability_from_exchange_repair_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hrepair : LAP.Assignment.SingleAddExchangeRepair w select) :
    paper_definition_d_instability 1
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_one_instability_of_exchange_repair
    hselect hrepair

/--
A finite-slot assignment chooses no more applicants than there are slots.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_chosen_set_card_le_slots_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : paper_definition_lap_assignment (α := α) σ) :
    (paper_definition_lap_chosen_set A).card ≤ Fintype.card σ := by
  exact paper_lap_chosen_set_card_le_slots A

/--
The borderline set of an assignment-induced choice rule is bounded by the
number of finite assignment slots.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_borderline_card_le_slots_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → paper_definition_lap_assignment (α := α) σ)
    (X : Finset α) :
    (paper_definition_borderline_set
      (paper_definition_lap_choice_rule (α := α) select) X).card ≤
        Fintype.card σ := by
  exact paper_lap_assignment_selector_borderline_card_le_slots select X

/--
An assignment-induced choice rule has variability bounded by the number of
finite assignment slots.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_variability_at_most_slots_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → paper_definition_lap_assignment (α := α) σ) :
    paper_definition_variability_at_most (Fintype.card σ)
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_variability_at_most_slots select

/--
If a unique-global-optimum finite LAP has one common strict order across all
slots, then its assignment-induced choice rule has variability at most one.
-/
theorem paper_lap_assignment_common_order_variability_at_most_one_statement
    [Fintype α] [LinearOrder α]
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → paper_definition_lap_assignment (α := α) σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (horder : ∀ s a b, a < b ↔ w b s < w a s) :
    paper_definition_variability_at_most 1
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact
    paper_lap_assignment_selector_variability_at_most_one_of_common_slot_order
      hselect horder

/--
LAP distinct-ordering counting bridge: if the old assigned slot class
identifies every borderline applicant injectively, the assignment-induced
choice rule has variability bounded by the number of supplied slot-order
classes.
-/
theorem paper_lap_assignment_slot_order_class_variability_statement
    [Fintype α] {σ κ : Type*} [DecidableEq σ] [Fintype σ] [DecidableEq κ]
    {select : Finset α → paper_definition_lap_assignment (α := α) σ}
    {classOf : σ → κ}
    (hinj :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ paper_definition_borderline_set
          (paper_definition_lap_choice_rule (α := α) select) X →
        z ∈ paper_definition_borderline_set
          (paper_definition_lap_choice_rule (α := α) select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        classOf sy = classOf sz →
        y = z) :
    paper_definition_variability_at_most
      ((Finset.univ : Finset σ).image classOf).card
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_variability_at_most_slot_order_classes
    hinj

/--
Paper-shaped LAP distinct-ordering bridge: if the supplied slot classifier only
groups slots with the same induced order, and same-order old slots cannot
carry two distinct borderline applicants, then variability is bounded by the
number of supplied slot-order classes.
-/
theorem paper_lap_assignment_slot_order_class_variability_from_same_order_kernel_statement
    [Fintype α] {σ κ : Type*} [DecidableEq σ] [Fintype σ] [DecidableEq κ]
    {w : α → σ → ℝ}
    {select : Finset α → paper_definition_lap_assignment (α := α) σ}
    {classOf : σ → κ}
    (hclass : ∀ {s t : σ}, classOf s = classOf t →
      LAP.Assignment.SameSlotOrder w s t)
    (hkernel :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ paper_definition_borderline_set
          (paper_definition_lap_choice_rule (α := α) select) X →
        z ∈ paper_definition_borderline_set
          (paper_definition_lap_choice_rule (α := α) select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        LAP.Assignment.SameSlotOrder w sy sz →
        y = z) :
    paper_definition_variability_at_most
      ((Finset.univ : Finset σ).image classOf).card
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact
    paper_lap_assignment_selector_variability_at_most_slot_order_classes_of_same_order_kernel
      hclass hkernel

/--
LAP distinct-ordering variability theorem: if a finite linear-assignment
selector returns unique global optima and every slot has no applicant-weight
ties, variability is bounded by the canonical number of distinct slot-induced
applicant orders.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ}
    (hwell : LAP.Assignment.WellPosedObjective w)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s) :
    paper_definition_variability_at_most
      (LAP.Assignment.distinctSlotOrderCount w)
      (paperLAPChoiceRule w hwell) := by
  exact
    paper_lap_well_posed_choice_variability_at_most_distinct_slot_orders
      hwell hnoTies

/--
Global objective optimality implies the local no-profitable-one-slot-swap
condition used by the LAP ordering lemma.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_no_profitable_one_slot_swap_of_objective_optimal_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ}
    {A : paper_definition_lap_assignment (α := α) σ}
    (hopt : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A) :
    paper_definition_lap_no_profitable_one_slot_swap X w A := by
  exact paper_lap_no_profitable_one_slot_swap_of_objective_optimal
    hopt hfill

/--
In a locally optimal finite linear assignment, the applicant assigned to a slot
is at least as high in that slot's weight order as any rejected applicant.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_ordering_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : paper_definition_lap_rejected X A x) :
    paper_definition_lap_slot_at_least w s y x := by
  exact paper_lap_slot_ordering
    (paper_lap_no_profitable_one_slot_swap_of_objective_optimal hobjective hfill)
    hassign hslot hrej

/--
In a locally optimal finite linear assignment, any offered applicant who
strictly outranks a slot occupant in that slot's weight order is assigned.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_strictly_higher_slot_applicant_assigned_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hxX : x ∈ X)
    (hbelow : paper_definition_lap_slot_below w s y x) :
    paper_definition_lap_assigned A x := by
  exact paper_lap_strictly_higher_slot_applicant_assigned
    (paper_lap_no_profitable_one_slot_swap_of_objective_optimal hobjective hfill)
    hassign hslot hxX hbelow

/--
In a feasible locally optimal finite linear assignment, no rejected applicant
strictly outranks the applicant assigned to any occupied slot.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_lap_no_rejected_slot_below_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A) :
    ¬ ∃ s y x, A.matchSlot s = some y ∧
      paper_definition_lap_rejected X A x ∧
        paper_definition_lap_slot_below w s y x := by
  exact paper_lap_no_rejected_slot_below
    (paper_lap_no_profitable_one_slot_swap_of_objective_optimal hobjective hfill)
    hassign

/--
Capacity-constrained choice functions are not zero-unstable on nontrivial
universes: if some applicant pool has more applicants than the positive capacity
`q`, a feasible q-acceptant choice function cannot be zero-unstable.
Source status: paper-facing source definition/result; row-local LLM validation pending.
-/
theorem paper_no_zero_instability_under_capacity_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    ¬ paper_definition_zero_instability C := by
  exact paper_no_zero_unstable_of_q_acceptant_nontrivial
    hfeasible haccept hqpos hUcard

end DGD26AdmissionsPredictability
