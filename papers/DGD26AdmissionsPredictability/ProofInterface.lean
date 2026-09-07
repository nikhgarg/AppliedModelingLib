import DGD26AdmissionsPredictability.PaperInterface

import DGD26AdmissionsPredictability.ProofBridge



namespace DGD26AdmissionsPredictability

namespace PaperInterface

open AppliedModelingLib.FiniteChoice
variable {α : Type*} [DecidableEq α]

theorem paper_choice_function_model_definition_statement
    (C : PaperChoiceRule α) :
    paper_choice_function_model_definition_statementSpec (C := C) := by
  rfl

theorem paper_definition_choice_label
    (C : PaperChoiceRule α) (X : Finset α) (x : α) (hx : x ∈ X) :
    paper_definition_choice_labelSpec (C := C) (X := X) (x := x) hx := by
  rfl

theorem paper_ml_representation_definition_statement
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α)  : paper_ml_representation_definition_statementSpec (predicts := predicts) (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_ml_representation_definition_statement (predicts := predicts) (C := C)

theorem paper_q_acceptance_definition_statement
    (q : ℕ) (C : PaperChoiceRule α)  : paper_q_acceptance_definition_statementSpec (q := q) (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_q_acceptance_definition_statement (q := q) (C := C)

-- The source-facing `Spec` does not use decidable equality.  Keep this
-- direct definitional bridge parameter-for-parameter identical to it.
omit [DecidableEq α] in
theorem paper_total_order_definition_statement
    (r : α → α → Prop)  : paper_total_order_definition_statementSpec (r := r) := by
  rfl

theorem paper_q_representativeness_definition_statement
    (q : ℕ) (C : PaperChoiceRule α)  : paper_q_representativeness_definition_statementSpec (q := q) (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_q_representativeness_definition_statement (q := q) (C := C)

theorem paper_definition_choice_distance
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) (hsubset : X₁ ⊆ X₂) :
    paper_definition_choice_distanceSpec (C := C) (X₁ := X₁) (X₂ := X₂)
      hsubset := by
  rfl

theorem paper_d_instability_definition_statement
    (d : ℕ) (C : PaperChoiceRule α)  : paper_d_instability_definition_statementSpec (d := d) (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_d_instability_definition_statement (d := d) (C := C)

theorem paper_tight_d_instability_definition_statement
    (d : ℕ) (C : PaperChoiceRule α)  : paper_tight_d_instability_definition_statementSpec (d := d) (C := C) := by
  intro _
  exact DGD26AdmissionsPredictability.ProofBridge.paper_tight_d_instability_definition_statement (d := d) (C := C)

theorem paper_definition_borderline_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) :
    paper_definition_borderline_setSpec (C := C) (X := X) := by
  rfl

theorem paper_variability_exactly_definition_statement [Fintype α]
    {q : ℕ} (m : ℕ) (C : PaperChoiceRule α)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C) :
    paper_variability_exactly_definition_statementSpec (q := q) (m := m)
      (C := C) hfeasible haccept hunstable := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_variability_exactly_definition_statement (m := m) (C := C)

theorem paper_fixed_threshold_formula_statement
    (score : α → ℝ) (threshold : ℝ)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1)
    (X : Finset α) (x : α)  : paper_fixed_threshold_formula_statementSpec (score := score) (threshold := threshold) (hscore := hscore) (X := X) (x := x) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_fixed_threshold_formula_statement (score := score) (threshold := threshold) (hscore := hscore) (X := X) (x := x)

theorem paper_ml_fixed_threshold_representation_zero_unstable_statement
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold) C)  : paper_ml_fixed_threshold_representation_zero_unstable_statementSpec (C := C) (score := score) (threshold := threshold) (hscore := hscore) (hfeasible := hfeasible) (hrep := hrep) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_ml_fixed_threshold_representation_zero_unstable_statement (C := C) (score := score) (threshold := threshold) (hfeasible := hfeasible) (hrep := hrep)

theorem paper_rank_threshold_formula_statement
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q) (X : Finset α) (hqcard : q ≤ X.card)  : paper_rank_threshold_formula_statementSpec (q := q) (operationalScore := operationalScore) (hinjective := hinjective) (hqpos := hqpos) (X := X) (hqcard := hqcard) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_rank_threshold_formula_statement (q := q) (score := operationalScore) (hinjective := hinjective) (hqpos := hqpos) (X := X) (hqcard := hqcard)

theorem paper_ml_rank_threshold_representation_instability_bound_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q operationalScore hinjective) C)  : paper_ml_rank_threshold_representation_instability_bound_statementSpec (C := C) (q := q) (operationalScore := operationalScore) (hinjective := hinjective) (hqpos := hqpos) (hfeasible := hfeasible) (hrep := hrep) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_ml_rank_threshold_representation_instability_bound_statement (C := C) (q := q) (score := operationalScore) (hinjective := hinjective) (hfeasible := hfeasible) (hrep := hrep)

theorem paper_ml_rank_threshold_representation_variability_bound_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q operationalScore hinjective) C)  : paper_ml_rank_threshold_representation_variability_bound_statementSpec (C := C) (q := q) (operationalScore := operationalScore) (hinjective := hinjective) (hqpos := hqpos) (hfeasible := hfeasible) (hrep := hrep) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_ml_rank_threshold_representation_variability_bound_statement (C := C) (q := q) (score := operationalScore) (hinjective := hinjective) (hfeasible := hfeasible) (hrep := hrep)

theorem paper_ml_rank_threshold_can_represent_exact_one_statement
    (q : ℕ) (hqpos : 0 < q)  : paper_ml_rank_threshold_can_represent_exact_one_statementSpec (q := q) (hqpos := hqpos) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_ml_rank_threshold_can_represent_exact_one_statement (q := q) (hqpos := hqpos)

theorem paper_q_representative_forward_exact_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : paper_q_representative_forward_exact_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (hrep := hrep) (hqpos := hqpos) (hqlt := hqlt) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_q_representative_forward_exact_statement (q := q) (C := C) (hfeasible := hfeasible) (hrep := hrep) (hqpos := hqpos) (hqlt := hqlt)

theorem paper_q_representative_converse_exact_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : paper_q_representative_converse_exact_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hvar := hvar) (hqpos := hqpos) (hqlt := hqlt) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_q_representative_converse_exact_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hvar := hvar) (hqpos := hqpos) (hqlt := hqlt)

theorem paper_variability_one_iff_single_order_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : paper_variability_one_iff_single_order_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hqpos := hqpos) (hqlt := hqlt) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_variability_one_iff_single_order_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hqpos := hqpos) (hqlt := hqlt)

theorem paper_substitutability_definition_statement
    (C : PaperChoiceRule α)  : paper_substitutability_definition_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_substitutability_definition_statement (C := C)

theorem paper_no_zero_instability_under_capacity_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card)  : paper_no_zero_instability_under_capacity_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hqpos := hqpos) (U := U) (hUcard := hUcard) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_no_zero_instability_under_capacity_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hqpos := hqpos) (U := U) (hUcard := hUcard)

theorem paper_independent_zero_unstable_corollary_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    paper_independent_zero_unstable_corollary_statementSpec hfeasible haccept hqpos hUcard := by
  exact ⟨(DGD26AdmissionsPredictability.ProofBridge.paper_independent_zero_unstable_statement C hfeasible).symm,
    DGD26AdmissionsPredictability.ProofBridge.paper_no_zero_instability_under_capacity_statement hfeasible haccept hqpos hUcard⟩

theorem paper_substitutability_one_instability_equivalence_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    paper_substitutability_one_instability_equivalence_statementSpec
      (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept)
      hqpos hUcard := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_substitutability_one_instability_equivalence_statement
    (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) hqpos hUcard

theorem paper_qacceptant_substitutable_iff_one_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    paper_qacceptant_substitutable_iff_one_statementSpec
      (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept)
      hqpos hUcard := by
  exact (DGD26AdmissionsPredictability.ProofBridge.paper_substitutability_one_instability_equivalence_statement
    (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept)
    hqpos hUcard).symm

theorem paper_theorem1_tight_all_d_statement
    (q d : ℕ) : paper_theorem1_tight_all_d_statementSpec q d := by
  intro hdpos hdle
  rcases Nat.even_or_odd d with heven | hodd
  · rcases heven with ⟨n, hn⟩
    subst d
    have hnpos : 0 < n := by omega
    have hnq : n ≤ q := by omega
    refine ⟨Fin (q + n + 1), inferInstance, paddedEvenChoice q n, ?_⟩
    simpa [two_mul] using DGD26AdmissionsPredictability.ProofBridge.paper_padded_even_tight_instability_family_statement hnpos hnq
  · rcases hodd with ⟨n, hn⟩
    subst d
    have hnq : n + 1 ≤ q := by omega
    refine ⟨Fin (q + (n + 1) + 1), inferInstance, paddedOddChoice q (n + 1), ?_⟩
    convert DGD26AdmissionsPredictability.ProofBridge.paper_padded_odd_tight_instability_family_statement (q := q) (n := n + 1) (by omega) hnq using 1

theorem paper_definition_sequential_composition
    (Cs : List (PaperChoiceRule α)) :
    paper_definition_sequential_compositionSpec (Cs := Cs) := by
  induction Cs with
  | nil => rfl
  | cons C Cs ih =>
      funext X
      simp only [paper_sequential_composition, sequentialComposition, sequentialCompositionSource]
      exact congrArg (fun Y => C X ∪ Y) (congrFun ih (X \ C X))

theorem paper_sequential_q_representative_variability_range_statement
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C) qs Cs)
    (hqpos : 0 < qs.sum)
    (hqlt : qs.sum < Fintype.card α)  : paper_sequential_q_representative_variability_range_statementSpec (qs := qs) (Cs := Cs) (hqueues := hqueues) (hqpos := hqpos) (hqlt := hqlt) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_sequential_q_representative_variability_range_statement (qs := qs) (Cs := Cs) (hqueues := hqueues) (hqpos := hqpos) (hqlt := hqlt)

theorem paper_screened_open_variability_one_statement  : paper_screened_open_variability_one_statementSpec := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_screened_open_variability_one_statement

theorem paper_screened_open_dia_variability_two_statement  : paper_screened_open_dia_variability_two_statementSpec := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_screened_open_dia_variability_two_statement

theorem paper_educational_option_variability_three_statement  : paper_educational_option_variability_three_statementSpec := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_educational_option_variability_three_statement

theorem paper_educational_option_dia_variability_six_statement  : paper_educational_option_dia_variability_six_statementSpec := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_educational_option_dia_variability_six_statement

theorem paper_program_classes_one_instability_statement  : paper_program_classes_one_instability_statementSpec := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_program_classes_one_instability_statement

theorem paper_monotonicity_definition_statement
    (C : PaperChoiceRule α)  : paper_monotonicity_definition_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_monotonicity_definition_statement (C := C)

theorem paper_consistency_definition_statement
    (C : PaperChoiceRule α)  : paper_consistency_definition_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_consistency_definition_statement (C := C)

theorem paper_monotonicity_q_acceptance_incompatible_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hmono : paper_definition_monotonicity C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card)  : paper_monotonicity_q_acceptance_incompatible_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (hmono := hmono) (haccept := haccept) (hqpos := hqpos) (U := U) (hUcard := hUcard) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_monotonicity_q_acceptance_incompatible_statement (q := q) (C := C) (hfeasible := hfeasible) (hmono := hmono) (haccept := haccept) (hqpos := hqpos) (U := U) (hUcard := hUcard)

theorem paper_non_substitutable_single_add_statement
    (C : PaperChoiceRule α)
    (hnot : ¬ paper_definition_substitutability C)  : paper_non_substitutable_single_add_statementSpec (C := C) (hnot := hnot) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_non_substitutable_single_add_statement (C := C) (hnot := hnot)

theorem paper_substitutability_term_statement
    (C : PaperChoiceRule α)  : paper_substitutability_term_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_substitutability_term_statement (C := C)

theorem paper_monotonicity_term_statement
    (C : PaperChoiceRule α)  : paper_monotonicity_term_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_monotonicity_term_statement (C := C)

theorem paper_choice_distance_triangle_statement
    (C : PaperChoiceRule α) {X₁ X₂ X₃ : Finset α}
    (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃)  : paper_choice_distance_triangle_statementSpec (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (h₁₂ := h₁₂) (h₂₃ := h₂₃) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_choice_distance_triangle_statement (C := C) (X₁ := X₁) (X₂ := X₂) (X₃ := X₃) (h₁₂ := h₁₂) (h₂₃ := h₂₃)

theorem paper_zero_instability_definition_statement
    (C : PaperChoiceRule α)  : paper_zero_instability_definition_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_zero_instability_definition_statement (C := C)

theorem paper_zero_distance_statement
    (C : PaperChoiceRule α)  : paper_zero_distance_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_zero_distance_statement (C := C)

theorem paper_independence_definition_statement
    (C : PaperChoiceRule α)  : paper_independence_definition_statementSpec (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_independence_definition_statement (C := C)

theorem paper_independent_substitutable_monotonic_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C)  : paper_independent_substitutable_monotonic_statementSpec (C := C) (hfeasible := hfeasible) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_independent_substitutable_monotonic_statement (C := C) (hfeasible := hfeasible)

theorem paper_independent_zero_unstable_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C)  : paper_independent_zero_unstable_statementSpec (C := C) (hfeasible := hfeasible) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_independent_zero_unstable_statement (C := C) (hfeasible := hfeasible)

theorem paper_q_acceptant_substitutable_consistent_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C) :
    paper_q_acceptant_substitutable_consistent_statementSpec (q := q) (C := C)
      hfeasible haccept hsub := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_q_acceptant_substitutable_consistent_statement
    (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hsub := hsub)

theorem paper_calculating_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hx : x ∉ X)  : paper_calculating_instability_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (X := X) (x := x) (hcard := hcard) (hx := hx) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_calculating_instability_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (X := X) (x := x) (hcard := hcard) (hx := hx)

theorem paper_even_distance_iff_inconsistent_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)  : paper_even_distance_iff_inconsistent_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_even_distance_iff_inconsistent_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept)

theorem paper_no_consistent_positive_tightly_even_statement
    {q k : ℕ} {C : PaperChoiceRule α}
    (hk : 0 < k)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C)  : paper_no_consistent_positive_tightly_even_statementSpec (q := q) (k := k) (C := C) (hk := hk) (hfeasible := hfeasible) (haccept := haccept) (hcons := hcons) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_no_consistent_positive_tightly_even_statement (q := q) (k := k) (C := C) (hk := hk) (hfeasible := hfeasible) (haccept := haccept) (hcons := hcons)

theorem paper_definition_waitlisted_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) :
    paper_definition_waitlisted_setSpec (C := C) (X := X) := by
  rfl

theorem paper_general_variability_exactly_definition_statement [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α)  : paper_general_variability_exactly_definition_statementSpec (m := m) (C := C) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_general_variability_exactly_definition_statement (m := m) (C := C)

theorem paper_append_remove_variability_exact_equivalence_statement
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hcard : 2 * q ≤ Fintype.card α) :
    paper_append_remove_variability_exact_equivalence_statementSpec (m := m)
      (q := q) (C := C) hfeasible haccept hunstable hcard := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_append_remove_variability_exact_equivalence_statement
    (m := m) (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept)
    (hunstable := hunstable) (hcard := hcard)

theorem paper_corrected_consistency_of_removable_sets_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂)  : paper_corrected_consistency_of_removable_sets_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hsub := hsub) (X₁ := X₁) (X₂ := X₂) (hchoice := hchoice) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_corrected_consistency_of_removable_sets_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hsub := hsub) (X₁ := X₁) (X₂ := X₂) (hchoice := hchoice)

theorem paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X)  : paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statementSpec (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hvar := hvar) (X := X) (x := x) (hx := hx) (hchange := hchange) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement (q := q) (C := C) (hfeasible := hfeasible) (haccept := haccept) (hunstable := hunstable) (hvar := hvar.1) (X := X) (x := x) (hx := hx) (hchange := hchange)

theorem paper_sequential_composition_substitutable_statement
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_choice_function_feasible C)
    (hsub : ∀ C ∈ Cs, paper_definition_substitutability C)  : paper_sequential_composition_substitutable_statementSpec (Cs := Cs) (hfeasible := hfeasible) (hsub := hsub) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_sequential_composition_substitutable_statement (Cs := Cs) (hfeasible := hfeasible) (hsub := hsub)

theorem paper_sequential_additive_variability_bound_statement
    [Fintype α] {qs ms : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hcapacity : List.Forall₂
      (fun q C =>
        paper_choice_function_feasible C ∧
          paper_definition_q_acceptance q C ∧
            paper_definition_d_instability 1 C)
      qs Cs)
    (hvariability : List.Forall₂
      (fun m C => paper_definition_variability_exactly m C)
      ms Cs)  : paper_sequential_additive_variability_bound_statementSpec (qs := qs) (ms := ms) (Cs := Cs) (hcapacity := hcapacity) (hvariability := hvariability) := by
  have hvariabilityAtMost : List.Forall₂
      (fun m C => paper_definition_variability_at_most m C) ms Cs := by
    clear hcapacity
    induction hvariability with
    | nil => exact .nil
    | cons h _ ih => exact .cons h.1 ih
  exact DGD26AdmissionsPredictability.ProofBridge.paper_sequential_additive_variability_bound_statement
    (qs := qs) (ms := ms) (Cs := Cs) hcapacity hvariabilityAtMost

-- These definition bridges deliberately omit the ambient applicant equality
-- instance: the source-facing Specs quantify only the data they use.
omit [DecidableEq α] in
theorem paper_lap_slot_below_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (x y : α)  : paper_lap_slot_below_definition_statementSpec (σ := σ) (w := w) (s := s) (x := x) (y := y) := by
  rfl

omit [DecidableEq α] in
theorem paper_lap_same_slot_order_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s t : σ) :
    paper_lap_same_slot_order_definition_statementSpec (w := w) (s := s) (t := t) := by
  rfl

omit [DecidableEq α] in
theorem paper_lap_model_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) :
    paper_lap_model_definition_statementSpec (X := X) (w := w) (A := A) := by
  rfl

theorem paper_lap_assignment_choice_formula_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) (X : Finset α) (x : α)  : paper_lap_assignment_choice_formula_statementSpec (σ := σ) (select := select) (X := X) (x := x) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_lap_assignment_choice_formula_statement (σ := σ) (select := select) (X := X) (x := x)

theorem paper_lap_assigned_strictly_outranks_rejected_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : LAP.Assignment.Rejected X A x)
    (hnoTies : LAP.Assignment.SlotNoTies w s)  : paper_lap_assigned_strictly_outranks_rejected_statementSpec (σ := σ) (X := X) (w := w) (A := A) (hobjective := hobjective) (hfill := hfill) (hassign := hassign) (s := s) (y := y) (x := x) (hslot := hslot) (hrej := hrej) (hnoTies := hnoTies) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_lap_assigned_strictly_outranks_rejected_statement (σ := σ) (X := X) (w := w) (A := A) (hobjective := hobjective) (hfill := hfill) (hassign := hassign) (s := s) (y := y) (x := x) (hslot := hslot) (hrej := hrej) (hnoTies := hnoTies)

theorem paper_lap_strictly_higher_slot_applicant_assigned_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hxX : x ∈ X)
    (hbelow : paper_definition_lap_slot_below w s y x)  : paper_lap_strictly_higher_slot_applicant_assigned_statementSpec (σ := σ) (X := X) (w := w) (A := A) (hobjective := hobjective) (hfill := hfill) (hassign := hassign) (s := s) (y := y) (x := x) (hslot := hslot) (hxX := hxX) (hbelow := hbelow) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_lap_strictly_higher_slot_applicant_assigned_statement (σ := σ) (X := X) (w := w) (A := A) (hobjective := hobjective) (hfill := hfill) (hassign := hassign) (s := s) (y := y) (x := x) (hslot := hslot) (hxX := hxX) (hbelow := hbelow)

theorem paper_lap_assignment_one_instability_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {operationalWeight : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧ LAP.Assignment.CapacityFilling X A ∧
        LAP.Assignment.ObjectiveOptimal X operationalWeight A ∧ ∀ B : LAP.Assignment α σ,
          LAP.Assignment.Feasible X B → LAP.Assignment.CapacityFilling X B →
            LAP.Assignment.ObjectiveOptimal X operationalWeight B → B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies operationalWeight s)  : paper_lap_assignment_one_instability_statementSpec (σ := σ) (operationalWeight := operationalWeight) (hwell := hwell) (hnoTies := hnoTies) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_lap_assignment_one_instability_statement (σ := σ) (w := operationalWeight) (hwell := hwell) (hnoTies := hnoTies)

theorem paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {operationalWeight : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧ LAP.Assignment.CapacityFilling X A ∧
        LAP.Assignment.ObjectiveOptimal X operationalWeight A ∧ ∀ B : LAP.Assignment α σ,
          LAP.Assignment.Feasible X B → LAP.Assignment.CapacityFilling X B →
            LAP.Assignment.ObjectiveOptimal X operationalWeight B → B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies operationalWeight s)  : paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statementSpec (σ := σ) (operationalWeight := operationalWeight) (hwell := hwell) (hnoTies := hnoTies) := by
  exact DGD26AdmissionsPredictability.ProofBridge.paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement (σ := σ) (w := operationalWeight) (hwell := hwell) (hnoTies := hnoTies)

end PaperInterface
end DGD26AdmissionsPredictability
