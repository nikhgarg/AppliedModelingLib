import DGD26AdmissionsPredictability.AuditInterface

/-!
# Proof Bridge: Capacity Constraints Make Admissions Processes Less Predictable

This module collects already-checked paper-model endpoints used by the
proof interface. The semantic review surface is `PaperInterface.lean`.
-/

namespace DGD26AdmissionsPredictability
namespace ProofBridge

open AppliedModelingLib.FiniteChoice

variable {α : Type*} [DecidableEq α]

/-- Finite choice-function carrier used by the paper model. -/
abbrev paper_definition_choice_function := PaperChoiceRule α

/-- Convention that choices lie in the offered pool. -/
abbrev paper_definition_choice_function_feasible (C : PaperChoiceRule α) : Prop :=
  paper_feasible C

/-- Complete feasible finite choice-function model. -/
abbrev paper_definition_choice_function_model (C : PaperChoiceRule α) : Prop :=
  paper_feasible C

/-- Source status: audited feasible-subset definition formula. -/
theorem paper_choice_function_model_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_choice_function_model C ↔
      ∀ X, C X ⊆ X := by
  rfl

/-- Source status: audited binary choice-label formula `C(X)_i`. -/
abbrev paper_definition_choice_label
    (C : PaperChoiceRule α) (X : Finset α) (x : α) : ℕ :=
  paperChoiceLabel C X x

/-- Source status: audited all-pools ML representation definition. -/
abbrev paper_definition_ml_representation
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α) : Prop :=
  paperRepresentsChoice predicts C

/-- Source status: audited all-pools ML representation formula. -/
theorem paper_ml_representation_definition_statement
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α) :
    paper_definition_ml_representation predicts C ↔
      ∀ X x, x ∈ X → (predicts X x ↔ x ∈ C X) := by
  rfl

/-- Source status: audited fixed-threshold classifier formula. -/
abbrev paper_definition_fixed_threshold_predictor
    (score : α → ℝ) (threshold : ℝ) : PaperPoolPredictor α :=
  paperFixedThresholdPredictor score threshold

/-- Source status: audited cohort-dependent rank-threshold formula. -/
noncomputable abbrev paper_definition_rank_threshold_predictor
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    PaperPoolPredictor α :=
  paperRankThresholdPredictor q score hinjective

/-- Source status: audited PaperInterface row `paper_definition_q_acceptance`. -/
abbrev paper_definition_q_acceptance (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_q_acceptant q C

/-- Source status: audited q-acceptance definition formula. -/
theorem paper_q_acceptance_definition_statement
    (q : ℕ) (C : PaperChoiceRule α) :
    paper_definition_q_acceptance q C ↔
      ∀ X, (C X).card = min q X.card := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_total_order`. -/
abbrev paper_definition_total_order (r : α → α → Prop) : Prop :=
  paper_total_order r

/-- Source status: audited strict-total-order definition on distinct pairs. -/
theorem paper_total_order_definition_statement
    (r : α → α → Prop) :
    paper_definition_total_order r ↔
      (∀ x, ¬ r x x) ∧
        (∀ {x y z}, r x y → r y z → r x z) ∧
          (∀ {x y}, x ≠ y → r x y ∨ r y x) := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_q_representativeness`. -/
abbrev paper_definition_q_representativeness
    (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_q_representative q C

/-- Source status: audited one-total-order q-representativeness definition. -/
theorem paper_q_representativeness_definition_statement
    (q : ℕ) (C : PaperChoiceRule α) :
    paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C ↔
      paper_choice_function_feasible C ∧
        ∃ r : α → α → Prop,
          paper_definition_total_order r ∧
            paper_choice_function_feasible C ∧
              paper_definition_q_acceptance q C ∧
                ∀ {X x y}, x ∈ C X → y ∈ X → y ∉ C X → r x y := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_choice_distance`. -/
abbrev paper_definition_choice_distance
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  paper_choiceDistance C X₁ X₂

/-- Source status: audited PaperInterface row `paper_choice_distance_formula`. -/
theorem paper_choice_distance_formula
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) :
    choiceDistance C X₁ X₂ =
      ((X₁ ∩ C X₂) \ C X₁).card + (C X₁ \ C X₂).card := by
  simpa [paper_choiceDistance] using paper_choiceDistance_eq_library C X₁ X₂

/-- Source status: audited PaperInterface row `paper_definition_d_instability`. -/
abbrev paper_definition_d_instability (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_d_unstable d C

/-- Source status: audited one-insertion d-instability definition formula. -/
theorem paper_d_instability_definition_statement
    (d : ℕ) (C : PaperChoiceRule α) :
    paper_definition_d_instability d C ↔
      ∀ X x, x ∉ X → choiceDistance C X (insert x X) ≤ d := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_tight_d_instability`. -/
abbrev paper_definition_tight_d_instability
    (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_tightly_d_unstable d C

/-- Source status: audited tight d-instability definition formula. -/
theorem paper_tight_d_instability_definition_statement
    (d : ℕ) (C : PaperChoiceRule α) :
    paper_definition_tight_d_instability d C ↔
      paper_definition_d_instability d C ∧
        ∀ k, k < d → ¬ paper_definition_d_instability k C := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_borderline_set`. -/
abbrev paper_definition_borderline_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  paper_borderline_set C X

/-- Source status: audited PaperInterface row `paper_definition_variability_at_most`. -/
abbrev paper_definition_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_variability_at_most m C

/-- Source status: audited variability upper-bound definition formula. -/
theorem paper_variability_at_most_definition_statement [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) :
    paper_definition_variability_at_most m C ↔
      ∀ X, (paper_definition_borderline_set C X).card ≤ m := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_variability_exactly`. -/
abbrev paper_definition_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_variability_exactly m C

/-- Source status: audited exact-variability definition formula. -/
theorem paper_variability_exactly_definition_statement [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) :
    paper_definition_variability_exactly m C ↔
      (∀ X, (paper_definition_borderline_set C X).card ≤ m) ∧
        ∃ X, (paper_definition_borderline_set C X).card = m := by
  rfl

/-- Source status: audited choice-label equality row. -/
theorem paper_choice_label_formula_statement
    (C : PaperChoiceRule α) (X : Finset α) (x : α) :
    paper_definition_choice_label C X x = 1 ↔ x ∈ C X := by
  exact paperChoiceLabel_eq_one_iff C X x

/-- Source status: audited fixed-threshold displayed formula row. -/
theorem paper_fixed_threshold_formula_statement
    (score : α → ℝ) (threshold : ℝ)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1)
    (X : Finset α) (x : α) :
    x ∈ paperFixedThresholdChoice score threshold X ↔
      x ∈ X ∧ paper_definition_fixed_threshold_predictor
        score threshold X x := by
  exact paperFixedThresholdChoice_mem_iff score threshold X x

/-- Source status: audited fixed-threshold representation row. -/
theorem paper_fixed_threshold_represents_induced_choice_statement
    (score : α → ℝ) (threshold : ℝ) :
    paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold)
      (paperFixedThresholdChoice score threshold) := by
  exact paperFixedThresholdPredictor_represents score threshold

/-- Source status: audited PaperInterface row `paper_ml_independent_predictions_zero_unstable_statement`. -/
theorem paper_ml_independent_predictions_zero_unstable_statement
    (score : α → ℝ) (threshold : ℝ) :
    paper_definition_zero_instability
      (paperFixedThresholdChoice score threshold) := by
  exact paper_fixed_threshold_predictions_zero_unstable score threshold

/-- Source status: audited fixed-threshold representation consequence. -/
theorem paper_ml_fixed_threshold_representation_zero_unstable_statement
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold) C) :
    paper_definition_zero_instability C := by
  exact paper_fixed_threshold_representation_zero_unstable
    score threshold hfeasible hrep

/-- Source status: audited rank-threshold order-statistic formula. -/
theorem paper_rank_threshold_formula_statement
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hqpos : 0 < q) (X : Finset α) (hqcard : q ≤ X.card) :
    ∃ threshold : ℝ,
      threshold ∈ X.image score ∧
        (X.filter (fun x => threshold ≤ score x)).card = q ∧
          ∀ x ∈ X,
            (paper_definition_rank_threshold_predictor
                q score hinjective X x ↔ threshold ≤ score x) := by
  exact paperRankThresholdPredictor_order_statistic_formula
    q score hinjective hqpos X hqcard

/-- Source status: audited rank-threshold representation row. -/
theorem paper_rank_threshold_represents_induced_choice_statement
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective)
      (paperRankThresholdChoice q score hinjective) := by
  exact paperRankThresholdPredictor_represents q score hinjective

/-- Source status: audited PaperInterface row `paper_ml_rank_threshold_one_instability_variability_statement`. -/
theorem paper_ml_rank_threshold_one_instability_variability_statement
    [Fintype α] (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score) :
    paper_definition_d_instability 1
        (paperRankThresholdChoice q score hinjective) ∧
      paper_definition_variability_at_most 1
        (paperRankThresholdChoice q score hinjective) := by
  exact paper_score_rank_threshold_one_instability_and_variability
    q score hinjective

/-- Source status: audited represented rank-threshold bounds. -/
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

/-- Source status: audited represented rank-threshold instability bound. -/
theorem paper_ml_rank_threshold_representation_instability_bound_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective) C) :
    paper_definition_d_instability 1 C := by
  exact (paper_ml_rank_threshold_representation_bounds_statement
    q score hinjective hfeasible hrep).1

/-- Source status: audited represented rank-threshold variability bound. -/
theorem paper_ml_rank_threshold_representation_variability_bound_statement
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q score hinjective) C) :
    paper_definition_variability_at_most 1 C := by
  exact (paper_ml_rank_threshold_representation_bounds_statement
    q score hinjective hfeasible hrep).2

/-- Source status: audited nondegenerate exact-one ML representation row. -/
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

/-- Source status: audited represented nondegenerate rank-threshold exactness. -/
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

/-- Source status: audited existence of an exact-one rank-threshold model. -/
theorem paper_ml_rank_threshold_can_represent_exact_one_statement
    (q : ℕ) (hqpos : 0 < q) :
    ∃ (score : Fin (q + 1) → ℝ) (hinjective : Function.Injective score),
      paper_definition_tight_d_instability 1
          (paperRankThresholdChoice q score hinjective) ∧
        paper_definition_variability_exactly 1
          (paperRankThresholdChoice q score hinjective) := by
  exact paper_rank_threshold_can_represent_exact_one q hqpos

/-- Source status: audited PaperInterface row `paper_q_representative_characterization_statement`. -/
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

/-- Source status: audited source-corrected exact q-representative characterization. -/
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

/-- Source status: audited nondegenerate forward q-representative theorem. -/
theorem paper_q_representative_forward_exact_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_q_acceptance q C ∧
      paper_definition_d_instability 1 C ∧
        paper_definition_variability_exactly 1 C := by
  exact (paper_q_representative_exact_characterization_statement
    hfeasible hqpos hqlt).mp hrep

/-- Source status: audited nondegenerate converse q-representative theorem. -/
theorem paper_q_representative_converse_exact_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_q_representativeness q C := by
  exact (paper_q_representative_exact_characterization_statement
    hfeasible hqpos hqlt).mpr ⟨haccept, hunstable, hvar⟩

/-- Source status: audited exact variability-one iff single-order row. -/
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

/-- Source status: audited PaperInterface row `paper_q_representative_variability_exactly_one_statement`. -/
theorem paper_q_representative_variability_exactly_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_definition_variability_exactly 1 C := by
  exact paper_q_representative_variability_exactly_one_nontrivial
    (C := C) hfeasible hrep hqpos hqlt

/-- Source status: audited PaperInterface row `paper_definition_substitutability`. -/
abbrev paper_definition_substitutability (C : PaperChoiceRule α) : Prop :=
  paper_substitutable C

/-- Source status: audited substitutability definition formula. -/
theorem paper_substitutability_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_substitutability C ↔
      ∀ {X₁ X₂}, X₁ ⊆ X₂ → X₁ ∩ C X₂ ⊆ C X₁ := by
  rfl

/-- Source status: audited PaperInterface row `paper_no_zero_instability_under_capacity_statement`. -/
theorem paper_no_zero_instability_under_capacity_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    ¬ paper_definition_zero_instability C := by
  exact paper_no_zero_unstable_of_q_acceptant_nontrivial
    hfeasible haccept hqpos hUcard

/-- Source status: audited PaperInterface row `paper_substitutability_one_instability_equivalence_statement`. -/
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
    exact ⟨(DGD26AdmissionsPredictability.paper_substitutability_iff_one_instability_of_q_acceptant
        (C := C) hfeasible haccept).mp hsub,
      DGD26AdmissionsPredictability.paper_no_zero_unstable_of_q_acceptant_nontrivial
        hfeasible haccept hqpos hUcard⟩
  · rintro ⟨hone, _⟩
    exact (DGD26AdmissionsPredictability.paper_substitutability_iff_one_instability_of_q_acceptant
      (C := C) hfeasible haccept).mpr hone

/-- Source status: audited PaperInterface row `paper_q_acceptant_two_q_instability_bound_statement`. -/
theorem paper_q_acceptant_two_q_instability_bound_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (haccept : paper_definition_q_acceptance q C) :
    paper_definition_d_instability (2 * q) C := by
  exact paper_q_acceptant_two_q_instability_bound haccept

/-- Source status: audited PaperInterface row `paper_padded_even_tight_instability_family_statement`. -/
theorem paper_padded_even_tight_instability_family_statement
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_choice_function_feasible (paddedEvenChoice q n) ∧
      paper_definition_q_acceptance q (paddedEvenChoice q n) ∧
        paper_definition_tight_d_instability (2 * n) (paddedEvenChoice q n) := by
  exact paper_padded_even_tight_instability_family hnpos hnq

/-- Source status: audited PaperInterface row `paper_padded_odd_tight_instability_family_statement`. -/
theorem paper_padded_odd_tight_instability_family_statement
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_choice_function_feasible (paddedOddChoice q n) ∧
      paper_definition_q_acceptance q (paddedOddChoice q n) ∧
        paper_definition_tight_d_instability (2 * n - 1) (paddedOddChoice q n) := by
  exact paper_padded_odd_tight_instability_family hnpos hnq

/-- Source status: audited PaperInterface row `paper_definition_sequential_composition`. -/
abbrev paper_definition_sequential_composition
    (Cs : List (PaperChoiceRule α)) : PaperChoiceRule α :=
  paper_sequential_composition Cs

/-- Source status: audited PaperInterface row `paper_sequential_q_representative_variability_bound_statement`. -/
theorem paper_sequential_q_representative_variability_bound_statement
    [Fintype α] {Cs : List (PaperChoiceRule α)}
    (hqueues :
      ∀ C ∈ Cs, ∃ q, paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C) :
    paper_definition_variability_at_most Cs.length
      (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_q_representative_variability_at_most_length hqueues

/-- Source status: audited PaperInterface row `paper_sequential_q_representative_choice_properties_statement`. -/
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

/-- Source status: audited nontrivial realized-variability range row. -/
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

/-- Source status: audited canonical Screened/Open program model. -/
abbrev paper_definition_screened_open_program_choice : PaperChoiceRule (Fin 2) :=
  paperScreenedOpenProgramChoice

/-- Source status: audited canonical Screened/Open with DIA program model. -/
abbrev paper_definition_screened_open_dia_program_choice : PaperChoiceRule (Fin 4) :=
  paperScreenedOpenDIAProgramChoice

/-- Source status: audited canonical Educational Option program model. -/
abbrev paper_definition_educational_option_program_choice : PaperChoiceRule (Fin 6) :=
  paperEducationalOptionProgramChoice

/-- Source status: audited canonical Educational Option with DIA program model. -/
abbrev paper_definition_educational_option_dia_program_choice : PaperChoiceRule (Fin 12) :=
  paperEducationalOptionDIAProgramChoice

/-- Source status: audited Proposition 2 Screened/Open row. -/
theorem paper_screened_open_program_properties_statement :
    paper_choice_function_feasible paper_definition_screened_open_program_choice ∧
      paper_definition_q_acceptance 1 paper_definition_screened_open_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_program_choice ∧
      paper_definition_variability_exactly 1
        paper_definition_screened_open_program_choice := by
  exact paper_screened_open_program_properties

/-- Source status: Proposition 2 abstract Screened/Open procedure. -/
theorem paper_screened_open_variability_one_statement :
    paper_definition_variability_exactly 1
      paper_definition_screened_open_program_choice := by
  exact paper_screened_open_program_properties_statement.2.2.2

/-- Source status: audited Proposition 2 Screened/Open with DIA row. -/
theorem paper_screened_open_dia_program_properties_statement :
    paper_choice_function_feasible paper_definition_screened_open_dia_program_choice ∧
      paper_definition_q_acceptance 2 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_variability_exactly 2
        paper_definition_screened_open_dia_program_choice := by
  exact paper_screened_open_dia_program_properties

/-- Source status: Proposition 2 abstract Screened/Open-with-DIA procedure. -/
theorem paper_screened_open_dia_variability_two_statement :
    paper_definition_variability_exactly 2
      paper_definition_screened_open_dia_program_choice := by
  exact paper_screened_open_dia_program_properties_statement.2.2.2

/-- Source status: audited Proposition 2 Educational Option row. -/
theorem paper_educational_option_program_properties_statement :
    paper_choice_function_feasible paper_definition_educational_option_program_choice ∧
      paper_definition_q_acceptance 3 paper_definition_educational_option_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_program_choice ∧
      paper_definition_variability_exactly 3
        paper_definition_educational_option_program_choice := by
  exact paper_educational_option_program_properties

/-- Source status: Proposition 2 abstract Educational Option procedure. -/
theorem paper_educational_option_variability_three_statement :
    paper_definition_variability_exactly 3
      paper_definition_educational_option_program_choice := by
  exact paper_educational_option_program_properties_statement.2.2.2

/-- Source status: audited Proposition 2 Educational Option with DIA row. -/
theorem paper_educational_option_dia_program_properties_statement :
    paper_choice_function_feasible paper_definition_educational_option_dia_program_choice ∧
      paper_definition_q_acceptance 6 paper_definition_educational_option_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_dia_program_choice ∧
      paper_definition_variability_exactly 6
        paper_definition_educational_option_dia_program_choice := by
  exact paper_educational_option_dia_program_properties

/-- Source status: Proposition 2 abstract Educational Option-with-DIA procedure. -/
theorem paper_educational_option_dia_variability_six_statement :
    paper_definition_variability_exactly 6
      paper_definition_educational_option_dia_program_choice := by
  exact paper_educational_option_dia_program_properties_statement.2.2.2

/-- Source status: Proposition 2 aggregate for the four abstract procedures. -/
theorem paper_program_classes_one_instability_statement :
    paper_definition_d_instability 1 paper_definition_screened_open_program_choice ∧
      paper_definition_d_instability 1 paper_definition_screened_open_dia_program_choice ∧
      paper_definition_d_instability 1 paper_definition_educational_option_program_choice ∧
      paper_definition_d_instability 1
        paper_definition_educational_option_dia_program_choice := by
  exact paper_program_classes_one_instability

/-- Source status: audited PaperInterface row `paper_definition_monotonicity`. -/
abbrev paper_definition_monotonicity (C : PaperChoiceRule α) : Prop :=
  paper_monotonic C

/-- Source status: audited monotonicity definition formula. -/
theorem paper_monotonicity_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_monotonicity C ↔
      ∀ {X₁ X₂}, X₁ ⊆ X₂ → C X₁ ⊆ C X₂ := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_consistency`. -/
abbrev paper_definition_consistency (C : PaperChoiceRule α) : Prop :=
  paper_consistent C

/-- Source status: audited consistency definition formula. -/
theorem paper_consistency_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_consistency C ↔
      ∀ {X₁ X₂}, C X₂ ⊆ X₁ → X₁ ⊆ X₂ → C X₂ = C X₁ := by
  rfl

/-- Source status: audited PaperInterface row `paper_monotonicity_q_acceptance_incompatible_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_non_substitutable_single_add_statement`. -/
theorem paper_non_substitutable_single_add_statement
    (C : PaperChoiceRule α)
    (hnot : ¬ paper_definition_substitutability C) :
    ∃ X x xstar,
      x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X := by
  exact paper_non_substitutable_single_add C hnot

/-- Source status: audited PaperInterface row `paper_substitutability_term_statement`. -/
theorem paper_substitutability_term_statement
    (C : PaperChoiceRule α) :
    paper_definition_substitutability C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        ((X₁ ∩ C X₂) \ C X₁).card = 0 := by
  simpa [paper_definition_substitutability] using paper_substitutability_term C

/-- Source status: audited PaperInterface row `paper_monotonicity_term_statement`. -/
theorem paper_monotonicity_term_statement
    (C : PaperChoiceRule α) :
    paper_definition_monotonicity C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        (C X₁ \ C X₂).card = 0 := by
  simpa [paper_definition_monotonicity] using paper_monotonicity_term C

/-- Source status: audited PaperInterface row `paper_choice_distance_triangle_statement`. -/
theorem paper_choice_distance_triangle_statement
    (C : PaperChoiceRule α) {X₁ X₂ X₃ : Finset α}
    (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
    paper_definition_choice_distance C X₁ X₃ ≤
      paper_definition_choice_distance C X₁ X₂ +
        paper_definition_choice_distance C X₂ X₃ := by
  simpa [paper_definition_choice_distance] using
    paper_choice_distance_triangle C h₁₂ h₂₃

/-- Source status: audited PaperInterface row `paper_definition_zero_instability`. -/
abbrev paper_definition_zero_instability (C : PaperChoiceRule α) : Prop :=
  paper_zero_unstable C

/-- Source status: audited zero-instability definition formula. -/
theorem paper_zero_instability_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_zero_instability C ↔
      ∀ {X₁ X₂}, X₁ ⊆ X₂ → choiceDistance C X₁ X₂ = 0 := by
  rfl

/-- Source status: audited PaperInterface row `paper_zero_distance_statement`. -/
theorem paper_zero_distance_statement
    (C : PaperChoiceRule α) :
    paper_definition_zero_instability C ↔
      paper_definition_substitutability C ∧ paper_definition_monotonicity C := by
  simpa [paper_definition_zero_instability, paper_definition_substitutability,
    paper_definition_monotonicity] using
      paper_zero_distance_iff_substitutable_and_monotonic C

/-- Source status: audited PaperInterface row `paper_definition_independence`. -/
abbrev paper_definition_independence (C : PaperChoiceRule α) : Prop :=
  paper_independent C

/-- Source status: audited independence definition formula. -/
theorem paper_independence_definition_statement
    (C : PaperChoiceRule α) :
    paper_definition_independence C ↔
      ∀ x,
        (∀ X, x ∈ X → x ∈ C X) ∨
          (∀ X, x ∈ X → x ∉ C X) := by
  rfl

/-- Source status: audited PaperInterface row `paper_independent_substitutable_monotonic_statement`. -/
theorem paper_independent_substitutable_monotonic_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C) :
    paper_definition_independence C ↔
      paper_definition_substitutability C ∧ paper_definition_monotonicity C := by
  simpa [paper_choice_function_feasible, paper_definition_independence,
    paper_definition_substitutability, paper_definition_monotonicity] using
      paper_independent_iff_substitutable_and_monotonic C hfeasible

/-- Source status: audited PaperInterface row `paper_independent_zero_unstable_statement`. -/
theorem paper_independent_zero_unstable_statement
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C) :
    paper_definition_independence C ↔ paper_definition_zero_instability C := by
  simpa [paper_choice_function_feasible, paper_definition_independence,
    paper_definition_zero_instability] using
      paper_independent_iff_zero_unstable C hfeasible

/-- Source status: audited PaperInterface row `paper_one_instability_of_substitutability_statement`. -/
theorem paper_one_instability_of_substitutability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C) :
    paper_definition_d_instability 1 C := by
  exact paper_one_instability_of_q_acceptant_substitutable
    (C := C) hfeasible haccept hsub

/-- Source status: audited PaperInterface row `paper_q_acceptant_substitutable_consistent_statement`. -/
theorem paper_q_acceptant_substitutable_consistent_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C) :
    paper_definition_consistency C := by
  intro X₁ X₂ hchosen_subset hsubset
  exact paper_q_acceptant_substitutable_consistent
    (C := C) haccept hsub hchosen_subset hsubset

/-- Source status: audited PaperInterface row `paper_calculating_instability_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_even_instability_inconsistency_forward_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_even_instability_inconsistency_converse_statement`. -/
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

/-- Source status: audited positive-even-distance iff inconsistency theorem. -/
theorem paper_even_distance_iff_inconsistent_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C) :
    (¬ paper_definition_consistency C) ↔
      ∃ X x, x ∉ X ∧
        0 < paper_definition_choice_distance C X (insert x X) ∧
          ∃ k, paper_definition_choice_distance C X (insert x X) = 2 * k := by
  constructor
  · exact paper_even_instability_inconsistency_converse_statement
      hfeasible haccept
  · rintro ⟨X, x, hx, hpositive, heven⟩
    exact paper_even_instability_inconsistency_forward_statement
      hfeasible haccept hx hpositive heven

/-- Source status: audited PaperInterface row `paper_no_consistent_tightly_even_instability_statement`. -/
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

/-- Source status: audited absence of positive tightly-even consistent rules. -/
theorem paper_no_consistent_positive_tightly_even_statement
    {q k : ℕ} {C : PaperChoiceRule α}
    (hk : 0 < k)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C) :
    ¬ paper_definition_tight_d_instability (2 * k) C := by
  intro htight
  have hbetter : paper_definition_d_instability (2 * k - 1) C :=
    paper_no_consistent_tightly_even_instability_statement
      hk hfeasible haccept hcons htight.1
  exact htight.2 (2 * k - 1) (by omega) hbetter

/-- Source status: audited PaperInterface row `paper_no_consistent_tightly_two_instability_statement`. -/
theorem paper_no_consistent_tightly_two_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C)
    (hunstable : paper_definition_d_instability 2 C) :
    paper_definition_d_instability 1 C := by
  exact paper_no_consistent_tightly_two_instability
    (C := C) hfeasible haccept hcons hunstable

/-- Source status: audited PaperInterface row `paper_definition_waitlisted_set`. -/
abbrev paper_definition_waitlisted_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  paper_waitlisted_set C X

/-- Source status: audited PaperInterface row `paper_definition_general_variability_at_most`. -/
abbrev paper_definition_general_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_general_variability_at_most m C

/-- Source status: audited general-variability upper-bound formula. -/
theorem paper_general_variability_at_most_definition_statement [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) :
    paper_definition_general_variability_at_most m C ↔
      ∀ X,
        (paper_definition_borderline_set C X).card ≤ m ∧
          (paper_definition_waitlisted_set C X).card ≤ m := by
  rfl

/-- Source status: audited PaperInterface row `paper_definition_general_variability_exactly`. -/
abbrev paper_definition_general_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  paper_general_variability_exactly m C

/-- Source status: audited exact general-variability formula. -/
theorem paper_general_variability_exactly_definition_statement [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) :
    paper_definition_general_variability_exactly m C ↔
      paper_definition_general_variability_at_most m C ∧
        ((∃ X, (paper_definition_borderline_set C X).card = m) ∨
          ∃ X, (paper_definition_waitlisted_set C X).card = m) := by
  rfl

/-! ## Linear Assignment Appendix Definitions -/

/-- Source status: audited PaperInterface row `paper_append_remove_variability_at_most_equivalence_statement`. -/
theorem paper_append_remove_variability_at_most_equivalence_statement
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C) :
    paper_definition_general_variability_at_most m C ↔
      paper_definition_variability_at_most m C := by
  exact paper_append_remove_variability_at_most_equivalence
    (C := C) hfeasible haccept hunstable

/-- Source status: audited PaperInterface row `paper_append_remove_variability_exact_equivalence_statement`. -/
theorem paper_append_remove_variability_exact_equivalence_statement
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hcard : 2 * q ≤ Fintype.card α) :
    paper_definition_general_variability_exactly m C ↔
      paper_definition_variability_exactly m C := by
  exact paper_append_remove_variability_exact_equivalence
    (C := C) hfeasible haccept hunstable

/-- Source status: audited PaperInterface row `paper_corrected_consistency_of_removable_sets_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement`. -/
theorem paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_at_most 1 C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X) :
    paper_definition_borderline_set C X =
      paper_definition_waitlisted_set C (insert x X) := by
  exact
    paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert
      (C := C) hfeasible haccept hunstable hvar hx hchange

/-- Source status: audited PaperInterface row `paper_q_representative_borderline_eq_waitlisted_after_changing_insert_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_q_representative_q_acceptant_statement`. -/
theorem paper_q_representative_q_acceptant_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_q_acceptance q C := by
  exact paper_q_representative_q_acceptant hrep

/-- Source status: audited PaperInterface row `paper_q_representative_one_instability_statement`. -/
theorem paper_q_representative_one_instability_statement
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_d_instability 1 C := by
  exact paper_q_representative_one_instability
    (C := C) hfeasible hrep

/-- Source status: audited PaperInterface row `paper_q_representative_variability_at_most_one_statement`. -/
theorem paper_q_representative_variability_at_most_one_statement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C) :
    paper_definition_variability_at_most 1 C := by
  exact paper_q_representative_variability_at_most_one
    (C := C) hfeasible hrep

/-- Source status: audited PaperInterface row `paper_q_representative_converse_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_sequential_composition_substitutable_statement`. -/
theorem paper_sequential_composition_substitutable_statement
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_choice_function_feasible C)
    (hsub : ∀ C ∈ Cs, paper_definition_substitutability C) :
    paper_definition_substitutability (paper_definition_sequential_composition Cs) := by
  exact paper_sequential_composition_substitutable hfeasible hsub

/-- Source status: audited PaperInterface row `paper_sequential_additive_variability_bound_statement`. -/
theorem paper_sequential_additive_variability_bound_statement
    [Fintype α] {qs ms : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hcapacity : List.Forall₂
      (fun q C =>
        paper_choice_function_feasible C ∧
          paper_definition_q_acceptance q C ∧
            paper_definition_d_instability 1 C)
      qs Cs)
    (hvariability : List.Forall₂
      (fun m C => paper_definition_variability_at_most m C)
      ms Cs) :
    paper_definition_variability_at_most
      ms.sum (paper_definition_sequential_composition Cs) := by
  exact
    paper_sequential_additive_variability_bound_of_stage_lists
      hcapacity hvariability

/-! ## Linear-assignment source model -/

/-- Source status: audited finite applicant-slot assignment object. -/
abbrev paper_definition_lap_assignment
    (σ : Type*) [DecidableEq σ] := LAP.Assignment α σ

/-- Source status: audited assignment incidence predicate. -/
abbrev paper_definition_lap_assigned
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : LAP.Assignment α σ) (x : α) : Prop :=
  A.Assigned x

/-- Source status: audited matching feasibility constraints. -/
abbrev paper_definition_lap_assignment_feasible
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (A : LAP.Assignment α σ) : Prop :=
  A.Feasible X

/-- Source status: audited capacity-filling assignment convention. -/
abbrev paper_definition_lap_capacity_filling
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (A : LAP.Assignment α σ) : Prop :=
  A.CapacityFilling X

/-- Source status: capacity-filling real-weight optimum used by fixed-slot results. -/
abbrev paper_definition_lap_objective_optimal
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  A.ObjectiveOptimal X w

/-- Source status: audited assignment-induced choice function. -/
abbrev paper_definition_lap_choice_rule
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) : PaperChoiceRule α :=
  LAP.Assignment.choiceRuleOfAssignment select

/-- Source status: audited strict slot order induced by real weights. -/
abbrev paper_definition_lap_slot_below
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (x y : α) : Prop :=
  LAP.Assignment.SlotBelow w s x y

/-- Source status: audited strict real-weight slot-order formula. -/
theorem paper_lap_slot_below_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (x y : α) :
    paper_definition_lap_slot_below w s x y ↔ w x s < w y s := by
  rfl

/-- Source status: audited equality of slot-induced applicant orders. -/
abbrev paper_definition_lap_same_slot_order
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s t : σ) : Prop :=
  LAP.Assignment.SameSlotOrder w s t

/-- Source status: audited extensional equality of slot-induced orders. -/
theorem paper_lap_same_slot_order_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s t : σ) :
    paper_definition_lap_same_slot_order w s t ↔
      ∀ x y, (w x s < w y s ↔ w x t < w y t) := by
  rfl

/-- Source status: audited canonical number of distinct slot orders. -/
noncomputable abbrev paper_definition_lap_distinct_slot_order_count
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) : ℕ :=
  LAP.Assignment.distinctSlotOrderCount w

/-- Source status: audited all-feasible real-weight maximum-assignment model. -/
abbrev paper_definition_lap_model
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  paper_definition_lap_assignment_feasible X A ∧
    ∀ B : LAP.Assignment α σ,
      paper_definition_lap_assignment_feasible X B →
        LAP.Assignment.objective w B ≤ LAP.Assignment.objective w A

/-- Source status: audited all-feasible real-weight LAP model formula. -/
theorem paper_lap_model_definition_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) :
    paper_definition_lap_model X w A ↔
      paper_definition_lap_assignment_feasible X A ∧
        ∀ B : LAP.Assignment α σ,
          paper_definition_lap_assignment_feasible X B →
            LAP.Assignment.objective w B ≤ LAP.Assignment.objective w A := by
  rfl

/-- Source status: audited formula relating assignment incidence and induced choice. -/
theorem paper_lap_assignment_choice_formula_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) (X : Finset α) (x : α) :
    x ∈ paper_definition_lap_choice_rule select X ↔
      paper_definition_lap_assigned (select X) x := by
  exact LAP.Assignment.mem_chosenSet

/-- Source status: audited PaperInterface row `paper_lap_ordering_statement`. -/
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

/-- Source status: audited strict assigned-versus-rejected slot ordering. -/
theorem paper_lap_assigned_strictly_outranks_rejected_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : LAP.Assignment.Rejected X A x)
    (hnoTies : LAP.Assignment.SlotNoTies w s) :
    paper_definition_lap_slot_below w s x y := by
  have hatleast : LAP.Assignment.SlotAtLeast w s y x :=
    paper_lap_ordering_statement hobjective hfill hassign hslot hrej
  have hxy : x ≠ y := by
    intro hxy
    apply hrej.2
    exact ⟨s, by simpa [hxy] using hslot⟩
  exact lt_of_le_of_ne hatleast (hnoTies hxy)

/-- Source status: audited PaperInterface row `paper_lap_strictly_higher_slot_applicant_assigned_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_lap_no_rejected_slot_below_statement`. -/
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

/-- Source status: audited PaperInterface row `paper_lap_no_profitable_one_slot_swap_of_objective_optimal_statement`. -/
theorem paper_lap_no_profitable_one_slot_swap_of_objective_optimal_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ}
    {A : paper_definition_lap_assignment (α := α) σ}
    (hopt : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A) :
    paper_definition_lap_no_profitable_one_slot_swap X w A := by
  exact paper_lap_no_profitable_one_slot_swap_of_objective_optimal
    hopt hfill

/-- Source status: audited PaperInterface row `paper_lap_assignment_one_instability_statement`. -/
theorem paper_lap_assignment_one_instability_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧ LAP.Assignment.CapacityFilling X A ∧
        LAP.Assignment.ObjectiveOptimal X w A ∧ ∀ B : LAP.Assignment α σ,
          LAP.Assignment.Feasible X B → LAP.Assignment.CapacityFilling X B →
            LAP.Assignment.ObjectiveOptimal X w B → B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s) :
    paper_definition_d_instability 1
      (paperLAPChoiceRule w hwell) := by
  exact paper_lap_well_posed_choice_one_instability hwell

/-- Source status: audited PaperInterface row `paper_lap_assignment_selector_feasible_choice_statement`. -/
theorem paper_lap_assignment_selector_feasible_choice_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, paper_definition_lap_assignment_feasible X (select X)) :
    paper_choice_function_feasible
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_feasible_choice hfeas

/-- Source status: audited PaperInterface row `paper_lap_assignment_selector_q_acceptant_statement`. -/
theorem paper_lap_assignment_selector_q_acceptant_statement
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, paper_definition_lap_assignment_feasible X (select X))
    (hfill : ∀ X, paper_definition_lap_capacity_filling X (select X)) :
    paper_definition_q_acceptance (Fintype.card σ)
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_q_acceptant hfeas hfill

/-- Source status: audited PaperInterface row `paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement`. -/
theorem paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧ LAP.Assignment.CapacityFilling X A ∧
        LAP.Assignment.ObjectiveOptimal X w A ∧ ∀ B : LAP.Assignment α σ,
          LAP.Assignment.Feasible X B → LAP.Assignment.CapacityFilling X B →
            LAP.Assignment.ObjectiveOptimal X w B → B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s) :
    paper_definition_variability_at_most
      (LAP.Assignment.distinctSlotOrderCount w)
      (paperLAPChoiceRule w hwell) := by
  exact
    paper_lap_well_posed_choice_variability_at_most_distinct_slot_orders
      hwell hnoTies

/-- Source status: audited PaperInterface row `paper_lap_assignment_variability_at_most_slots_statement`. -/
theorem paper_lap_assignment_variability_at_most_slots_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → paper_definition_lap_assignment (α := α) σ) :
    paper_definition_variability_at_most (Fintype.card σ)
      (paper_definition_lap_choice_rule (α := α) select) := by
  exact paper_lap_assignment_selector_variability_at_most_slots select

/-- Source status: audited PaperInterface row `paper_lap_assignment_borderline_card_le_slots_statement`. -/
theorem paper_lap_assignment_borderline_card_le_slots_statement
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → paper_definition_lap_assignment (α := α) σ)
    (X : Finset α) :
    (paper_definition_borderline_set
      (paper_definition_lap_choice_rule (α := α) select) X).card ≤
        Fintype.card σ := by
  exact paper_lap_assignment_selector_borderline_card_le_slots select X

end ProofBridge
end DGD26AdmissionsPredictability
