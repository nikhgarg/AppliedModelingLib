import DGD26AdmissionsPredictability.AuditInterface
import DGD26AdmissionsPredictability.SourceModel

namespace DGD26AdmissionsPredictability

namespace PaperInterface

open AppliedModelingLib.FiniteChoice
variable {α : Type*} [DecidableEq α]

def paper_choice_function_model_definition_statementSpec
    (C : PaperChoiceRule α) : Prop :=
  paper_feasible C ↔ ∀ X, C X ⊆ X

def paper_definition_choice_labelSpec
    (C : PaperChoiceRule α) (X : Finset α) (x : α) (hx : x ∈ X) : Prop :=
  paperChoiceLabel C X x = if x ∈ C X then 1 else 0

/-- Source-facing semantic target for the introductory binary-classifier model. -/
def paper_binary_classifier_model_statementSpec
    (f : α → ℕ) : Prop :=
  ∀ x, f x = 0 ∨ f x = 1

/-- Source-facing semantic target for `paper_ml_representation_definition_statement`. -/
def paper_ml_representation_definition_statementSpec
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α)  : Prop :=
  paper_definition_ml_representation predicts C ↔
        ∀ X x, x ∈ X → (predicts X x ↔ x ∈ C X)

/-- Source-facing semantic target for `paper_q_acceptance_definition_statement`. -/
def paper_q_acceptance_definition_statementSpec
    (q : ℕ) (C : PaperChoiceRule α)  : Prop :=
  paper_definition_q_acceptance q C ↔
        ∀ X, (C X).card = min q X.card

/-- Source-facing semantic target for `paper_total_order_definition_statement`. -/
def paper_total_order_definition_statementSpec
    (r : α → α → Prop)  : Prop :=
  paper_definition_total_order r ↔
        (∀ x, ¬ r x x) ∧
          (∀ {x y z}, r x y → r y z → r x z) ∧
            (∀ {x y}, x ≠ y → r x y ∨ r y x)

/-- Source-facing semantic target for `paper_q_representativeness_definition_statement`. -/
def paper_q_representativeness_definition_statementSpec
    (q : ℕ) (C : PaperChoiceRule α)  : Prop :=
  paper_choice_function_feasible C ∧
      paper_definition_q_representativeness q C ↔
    paper_choice_function_feasible C ∧
      ∃ r : α → α → Prop,
        paper_definition_total_order r ∧
          paper_choice_function_feasible C ∧
            paper_definition_q_acceptance q C ∧
              ∀ {X x y}, x ∈ C X → y ∈ X → y ∉ C X → r x y

def paper_definition_choice_distanceSpec
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) (hsubset : X₁ ⊆ X₂) : Prop :=
  choiceDistance C X₁ X₂ =
    ((X₁ ∩ C X₂) \ C X₁).card + (C X₁ \ C X₂).card

/-- Source-facing semantic target for `paper_d_instability_definition_statement`. -/
def paper_d_instability_definition_statementSpec
    (d : ℕ) (C : PaperChoiceRule α)  : Prop :=
  paper_definition_d_instability d C ↔
        ∀ X x, x ∉ X → choiceDistance C X (insert x X) ≤ d

/-- Source-facing semantic target for `paper_tight_d_instability_definition_statement`. -/
def paper_tight_d_instability_definition_statementSpec
    (d : ℕ) (C : PaperChoiceRule α)  : Prop :=
  0 < d →
    (paper_definition_tight_d_instability d C ↔
      paper_definition_d_instability d C ∧
        ∀ k, k < d → ¬ paper_definition_d_instability k C)

def paper_definition_borderline_setSpec [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Prop :=
  paper_borderline_set C X =
    Finset.univ.biUnion (fun x => C X \ C (insert x X))

/-- Source-facing semantic target for `paper_variability_exactly_definition_statement`. -/
def paper_variability_exactly_definition_statementSpec [Fintype α]
    {q : ℕ} (m : ℕ) (C : PaperChoiceRule α)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C) : Prop :=
  paper_definition_variability_exactly m C ↔
        (∀ X, (paper_definition_borderline_set C X).card ≤ m) ∧
          ∃ X, (paper_definition_borderline_set C X).card = m

/-- Source-facing semantic target for `paper_fixed_threshold_formula_statement`. -/
def paper_fixed_threshold_formula_statementSpec
    (score : α → ℝ) (threshold : ℝ)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1)
    (X : Finset α) (x : α)  : Prop :=
  x ∈ paperFixedThresholdChoice score threshold X ↔
        x ∈ X ∧ paper_definition_fixed_threshold_predictor
          score threshold X x

/-- Source-facing semantic target for `paper_ml_fixed_threshold_representation_zero_unstable_statement`. -/
def paper_ml_fixed_threshold_representation_zero_unstable_statementSpec
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hscore : ∀ x, 0 ≤ score x ∧ score x ≤ 1)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_fixed_threshold_predictor score threshold) C)  : Prop :=
  paper_definition_zero_instability C

/-- Source-facing semantic target for `paper_rank_threshold_formula_statement`.
`operationalScore` is the source score after the fixed generic, ex-ante
tie-break for equal raw scores; its injectivity is a property of that
operational refinement, not a claim that raw scores are distinct. -/
def paper_rank_threshold_formula_statementSpec
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q) (X : Finset α) (hqcard : q ≤ X.card)  : Prop :=
  ∃ threshold : ℝ,
    threshold ∈ X.image operationalScore ∧
      (X.filter (fun x => threshold ≤ operationalScore x)).card = q ∧
        ∀ x ∈ X,
          (paper_definition_rank_threshold_predictor
              q operationalScore hinjective X x ↔ threshold ≤ operationalScore x)

/-- Source-facing semantic target for `paper_ml_rank_threshold_representation_instability_bound_statement`. -/
def paper_ml_rank_threshold_representation_instability_bound_statementSpec
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q operationalScore hinjective) C)  : Prop :=
  paper_definition_d_instability 1 C

/-- Source-facing semantic target for `paper_ml_rank_threshold_representation_variability_bound_statement`. -/
def paper_ml_rank_threshold_representation_variability_bound_statementSpec
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (operationalScore : α → ℝ)
    (hinjective : Function.Injective operationalScore)
    (hqpos : 0 < q)
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_ml_representation
      (paper_definition_rank_threshold_predictor q operationalScore hinjective) C)  : Prop :=
  paper_definition_variability_at_most 1 C

/-- Source-facing semantic target for `paper_ml_rank_threshold_can_represent_exact_one_statement`. -/
def paper_ml_rank_threshold_can_represent_exact_one_statementSpec
    (q : ℕ) (hqpos : 0 < q)  : Prop :=
  ∃ (score : Fin (q + 1) → ℝ) (hinjective : Function.Injective score),
        paper_definition_tight_d_instability 1
            (paperRankThresholdChoice q score hinjective) ∧
          paper_definition_variability_exactly 1
            (paperRankThresholdChoice q score hinjective)

/-- Source-facing semantic target for `paper_q_representative_forward_exact_statement`. -/
def paper_q_representative_forward_exact_statementSpec
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hrep : paper_definition_q_representativeness q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : Prop :=
  paper_definition_q_acceptance q C ∧
        paper_definition_d_instability 1 C ∧
          paper_definition_variability_exactly 1 C

/-- Source-facing semantic target for `paper_q_representative_converse_exact_statement`. -/
def paper_q_representative_converse_exact_statementSpec
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : Prop :=
  paper_definition_q_representativeness q C

/-- Source-facing semantic target for `paper_variability_one_iff_single_order_statement`. -/
def paper_variability_one_iff_single_order_statementSpec
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α)  : Prop :=
  paper_definition_variability_exactly 1 C ↔
        paper_definition_q_representativeness q C

/-- Source-facing semantic target for `paper_substitutability_definition_statement`. -/
def paper_substitutability_definition_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_substitutability C ↔
        ∀ {X₁ X₂}, X₁ ⊆ X₂ → X₁ ∩ C X₂ ⊆ C X₁

/-- Source-facing semantic target for `paper_no_zero_instability_under_capacity_statement`. -/
def paper_no_zero_instability_under_capacity_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card)  : Prop :=
  ¬ paper_definition_zero_instability C

def paper_independent_zero_unstable_corollary_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) : Prop :=
  (paper_definition_zero_instability C ↔ paper_definition_independence C) ∧
    ¬ paper_definition_zero_instability C

/-- Source-facing semantic target for `paper_substitutability_one_instability_equivalence_statement`. -/
def paper_substitutability_one_instability_equivalence_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card)  : Prop :=
  paper_definition_substitutability C ↔
    paper_definition_d_instability 1 C ∧ ¬ paper_definition_zero_instability C

/-- Source-facing semantic target for the separately labelled capacity-constrained
substitutability/one-instability theorem. -/
def paper_qacceptant_substitutable_iff_one_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) : Prop :=
  paper_definition_d_instability 1 C ∧ ¬ paper_definition_zero_instability C ↔
    paper_definition_substitutability C

def paper_theorem1_tight_all_d_statementSpec
    (q d : ℕ) : Prop :=
  1 ≤ d → d ≤ 2 * q →
    ∃ (β : Type) (inst : DecidableEq β) (C : @PaperChoiceRule β inst),
      @paper_choice_function_feasible β inst C ∧
        @paper_definition_q_acceptance β inst q C ∧
          @paper_definition_tight_d_instability β inst d C

def paper_definition_sequential_compositionSpec
    (Cs : List (PaperChoiceRule α)) : Prop :=
  paper_sequential_composition Cs = sequentialCompositionSource Cs

/-- Source-facing semantic target for `paper_sequential_q_representative_variability_range_statement`. -/
def paper_sequential_q_representative_variability_range_statementSpec
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_choice_function_feasible C ∧
        paper_definition_q_representativeness q C) qs Cs)
    (hqpos : 0 < qs.sum)
    (hqlt : qs.sum < Fintype.card α)  : Prop :=
  ∃ m, 1 ≤ m ∧ m ≤ Cs.length ∧
        paper_definition_variability_exactly m
          (paper_definition_sequential_composition Cs)

/-- Source-facing Proposition 2 target for the abstract Screened/Open procedure. -/
def paper_screened_open_variability_one_statementSpec  : Prop :=
  paper_definition_variability_exactly 1
        paper_definition_screened_open_program_choice

/-- Source-facing Proposition 2 target for the abstract Screened/Open-with-DIA procedure. -/
def paper_screened_open_dia_variability_two_statementSpec  : Prop :=
  paper_definition_variability_exactly 2
        paper_definition_screened_open_dia_program_choice

/-- Source-facing Proposition 2 target for the abstract Educational Option procedure. -/
def paper_educational_option_variability_three_statementSpec  : Prop :=
  paper_definition_variability_exactly 3
        paper_definition_educational_option_program_choice

/-- Source-facing Proposition 2 target for the abstract Educational Option-with-DIA procedure. -/
def paper_educational_option_dia_variability_six_statementSpec  : Prop :=
  paper_definition_variability_exactly 6
        paper_definition_educational_option_dia_program_choice

/-- Source-facing Proposition 2 aggregate for the four abstract queue procedures. -/
def paper_program_classes_one_instability_statementSpec  : Prop :=
  paper_definition_d_instability 1 paper_definition_screened_open_program_choice ∧
        paper_definition_d_instability 1 paper_definition_screened_open_dia_program_choice ∧
        paper_definition_d_instability 1 paper_definition_educational_option_program_choice ∧
        paper_definition_d_instability 1
          paper_definition_educational_option_dia_program_choice

/-- Source-facing semantic target for `paper_monotonicity_definition_statement`. -/
def paper_monotonicity_definition_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_monotonicity C ↔
        ∀ {X₁ X₂}, X₁ ⊆ X₂ → C X₁ ⊆ C X₂

/-- Source-facing semantic target for `paper_consistency_definition_statement`. -/
def paper_consistency_definition_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_consistency C ↔
        ∀ {X₁ X₂}, C X₂ ⊆ X₁ → X₁ ⊆ X₂ → C X₂ = C X₁

/-- Source-facing semantic target for `paper_monotonicity_q_acceptance_incompatible_statement`. -/
def paper_monotonicity_q_acceptance_incompatible_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (hmono : paper_definition_monotonicity C)
    (haccept : paper_definition_q_acceptance q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card)  : Prop :=
  False

/-- Source-facing semantic target for `paper_non_substitutable_single_add_statement`. -/
def paper_non_substitutable_single_add_statementSpec
    (C : PaperChoiceRule α)
    (hnot : ¬ paper_definition_substitutability C)  : Prop :=
  ∃ X x xstar,
        x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X

/-- Source-facing semantic target for `paper_substitutability_term_statement`. -/
def paper_substitutability_term_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_substitutability C ↔
        ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
          ((X₁ ∩ C X₂) \ C X₁).card = 0

/-- Source-facing semantic target for `paper_monotonicity_term_statement`. -/
def paper_monotonicity_term_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_monotonicity C ↔
        ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
          (C X₁ \ C X₂).card = 0

/-- Source-facing semantic target for `paper_choice_distance_triangle_statement`. -/
def paper_choice_distance_triangle_statementSpec
    (C : PaperChoiceRule α) {X₁ X₂ X₃ : Finset α}
    (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃)  : Prop :=
  paper_definition_choice_distance C X₁ X₃ ≤
        paper_definition_choice_distance C X₁ X₂ +
          paper_definition_choice_distance C X₂ X₃

/-- Source-facing semantic target for `paper_zero_instability_definition_statement`. -/
def paper_zero_instability_definition_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_zero_instability C ↔
        ∀ {X₁ X₂}, X₁ ⊆ X₂ → choiceDistance C X₁ X₂ = 0

/-- Source-facing semantic target for `paper_zero_distance_statement`. -/
def paper_zero_distance_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_zero_instability C ↔
        paper_definition_substitutability C ∧ paper_definition_monotonicity C

/-- Source-facing semantic target for `paper_independence_definition_statement`. -/
def paper_independence_definition_statementSpec
    (C : PaperChoiceRule α)  : Prop :=
  paper_definition_independence C ↔
        ∀ x,
          (∀ X, x ∈ X → x ∈ C X) ∨
            (∀ X, x ∈ X → x ∉ C X)

/-- Source-facing semantic target for `paper_independent_substitutable_monotonic_statement`. -/
def paper_independent_substitutable_monotonic_statementSpec
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C)  : Prop :=
  paper_definition_independence C ↔
        paper_definition_substitutability C ∧ paper_definition_monotonicity C

/-- Source-facing semantic target for `paper_independent_zero_unstable_statement`. -/
def paper_independent_zero_unstable_statementSpec
    (C : PaperChoiceRule α) (hfeasible : paper_choice_function_feasible C)  : Prop :=
  paper_definition_independence C ↔ paper_definition_zero_instability C

/-- Source-facing semantic target for `paper_q_acceptant_substitutable_consistent_statement`. -/
def paper_q_acceptant_substitutable_consistent_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)  : Prop :=
  paper_definition_consistency C

/-- Source-facing semantic target for `paper_calculating_instability_statement`. -/
def paper_calculating_instability_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hx : x ∉ X)  : Prop :=
  paper_definition_choice_distance C X (insert x X) =
        if x ∈ C (insert x X) then
          2 * (C X \ C (insert x X)).card - 1
        else
          2 * (C X \ C (insert x X)).card

/-- Source-facing semantic target for `paper_even_distance_iff_inconsistent_statement`. -/
def paper_even_distance_iff_inconsistent_statementSpec
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)  : Prop :=
  (¬ paper_definition_consistency C) ↔
        ∃ X x, x ∉ X ∧
          0 < paper_definition_choice_distance C X (insert x X) ∧
            ∃ k, paper_definition_choice_distance C X (insert x X) = 2 * k

/-- Source-facing semantic target for `paper_no_consistent_positive_tightly_even_statement`. -/
def paper_no_consistent_positive_tightly_even_statementSpec
    {q k : ℕ} {C : PaperChoiceRule α}
    (hk : 0 < k)
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hcons : paper_definition_consistency C)  : Prop :=
  ¬ paper_definition_tight_d_instability (2 * k) C

def paper_definition_waitlisted_setSpec [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Prop :=
  paper_waitlisted_set C X =
    X.biUnion (fun x => C (X.erase x) \ C X)

/-- Source-facing semantic target for `paper_general_variability_exactly_definition_statement`. -/
def paper_general_variability_exactly_definition_statementSpec [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α)  : Prop :=
  paper_definition_general_variability_exactly m C ↔
        (∀ X,
          (paper_definition_borderline_set C X).card ≤ m ∧
            (paper_definition_waitlisted_set C X).card ≤ m) ∧
          ((∃ X, (paper_definition_borderline_set C X).card = m) ∨
            ∃ X, (paper_definition_waitlisted_set C X).card = m)

/-- Source-facing semantic target for `paper_append_remove_variability_exact_equivalence_statement`. -/
def paper_append_remove_variability_exact_equivalence_statementSpec
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hcard : 2 * q ≤ Fintype.card α) : Prop :=
  paper_definition_general_variability_exactly m C ↔
        paper_definition_variability_exactly m C

/-- Source-facing semantic target for `paper_corrected_consistency_of_removable_sets_statement`. -/
def paper_corrected_consistency_of_removable_sets_statementSpec
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hsub : paper_definition_substitutability C)
    {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂)  : Prop :=
  paper_definition_borderline_set C X₁ =
        paper_definition_borderline_set C X₂

/-- Source-facing semantic target for `paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statement`. -/
def paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert_statementSpec
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_choice_function_feasible C)
    (haccept : paper_definition_q_acceptance q C)
    (hunstable : paper_definition_d_instability 1 C)
    (hvar : paper_definition_variability_exactly 1 C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X)  : Prop :=
  paper_definition_borderline_set C X =
        paper_definition_waitlisted_set C (insert x X)

/-- Source-facing semantic target for `paper_sequential_composition_substitutable_statement`. -/
def paper_sequential_composition_substitutable_statementSpec
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_choice_function_feasible C)
    (hsub : ∀ C ∈ Cs, paper_definition_substitutability C)  : Prop :=
  paper_definition_substitutability (paper_definition_sequential_composition Cs)

/-- Source-facing semantic target for `paper_sequential_additive_variability_bound_statement`. -/
def paper_sequential_additive_variability_bound_statementSpec
    [Fintype α] {qs ms : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hcapacity : List.Forall₂
      (fun q C =>
        paper_choice_function_feasible C ∧
          paper_definition_q_acceptance q C ∧
            paper_definition_d_instability 1 C)
      qs Cs)
    (hvariability : List.Forall₂
      (fun m C => paper_definition_variability_exactly m C)
      ms Cs)  : Prop :=
  paper_definition_variability_at_most
        ms.sum (paper_definition_sequential_composition Cs)

/-- Source-facing semantic target for `paper_lap_slot_below_definition_statement`. -/
def paper_lap_slot_below_definition_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s : σ) (x y : α)  : Prop :=
  paper_definition_lap_slot_below w s x y ↔ w x s < w y s

def paper_lap_same_slot_order_definition_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (s t : σ) : Prop :=
  LAP.Assignment.SameSlotOrder w s t ↔
    ∀ x y, (w x s < w y s ↔ w x t < w y t)

def paper_lap_model_definition_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (X : Finset α) (w : α → σ → ℝ) (A : LAP.Assignment α σ) : Prop :=
  lapModel X w A ↔
    paper_definition_lap_assignment_feasible X A ∧
      ∀ B : LAP.Assignment α σ,
        paper_definition_lap_assignment_feasible X B →
          LAP.Assignment.objective w B ≤ LAP.Assignment.objective w A

/-- Source-facing semantic target for `paper_lap_assignment_choice_formula_statement`. -/
def paper_lap_assignment_choice_formula_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) (X : Finset α) (x : α)  : Prop :=
  x ∈ paper_definition_lap_choice_rule select X ↔
        ∃ s : σ, (select X).matchSlot s = some x

/-- Source-facing semantic target for `paper_lap_assigned_strictly_outranks_rejected_statement`. -/
def paper_lap_assigned_strictly_outranks_rejected_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : LAP.Assignment.Rejected X A x)
    (hnoTies : LAP.Assignment.SlotNoTies w s)  : Prop :=
  paper_definition_lap_slot_below w s x y

/-- Source-facing semantic target for `paper_lap_strictly_higher_slot_applicant_assigned_statement`. -/
def paper_lap_strictly_higher_slot_applicant_assigned_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hobjective : paper_definition_lap_objective_optimal X w A)
    (hfill : paper_definition_lap_capacity_filling X A)
    (hassign : paper_definition_lap_assignment_feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hxX : x ∈ X)
    (hbelow : paper_definition_lap_slot_below w s y x)  : Prop :=
  paper_definition_lap_assigned A x

/-- Source-facing semantic target for `paper_lap_assignment_one_instability_statement`.
`operationalWeight` is the fixed generic refinement of the raw source score.
`hwell` asserts uniqueness only for this refined objective; it does not assert
that all raw-primary optima have one chosen set. -/
def paper_lap_assignment_one_instability_statementSpec
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {operationalWeight : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧
        LAP.Assignment.CapacityFilling X A ∧
          LAP.Assignment.ObjectiveOptimal X operationalWeight A ∧
            ∀ B : LAP.Assignment α σ,
              LAP.Assignment.Feasible X B →
                LAP.Assignment.CapacityFilling X B →
                  LAP.Assignment.ObjectiveOptimal X operationalWeight B →
                    B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies operationalWeight s)  : Prop :=
  paper_definition_d_instability 1
        (paperLAPChoiceRule operationalWeight hwell)

/-- Source-facing semantic target for
`paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statement`.
As above, `operationalWeight` is the fixed generic refinement used to select
one optimum from a raw-primary tie; `hwell` is not a uniqueness claim about
the raw-primary objective. -/
def paper_lap_assignment_slot_order_class_variability_of_unique_global_optima_statementSpec
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {operationalWeight : α → σ → ℝ}
    (hwell : ∀ X : Finset α, ∃ A : LAP.Assignment α σ,
      LAP.Assignment.Feasible X A ∧
        LAP.Assignment.CapacityFilling X A ∧
          LAP.Assignment.ObjectiveOptimal X operationalWeight A ∧
            ∀ B : LAP.Assignment α σ,
              LAP.Assignment.Feasible X B →
                LAP.Assignment.CapacityFilling X B →
                  LAP.Assignment.ObjectiveOptimal X operationalWeight B →
                    B.chosenSet = A.chosenSet)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies operationalWeight s)  : Prop := by
  classical
  exact ∀ X,
    (paper_definition_borderline_set (paperLAPChoiceRule operationalWeight hwell) X).card ≤
      ((Finset.univ : Finset σ).image (LAP.Assignment.slotOrderClass operationalWeight)).card

end PaperInterface
end DGD26AdmissionsPredictability
