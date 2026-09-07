import AppliedModelingLib.Foundations.Math.FiniteChoice
import DGD26AdmissionsPredictability.LAP
import DGD26AdmissionsPredictability.QRepresentativeConverseWork
import DGD26AdmissionsPredictability.TightExamples
import DGD26AdmissionsPredictability.ProgramClasses

/-!
# Paper-Facing Theorems: Capacity Constraints Make Admissions Processes Less Predictable

Implementation layer for the finite choice-function theory in Dong, Garg, and
Dean, "Capacity Constraints Make Admissions Processes Less Predictable".

The first proof slice covers the reusable base of the paper: q-acceptance,
choice distance, substitutability, monotonicity, independence, zero
instability, and the nontrivial-universe obstruction to zero instability under
capacity constraints.
-/

namespace DGD26AdmissionsPredictability

open AppliedModelingLib.FiniteChoice

variable {α : Type*} [DecidableEq α]

/-- Paper choice functions are finite choice rules. -/
abbrev PaperChoiceRule (α : Type*) [DecidableEq α] :=
  ChoiceRule α

/-- Source convention: a choice function only chooses applicants from the input set. -/
abbrev paper_feasible (C : PaperChoiceRule α) : Prop :=
  Feasible C

/-- Definition q-Acceptance. -/
abbrev paper_q_acceptant (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  QAcceptant q C

/-- Definition Choice Distance, in the exact displayed formula form. -/
abbrev paper_choiceDistance (C : PaperChoiceRule α) (X₁ X₂ : Finset α) : ℕ :=
  ((X₁ ∩ C X₂) \ C X₁).card + (C X₁ \ C X₂).card

/-- Definition d-Instability for one fresh added applicant. -/
abbrev paper_d_unstable (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  DUnstable d C

/-- Definition tight d-Instability. -/
abbrev paper_tightly_d_unstable (d : ℕ) (C : PaperChoiceRule α) : Prop :=
  TightlyDUnstable d C

/-- Appendix Definition 0-Instability over arbitrary nested applicant sets. -/
abbrev paper_zero_unstable (C : PaperChoiceRule α) : Prop :=
  ZeroUnstable C

/-- Definition Substitutability. -/
abbrev paper_substitutable (C : PaperChoiceRule α) : Prop :=
  Substitutable C

/-- Appendix Definition Monotonicity. -/
abbrev paper_monotonic (C : PaperChoiceRule α) : Prop :=
  Monotonic C

/-- Appendix Definition Consistency. -/
abbrev paper_consistent (C : PaperChoiceRule α) : Prop :=
  Consistent C

/-- Appendix Definition Independence. -/
abbrev paper_independent (C : PaperChoiceRule α) : Prop :=
  Independent C

/-- Definition total ordering over applicants. -/
abbrev paper_total_order (r : α → α → Prop) : Prop :=
  StrictTotalOrder r

/-- Definition q-Representativeness: admissions by one total priority order. -/
abbrev paper_q_representative (q : ℕ) (C : PaperChoiceRule α) : Prop :=
  QRepresentative q C

/-- Definition sequential composition of admissions queues. -/
abbrev paper_sequential_composition (Cs : List (PaperChoiceRule α)) :
    PaperChoiceRule α :=
  sequentialComposition Cs

/-- Definition borderline set: admits displaced by some added applicant. -/
abbrev paper_borderline_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  borderlineSet C X

/-- Appendix waitlisted set: rejections admitted after some removal. -/
abbrev paper_waitlisted_set [Fintype α]
    (C : PaperChoiceRule α) (X : Finset α) : Finset α :=
  waitlistedSet C X

/-- Main-text variability upper bound. -/
abbrev paper_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  VariabilityAtMost m C

/-- Main-text exact variability. -/
abbrev paper_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  VariabilityExactly m C

/-- The realized maximum borderline-set size on a finite applicant universe. -/
noncomputable def paperRealizedVariability [Fintype α]
    (C : PaperChoiceRule α) : ℕ :=
  (Finset.univ : Finset (Finset α)).sup fun X =>
    (paper_borderline_set C X).card

/-- Every finite choice rule attains its realized variability maximum. -/
theorem paper_variability_exactly_realized [Fintype α]
    (C : PaperChoiceRule α) :
    paper_variability_exactly (paperRealizedVariability C) C := by
  classical
  constructor
  · intro X
    exact Finset.le_sup (f := fun Y : Finset α =>
      (paper_borderline_set C Y).card) (Finset.mem_univ X)
  · have hnonempty : (Finset.univ : Finset (Finset α)).Nonempty :=
      ⟨∅, Finset.mem_univ ∅⟩
    obtain ⟨X, _hX, hmax⟩ :=
      Finset.exists_mem_eq_sup
        (Finset.univ : Finset (Finset α)) hnonempty
        (fun Y : Finset α => (paper_borderline_set C Y).card)
    exact ⟨X, hmax.symm⟩

/-- Nontriviality witness: some added applicant displaces an existing admit. -/
abbrev paper_has_displacement (C : PaperChoiceRule α) : Prop :=
  HasDisplacement C

/-- Appendix general variability upper bound. -/
abbrev paper_general_variability_at_most [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  GeneralVariabilityAtMost m C

/-- Appendix exact general variability. -/
abbrev paper_general_variability_exactly [Fintype α]
    (m : ℕ) (C : PaperChoiceRule α) : Prop :=
  GeneralVariabilityExactly m C

/-- The source choice-distance formula is definitionally the reusable library formula. -/
theorem paper_choiceDistance_eq_library
    (C : PaperChoiceRule α) (X₁ X₂ : Finset α) :
    choiceDistance C X₁ X₂ = paper_choiceDistance C X₁ X₂ := by
  rfl

/--
Appendix Lemma, Substitutability Term: substitutability is equivalent to the
first choice-distance term vanishing for every nested pair of applicant sets.
-/
theorem paper_substitutability_term
    (C : PaperChoiceRule α) :
    paper_substitutable C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        ((X₁ ∩ C X₂) \ C X₁).card = 0 := by
  simpa [paper_substitutable, choiceGainTerm] using
    substitutable_iff_choiceGainTerm_eq_zero C

/--
Appendix Lemma, Monotonicity Term: monotonicity is equivalent to the second
choice-distance term vanishing for every nested pair of applicant sets.
-/
theorem paper_monotonicity_term
    (C : PaperChoiceRule α) :
    paper_monotonic C ↔
      ∀ {X₁ X₂ : Finset α}, X₁ ⊆ X₂ →
        (C X₁ \ C X₂).card = 0 := by
  simpa [paper_monotonic, choiceLossTerm] using
    monotonic_iff_choiceLossTerm_eq_zero C

/--
Appendix Corollary Zero-Distance: zero instability is equivalent to being both
substitutable and monotonic.
-/
theorem paper_zero_distance_iff_substitutable_and_monotonic
    (C : PaperChoiceRule α) :
    paper_zero_unstable C ↔ paper_substitutable C ∧ paper_monotonic C := by
  simpa [paper_zero_unstable, paper_substitutable, paper_monotonic] using
    zeroUnstable_iff_substitutable_and_monotonic C

/--
Appendix Theorem, Independent Rules are Substitutable and Monotonic: under the
paper's feasibility convention, independence is equivalent to substitutability
plus monotonicity.
-/
theorem paper_independent_iff_substitutable_and_monotonic
    (C : PaperChoiceRule α) (hfeasible : paper_feasible C) :
    paper_independent C ↔ paper_substitutable C ∧ paper_monotonic C := by
  simpa [paper_independent, paper_substitutable, paper_monotonic, paper_feasible] using
    independent_iff_substitutable_and_monotonic_of_feasible C hfeasible

/--
Appendix corollary: under feasibility, independence is equivalent to zero
instability.
-/
theorem paper_independent_iff_zero_unstable
    (C : PaperChoiceRule α) (hfeasible : paper_feasible C) :
    paper_independent C ↔ paper_zero_unstable C := by
  simpa [paper_independent, paper_zero_unstable, paper_feasible] using
    independent_iff_zeroUnstable_of_feasible C hfeasible

/--
Appendix Theorem, Triangle Inequality: choice distance is subadditive along
nested applicant pools.
-/
theorem paper_choice_distance_triangle
    (C : PaperChoiceRule α) {X₁ X₂ X₃ : Finset α}
    (h₁₂ : X₁ ⊆ X₂) (h₂₃ : X₂ ⊆ X₃) :
    paper_choiceDistance C X₁ X₃ ≤
      paper_choiceDistance C X₁ X₂ + paper_choiceDistance C X₂ X₃ := by
  simpa [paper_choiceDistance] using choiceDistance_triangle C h₁₂ h₂₃

/--
Triangle-inequality consequence: a d-unstable choice function changes at most
`d` times the number of newly added applicants when expanding a pool.
-/
theorem paper_choice_distance_multi_add_bound
    {d : ℕ} {C : PaperChoiceRule α}
    (hunstable : paper_d_unstable d C)
    (X S : Finset α) :
    paper_choiceDistance C X (X ∪ S) ≤ d * (S \ X).card := by
  simpa [paper_choiceDistance] using
    choiceDistance_union_le_card_sdiff_mul_of_dUnstable
      (C := C) hunstable X S

/--
Appendix Theorem, BoundedDistance: every q-acceptant substitutable choice
function is consistent.
-/
theorem paper_q_acceptant_substitutable_consistent
    {q : ℕ} {C : PaperChoiceRule α}
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C) :
    paper_consistent C := by
  intro X₁ X₂ hchosen_subset hsubset
  exact consistent_of_qAcceptant_of_substitutable
    (C := C) haccept hsub hchosen_subset hsubset

/--
Corrected Appendix Lemma, Consistency of Removable Sets: for feasible
q-acceptant substitutable choice functions, if two pools induce the same chosen
set, then they have the same borderline set.
-/
theorem paper_corrected_consistency_of_removable_sets
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C)
    {X₁ X₂ : Finset α}
    (hchoice : C X₁ = C X₂) :
    paper_borderline_set C X₁ = paper_borderline_set C X₂ := by
  exact borderlineSet_eq_of_choice_eq_of_substitutable
    (C := C) hfeasible haccept hsub hchoice

/--
Append/remove exchange helper: a waitlisted witness is an exact one-for-one
replacement in a feasible q-acceptant substitutable rule.
-/
theorem paper_waitlisted_witness_exact_exchange
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C)
    {X : Finset α} {x y : α}
    (hxX : x ∈ X)
    (hy : y ∈ C (X.erase x) \ C X) :
    x ∈ C X ∧ (C X).card = q ∧
      C (X.erase x) = insert y ((C X).erase x) := by
  exact choice_erase_eq_insert_erase_choice_of_waitlisted_witness
    (C := C) hfeasible haccept hsub hxX hy

/--
Append/remove batch helper: if a finite family of waitlisted applicants is
matched injectively to currently chosen applicants and each individual removal
performs the expected one-for-one exchange, then all of those waitlisted
applicants are borderline after removing the matched chosen applicants.
-/
theorem paper_waitlisted_family_subset_borderline_after_matched_removals
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C)
    {X W : Finset α} {mate : α → α}
    (hcardCX : (C X).card = q)
    (hWsubset : W ⊆ X \ C X)
    (hmate_chosen : ∀ y, y ∈ W → mate y ∈ C X)
    (hmate_inj : ∀ {y z}, y ∈ W → z ∈ W → mate y = mate z → y = z)
    (hmatch :
      ∀ y, y ∈ W →
        C (X.erase (mate y)) = insert y ((C X).erase (mate y))) :
    W ⊆ paper_borderline_set C (X \ W.image mate) := by
  exact waitlisted_family_subset_borderlineSet_of_exchange_matching
    (C := C) hfeasible haccept hsub hcardCX hWsubset hmate_chosen
    hmate_inj hmatch

/--
Append/remove cardinal bridge: every waitlisted set has some borderline set at
least as large.
-/
theorem paper_waitlisted_set_card_le_some_borderline_set_card
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C)
    (X : Finset α) :
    ∃ Y : Finset α,
      (paper_waitlisted_set C X).card ≤ (paper_borderline_set C Y).card := by
  exact waitlistedSet_card_le_some_borderlineSet_card
    (C := C) hfeasible haccept hsub X

/--
Append/remove theorem in threshold form: for feasible q-acceptant 1-unstable
rules, bounding the paper's borderline sets is equivalent to bounding the
appendix's combined borderline/waitlisted variability.
-/
theorem paper_append_remove_variability_at_most_equivalence
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C) :
    paper_general_variability_at_most m C ↔ paper_variability_at_most m C := by
  exact generalVariabilityAtMost_iff_variabilityAtMost_of_feasible_of_qAcceptant_of_dUnstable_one
    (C := C) hfeasible haccept hunstable

/--
Append/remove theorem in exact form: for feasible q-acceptant 1-unstable rules,
main-text exact variability equals appendix exact general variability.
-/
theorem paper_append_remove_variability_exact_equivalence
    [Fintype α] {m q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C) :
    paper_general_variability_exactly m C ↔ paper_variability_exactly m C := by
  exact generalVariabilityExactly_iff_variabilityExactly_of_feasible_of_qAcceptant_of_dUnstable_one
    (C := C) hfeasible haccept hunstable

/--
Append/remove exchange helper: a borderline witness is an exact one-for-one
replacement in a feasible q-acceptant substitutable 1-unstable rule.
-/
theorem paper_borderline_witness_exact_exchange
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C)
    (hunstable : paper_d_unstable 1 C)
    {X : Finset α} {x y : α}
    (hx : x ∉ X)
    (hy : y ∈ C X \ C (insert x X)) :
    x ∈ C (insert x X) ∧ (C X).card = q ∧
      C (insert x X) = insert x ((C X).erase y) := by
  exact choice_insert_eq_insert_erase_choice_of_borderline_witness
    (C := C) hfeasible haccept hsub hunstable hx hy

/--
Appendix Lemma, Incompatibility of Monotonicity and q-Acceptance: under a
positive capacity and a pool larger than capacity, no feasible choice function
is both monotonic and q-acceptant.
-/
theorem paper_monotonicity_q_acceptance_incompatible
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hmono : paper_monotonic C)
    (haccept : paper_q_acceptant q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    False := by
  exact false_of_feasible_of_monotonic_of_qAcceptant_of_card_gt
    (C := C) hfeasible hmono haccept hqpos hUcard

/--
Appendix Lemma, Non-Substitutable Functions: non-substitutability has a
single-addition witness.
-/
theorem paper_non_substitutable_single_add
    (C : PaperChoiceRule α) (hnot : ¬ paper_substitutable C) :
    ∃ X x xstar,
      x ∉ X ∧ xstar ∈ X ∧ xstar ∈ C (insert x X) ∧ xstar ∉ C X := by
  exact exists_single_add_gain_of_not_substitutable C hnot

/--
Forward half of Appendix Theorem "Substitutability and 1-Instability are
Equivalent Under Capacity Constraints": feasible q-acceptance and
substitutability imply 1-instability.
-/
theorem paper_one_instability_of_q_acceptant_substitutable
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hsub : paper_substitutable C) :
    paper_d_unstable 1 C := by
  exact dUnstable_one_of_feasible_of_qAcceptant_of_substitutable
    (C := C) hfeasible haccept hsub

/--
Appendix Theorem "Substitutability and 1-Instability are Equivalent Under
Capacity Constraints": under feasibility and q-acceptance, substitutability is
equivalent to 1-instability.
-/
theorem paper_substitutability_iff_one_instability_of_q_acceptant
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C) :
    paper_substitutable C ↔ paper_d_unstable 1 C := by
  constructor
  · exact paper_one_instability_of_q_acceptant_substitutable
      (C := C) hfeasible haccept
  · intro hunstable
    exact substitutable_of_dUnstable_one_of_feasible_of_qAcceptant
      (C := C) hfeasible haccept hunstable

/--
Appendix Lemma, Calculating Instability: when `X` is already at capacity,
choice distance after adding one fresh applicant is twice the number of
displaced old choices, minus one exactly when the fresh applicant is chosen.
-/
theorem paper_calculating_instability
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} {x : α} (hcard : q ≤ X.card) (hx : x ∉ X) :
    paper_choiceDistance C X (insert x X) =
      if x ∈ C (insert x X) then
        2 * (C X \ C (insert x X)).card - 1
      else
        2 * (C X \ C (insert x X)).card := by
  simpa [paper_choiceDistance] using
    choiceDistance_insert_eq_if_mem
      (C := C) hfeasible haccept hcard hx

/--
Forward direction of the appendix even-instability theorem: if a fresh
applicant is not chosen but produces a positive choice distance, then the
choice function is inconsistent.
-/
theorem paper_inconsistent_of_positive_distance_and_fresh_not_chosen
    {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    {X : Finset α} {x : α}
    (hxNotChosen : x ∉ C (insert x X))
    (hpositive : 0 < paper_choiceDistance C X (insert x X)) :
    ¬ paper_consistent C := by
  exact not_consistent_of_choiceDistance_pos_of_fresh_not_chosen
    (C := C) hfeasible hxNotChosen
      (by
    simpa only [paper_choiceDistance, choiceDistance, choiceGainTerm,
      choiceLossTerm] using hpositive)

/-- Positive one-step distance forces the original pool to be at capacity. -/
theorem paper_capacity_reached_of_positive_insert_distance
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hpositive : 0 < paper_choiceDistance C X (insert x X)) :
    q ≤ X.card := by
  by_contra hnot
  have hlt : X.card < q := Nat.lt_of_not_ge hnot
  have hXeq : C X = X := by
    apply Finset.eq_of_subset_of_card_le (hfeasible X)
    rw [haccept X, Nat.min_eq_right (Nat.le_of_lt hlt)]
  have hInsertCard : (insert x X).card ≤ q := by
    rw [Finset.card_insert_of_notMem hx]
    omega
  have hInsertEq : C (insert x X) = insert x X := by
    apply Finset.eq_of_subset_of_card_le (hfeasible (insert x X))
    rw [haccept (insert x X), Nat.min_eq_right hInsertCard]
  have hzero : paper_choiceDistance C X (insert x X) = 0 := by
    simp [paper_choiceDistance, hXeq, hInsertEq]
  omega

/--
Exact forward direction of the source's even-instability theorem: a positive,
even one-step choice distance makes a feasible q-acceptant rule inconsistent.
The parity equation derives that the fresh applicant was not selected.
-/
theorem paper_inconsistent_of_positive_even_insert_distance
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hpositive : 0 < paper_choiceDistance C X (insert x X))
    (heven : ∃ k, paper_choiceDistance C X (insert x X) = 2 * k) :
    ¬ paper_consistent C := by
  have hcard : q ≤ X.card :=
    paper_capacity_reached_of_positive_insert_distance
      hfeasible haccept hx hpositive
  have hxNotChosen : x ∉ C (insert x X) := by
    intro hxChosen
    rcases heven with ⟨k, hk⟩
    have hcalc := paper_calculating_instability
      (C := C) hfeasible haccept hcard hx
    rw [if_pos hxChosen] at hcalc
    omega
  exact paper_inconsistent_of_positive_distance_and_fresh_not_chosen
    hfeasible hxNotChosen hpositive

/--
Converse direction of the appendix even-instability theorem: if a feasible
q-acceptant choice function is inconsistent, then there is a single fresh
addition with positive even choice distance.
-/
theorem paper_exists_positive_even_distance_of_inconsistent
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hnot : ¬ paper_consistent C) :
    ∃ X x, x ∉ X ∧ 0 < paper_choiceDistance C X (insert x X) ∧
      ∃ k, paper_choiceDistance C X (insert x X) = 2 * k := by
  have hnot' : ¬ Consistent C := by
    simpa [paper_consistent] using hnot
  change ∃ X x, x ∉ X ∧ 0 < choiceDistance C X (insert x X) ∧
    ∃ k, choiceDistance C X (insert x X) = 2 * k
  exact
    exists_positive_even_choiceDistance_insert_of_not_consistent
      (C := C) hfeasible haccept hnot'

/--
Consistent q-acceptant choice functions cannot be tightly 2-unstable: any
two-instability bound improves to a one-instability bound.
-/
theorem paper_no_consistent_tightly_two_instability
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hcons : paper_consistent C)
    (hunstable : paper_d_unstable 2 C) :
    paper_d_unstable 1 C := by
  exact dUnstable_one_of_dUnstable_two_of_feasible_of_qAcceptant_of_consistent
    (C := C) hfeasible haccept hcons hunstable

/--
General even-instability corollary: a consistent q-acceptant choice function
cannot have a positive even tight instability bound, because every `2*k`
bound improves to `2*k - 1`.
-/
theorem paper_no_consistent_tightly_even_instability
    {q k : ℕ} {C : PaperChoiceRule α}
    (hk : 0 < k)
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hcons : paper_consistent C)
    (hunstable : paper_d_unstable (2 * k) C) :
    paper_d_unstable (2 * k - 1) C := by
  exact dUnstable_pred_of_dUnstable_even_of_feasible_of_qAcceptant_of_consistent
    (C := C) hk hfeasible haccept hcons hunstable

/-- Every q-acceptant choice function is at most `2q`-unstable. -/
theorem paper_q_acceptant_two_q_instability_bound
    {q : ℕ} {C : PaperChoiceRule α}
    (haccept : paper_q_acceptant q C) :
    paper_d_unstable (2 * q) C := by
  exact dUnstable_two_mul_of_qAcceptant haccept

/--
Generic tight maximal-even construction: two disjoint q-blocks plus one trigger
applicant define a feasible q-acceptant rule that is tightly `2*q`-unstable.
-/
theorem paper_tight_max_even_instability_family
    {q : ℕ} {A B : Finset α} {z : α}
    (hqpos : 0 < q) (hAcard : A.card = q) (hBcard : B.card = q)
    (hdisj : Disjoint A B) (hzA : z ∉ A) (hzB : z ∉ B) :
    paper_feasible (switchEvenChoice q A B z) ∧
      paper_q_acceptant q (switchEvenChoice q A B z) ∧
        paper_tightly_d_unstable (2 * q) (switchEvenChoice q A B z) := by
  exact
    ⟨switchEvenChoice_feasible hAcard hBcard,
      switchEvenChoice_qAcceptant hAcard hBcard,
      switchEvenChoice_tightlyDUnstable_two_mul
        hqpos hAcard hBcard hdisj hzA hzB⟩

/--
Generic tight maximal-odd construction: a complementary trigger group layered
over a stable fallback rule gives tight instability `2*q - 1`.
-/
theorem paper_tight_max_odd_instability_family
    {q : ℕ} {A B : Finset α} {z : α} {F : PaperChoiceRule α}
    (hAcard : A.card = q)
    (htrigger_card : (insert z B).card = q)
    (hdisj : Disjoint A (insert z B))
    (hFfeasible : paper_feasible F)
    (hFaccept : paper_q_acceptant q F)
    (hFconsistent : paper_consistent F)
    (hFbase : F (A ∪ B) = A)
    (hzA : z ∉ A) (hzB : z ∉ B) :
    paper_feasible (switchOddChoice q B z F) ∧
      paper_q_acceptant q (switchOddChoice q B z F) ∧
        paper_tightly_d_unstable (2 * q - 1) (switchOddChoice q B z F) := by
  exact
    ⟨switchOddChoice_feasible (q := q) hFfeasible,
      switchOddChoice_qAcceptant htrigger_card hFaccept,
      switchOddChoice_tightlyDUnstable_two_mul_sub_one
        hAcard htrigger_card hdisj hFfeasible hFaccept hFconsistent
        hFbase hzA hzB⟩

/--
Padded lower-even construction witness: for any `n ≤ q`, the ranked trigger
construction has a one-step choice-distance witness equal to `2*n`.
-/
theorem paper_padded_even_choiceDistance_witness
    {q n : ℕ} (hnq : n ≤ q) :
    paper_feasible (paddedEvenChoice q n) ∧
      paper_q_acceptant q (paddedEvenChoice q n) ∧
        paddedEvenZ q n ∉ paddedEvenBase q n ∧
          paper_choiceDistance (paddedEvenChoice q n) (paddedEvenBase q n)
            (insert (paddedEvenZ q n) (paddedEvenBase q n)) = 2 * n := by
  exact
    ⟨rankedTriggerSwitchChoice_feasible (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
        (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n),
      rankedTriggerSwitchChoice_qAcceptant (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
        (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n),
      paddedEven_fresh_not_mem_base q n,
      paddedEven_choiceDistance_witness hnq⟩

/--
Padded lower-even construction family: for every `0 < n ≤ q`, the ranked
trigger construction is tightly `2*n`-unstable.
-/
theorem paper_padded_even_tight_instability_family
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_feasible (paddedEvenChoice q n) ∧
      paper_q_acceptant q (paddedEvenChoice q n) ∧
        paper_tightly_d_unstable (2 * n) (paddedEvenChoice q n) := by
  exact
    ⟨rankedTriggerSwitchChoice_feasible (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
        (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n),
      rankedTriggerSwitchChoice_qAcceptant (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedEvenZ q n ∈ X)
        (rank₀ := paddedEvenRank₀ q n) (rank₁ := paddedEvenRank₁ q n),
      paddedEven_tightlyDUnstable hnpos hnq⟩

/--
Padded lower-odd construction witness: for `0 < n ≤ q`, the ranked trigger
construction has a one-step choice-distance witness equal to `2*n - 1`.
-/
theorem paper_padded_odd_choiceDistance_witness
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_feasible (paddedOddChoice q n) ∧
      paper_q_acceptant q (paddedOddChoice q n) ∧
        paddedOddZ q n ∉ paddedOddBase q n ∧
          paper_choiceDistance (paddedOddChoice q n) (paddedOddBase q n)
            (insert (paddedOddZ q n) (paddedOddBase q n)) = 2 * n - 1 := by
  exact
    ⟨rankedTriggerSwitchChoice_feasible (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
        (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n),
      rankedTriggerSwitchChoice_qAcceptant (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
        (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n),
      paddedOdd_fresh_not_mem_base q n,
      paddedOdd_choiceDistance_witness hnpos hnq⟩

/--
Padded lower-odd construction family: for every `0 < n ≤ q`, the ranked
trigger construction is tightly `2*n - 1`-unstable.
-/
theorem paper_padded_odd_tight_instability_family
    {q n : ℕ} (hnpos : 0 < n) (hnq : n ≤ q) :
    paper_feasible (paddedOddChoice q n) ∧
      paper_q_acceptant q (paddedOddChoice q n) ∧
        paper_tightly_d_unstable (2 * n - 1) (paddedOddChoice q n) := by
  exact
    ⟨rankedTriggerSwitchChoice_feasible (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
        (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n),
      rankedTriggerSwitchChoice_qAcceptant (q := q)
        (τ := fun X : Finset (Fin (q + n + 1)) => paddedOddZ q n ∈ X)
        (rank₀ := paddedOddRank₀ q n) (rank₁ := paddedOddRank₁ q n),
      paddedOdd_tightlyDUnstable hnpos hnq⟩

/-- Concrete q-acceptant choice function that is tightly 1-unstable. -/
theorem paper_tight_one_instability_example :
    paper_feasible tightOneChoice ∧
      paper_q_acceptant 1 tightOneChoice ∧
        paper_tightly_d_unstable 1 tightOneChoice := by
  exact ⟨tightOne_feasible, tightOne_qAcceptant, tightOne_tightlyDUnstable_one⟩

/-- Concrete q-acceptant choice function that is tightly 2-unstable. -/
theorem paper_tight_two_instability_example :
    paper_feasible tightTwoChoice ∧
      paper_q_acceptant 1 tightTwoChoice ∧
        paper_tightly_d_unstable 2 tightTwoChoice := by
  exact ⟨tightTwo_feasible, tightTwo_qAcceptant, tightTwo_tightlyDUnstable_two⟩

/-- Concrete q-acceptant choice function that is tightly 3-unstable. -/
theorem paper_tight_three_instability_example :
    paper_feasible tightThreeChoice ∧
      paper_q_acceptant 2 tightThreeChoice ∧
        paper_tightly_d_unstable 3 tightThreeChoice := by
  exact ⟨tightThree_feasible, tightThree_qAcceptant, tightThree_tightlyDUnstable_three⟩

/-- Concrete q-acceptant choice function that is tightly 4-unstable. -/
theorem paper_tight_four_instability_example :
    paper_feasible tightFourChoice ∧
      paper_q_acceptant 2 tightFourChoice ∧
        paper_tightly_d_unstable 4 tightFourChoice := by
  exact ⟨tightFour_feasible, tightFour_qAcceptant, tightFour_tightlyDUnstable_four⟩

/-- Concrete q-acceptant choice function that is tightly 5-unstable. -/
theorem paper_tight_five_instability_example :
    paper_feasible tightFiveChoice ∧
      paper_q_acceptant 3 tightFiveChoice ∧
        paper_tightly_d_unstable 5 tightFiveChoice := by
  exact ⟨tightFive_feasible, tightFive_qAcceptant, tightFive_tightlyDUnstable_five⟩

/-- A q-representative choice function is q-acceptant by definition. -/
theorem paper_q_representative_q_acceptant
    {q : ℕ} {C : PaperChoiceRule α}
    (hrep : paper_q_representative q C) :
    paper_q_acceptant q C := by
  exact hrep.qAcceptant

/-- A feasible q-representative choice function is substitutable. -/
theorem paper_q_representative_substitutable
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C) :
    paper_substitutable C := by
  exact substitutable_of_feasible_of_qRepresentative
    (C := C) hfeasible hrep

/-- A feasible q-representative choice function is 1-unstable. -/
theorem paper_q_representative_one_instability
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C) :
    paper_d_unstable 1 C := by
  exact dUnstable_one_of_feasible_of_qRepresentative
    (C := C) hfeasible hrep

/-- A q-representative rule with a real displacement is tightly 1-unstable. -/
theorem paper_q_representative_tightly_one_instability
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C)
    (hwitness : paper_has_displacement C) :
    paper_tightly_d_unstable 1 C := by
  exact tightlyDUnstable_one_of_feasible_of_qRepresentative_of_hasDisplacement
    (C := C) hfeasible hrep hwitness

/-- A feasible q-representative choice function has variability at most one. -/
theorem paper_q_representative_variability_at_most_one
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C) :
    paper_variability_at_most 1 C := by
  exact variabilityAtMost_one_of_feasible_of_qRepresentative
    (C := C) hfeasible hrep

/--
Converse direction of the q-representative characterization: under feasibility,
q-acceptance, 1-instability, and variability at most one force a single
priority-order representation.
-/
theorem paper_q_representative_of_q_acceptant_one_instability_variability
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C)
    (hvar : paper_variability_at_most 1 C) :
    paper_q_representative q C := by
  exact
    AppliedModelingLib.FiniteChoice.QRepresentativeConverseWork.qRepresentative_of_feasible_qAcceptant_dUnstable_one_variabilityAtMost_one
      (C := C) hfeasible haccept hunstable hvar

/--
Appendix q-representative characterization: under feasibility, a choice rule is
q-representative iff it is q-acceptant, 1-unstable, and has variability at
most one.
-/
theorem paper_q_representative_iff_q_acceptant_one_instability_variability
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C) :
    paper_q_representative q C ↔
      paper_q_acceptant q C ∧ paper_d_unstable 1 C ∧
        paper_variability_at_most 1 C := by
  constructor
  · intro hrep
    exact
      ⟨paper_q_representative_q_acceptant hrep,
        paper_q_representative_one_instability hfeasible hrep,
        paper_q_representative_variability_at_most_one hfeasible hrep⟩
  · intro h
    exact
      paper_q_representative_of_q_acceptant_one_instability_variability
        hfeasible h.1 h.2.1 h.2.2

/--
A feasible q-representative choice function has general variability at most
one: both its borderline and waitlisted sets have size at most one.
-/
theorem paper_q_representative_general_variability_at_most_one
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C) :
    paper_general_variability_at_most 1 C := by
  exact generalVariabilityAtMost_one_of_feasible_of_qRepresentative
    (C := C) hfeasible hrep

/--
Under the paper's one-variable characterization hypotheses, the appendix
general variability definition is also bounded by one.
-/
theorem paper_acceptant_one_instability_variability_general_variability_at_most_one
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C)
    (hvar : paper_variability_at_most 1 C) :
    paper_general_variability_at_most 1 C := by
  exact
    (paper_append_remove_variability_at_most_equivalence
      (C := C) hfeasible haccept hunstable).2 hvar

/--
A feasible q-representative choice function has exact general variability one
whenever there is an actual displacement.
-/
theorem paper_q_representative_general_variability_exactly_one_of_displacement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C)
    (hwitness : paper_has_displacement C) :
    paper_general_variability_exactly 1 C := by
  exact generalVariabilityExactly_one_of_feasible_of_qRepresentative_of_hasDisplacement
    (C := C) hfeasible hrep hwitness

/--
Under the paper's one-variable characterization hypotheses, a real
displacement gives exact appendix general variability one.
-/
theorem paper_acceptant_one_instability_variability_general_variability_exactly_one_of_displacement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C)
    (hvar : paper_variability_at_most 1 C)
    (hwitness : paper_has_displacement C) :
    paper_general_variability_exactly 1 C := by
  have hexact : paper_variability_exactly 1 C :=
    variabilityExactly_one_of_atMost_one_of_hasDisplacement
      hvar hwitness
  exact
    (paper_append_remove_variability_exact_equivalence
      (C := C) hfeasible haccept hunstable).2 hexact

/--
A feasible q-representative choice function has exact variability one whenever
there is an actual displacement.
-/
theorem paper_q_representative_variability_exactly_one_of_displacement
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C)
    (hwitness : paper_has_displacement C) :
    paper_variability_exactly 1 C := by
  exact variabilityExactly_one_of_feasible_of_qRepresentative_of_hasDisplacement
    (C := C) hfeasible hrep hwitness

/--
Any feasible positive-capacity choice rule on a strictly larger finite
applicant universe has a genuine one-step displacement. This supplies the
nondegeneracy step omitted by the source's exact-variability statement.
-/
theorem paper_has_displacement_of_feasible_q_acceptant_nontrivial
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_has_displacement C := by
  classical
  have hqUniv : q ≤ (Finset.univ : Finset α).card := by
    simpa using Nat.le_of_lt hqlt
  have hCunivCard : (C (Finset.univ : Finset α)).card = q := by
    rw [haccept]
    exact Nat.min_eq_left hqUniv
  have hCunivNonempty : (C (Finset.univ : Finset α)).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty, Finset.card_empty] at hCunivCard
    omega
  rcases hCunivNonempty with ⟨x, hxChosen⟩
  let X : Finset α := Finset.univ.erase x
  have hxNotX : x ∉ X := by
    simp [X]
  have hxNotChosenX : x ∉ C X := by
    intro hx
    exact hxNotX (hfeasible X hx)
  have hXcard : X.card + 1 = Fintype.card α := by
    simp [X]
    omega
  have hqX : q ≤ X.card := by
    omega
  have hCXCard : (C X).card = q := by
    rw [haccept]
    exact Nat.min_eq_left hqX
  have hxDiff : x ∈ C (Finset.univ : Finset α) \ C X := by
    exact Finset.mem_sdiff.mpr ⟨hxChosen, hxNotChosenX⟩
  obtain ⟨y, hyDiff⟩ :=
    exists_mem_sdiff_of_card_eq_of_mem_sdiff
      (A := C X) (B := C (Finset.univ : Finset α))
      (by omega) hxDiff
  refine ⟨X, x, y, hxNotX, (Finset.mem_sdiff.mp hyDiff).1, ?_⟩
  have hInsert : insert x X = (Finset.univ : Finset α) := by
    ext z
    by_cases hzx : z = x
    · simp [hzx]
    · simp [X]
  simpa [hInsert] using (Finset.mem_sdiff.mp hyDiff).2

/--
Source-corrected exact-one statement: a feasible q-representative rule has
exact variability one at positive, nontrivial capacity. The source omits these
necessary degeneracy exclusions.
-/
theorem paper_q_representative_variability_exactly_one_nontrivial
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_variability_exactly 1 C := by
  exact paper_q_representative_variability_exactly_one_of_displacement
    (C := C) hfeasible hrep
    (paper_has_displacement_of_feasible_q_acceptant_nontrivial
      hfeasible hrep.qAcceptant hqpos hqlt)

/--
Source-corrected exact characterization: on a positive, nontrivial finite
universe, q-representativeness is equivalent to q-acceptance, 1-instability,
and exact variability one.
-/
theorem paper_q_representative_iff_q_acceptant_one_instability_exact_variability
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_q_representative q C ↔
      paper_q_acceptant q C ∧ paper_d_unstable 1 C ∧
        paper_variability_exactly 1 C := by
  constructor
  · intro hrep
    exact ⟨hrep.qAcceptant,
      paper_q_representative_one_instability hfeasible hrep,
      paper_q_representative_variability_exactly_one_nontrivial
        hfeasible hrep hqpos hqlt⟩
  · rintro ⟨haccept, hunstable, hexact⟩
    exact paper_q_representative_of_q_acceptant_one_instability_variability
      hfeasible haccept hunstable hexact.1

/--
Under the source's standing q-acceptance and 1-instability conditions, exact
variability one is equivalent to representation by a single total order.
-/
theorem paper_variability_exactly_one_iff_q_representative
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_variability_exactly 1 C ↔ paper_q_representative q C := by
  constructor
  · intro hexact
    exact paper_q_representative_of_q_acceptant_one_instability_variability
      hfeasible haccept hunstable hexact.1
  · intro hrep
    exact paper_q_representative_variability_exactly_one_nontrivial
      hfeasible hrep hqpos hqlt

/-- Below capacity, feasibility and q-acceptance force the rule to choose all offers. -/
theorem paper_choice_eq_self_of_card_le_capacity
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} (hcard : X.card ≤ q) :
    C X = X := by
  apply Finset.eq_of_subset_of_card_le (hfeasible X)
  rw [haccept X, Nat.min_eq_right hcard]

/-- A pool strictly below capacity has no borderline applicants. -/
theorem paper_borderline_set_eq_empty_of_card_lt_capacity
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} (hcard : X.card < q) :
    paper_borderline_set C X = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro y hy
  rw [paper_borderline_set, borderlineSet] at hy
  rcases Finset.mem_biUnion.mp hy with ⟨z, _hz, hyDiff⟩
  have hXeq : C X = X :=
    paper_choice_eq_self_of_card_le_capacity hfeasible haccept
      (Nat.le_of_lt hcard)
  have hInsertCard : (insert z X).card ≤ q := by
    by_cases hzX : z ∈ X
    · rw [Finset.insert_eq_of_mem hzX]
      exact Nat.le_of_lt hcard
    · rw [Finset.card_insert_of_notMem hzX]
      omega
  have hInsertEq : C (insert z X) = insert z X :=
    paper_choice_eq_self_of_card_le_capacity hfeasible haccept hInsertCard
  rw [hXeq, hInsertEq] at hyDiff
  exact (Finset.mem_sdiff.mp hyDiff).2
    (Finset.mem_insert_of_mem (Finset.mem_sdiff.mp hyDiff).1)

/-- A pool at or below capacity has no waitlisted applicants. -/
theorem paper_waitlisted_set_eq_empty_of_card_le_capacity
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    {X : Finset α} (hcard : X.card ≤ q) :
    paper_waitlisted_set C X = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro y hy
  rw [paper_waitlisted_set, waitlistedSet] at hy
  rcases Finset.mem_biUnion.mp hy with ⟨z, hzX, hyDiff⟩
  have hXeq : C X = X :=
    paper_choice_eq_self_of_card_le_capacity hfeasible haccept hcard
  have hEraseCard : (X.erase z).card ≤ q :=
    (Finset.card_le_card (Finset.erase_subset z X)).trans hcard
  have hEraseEq : C (X.erase z) = X.erase z :=
    paper_choice_eq_self_of_card_le_capacity hfeasible haccept hEraseCard
  rw [hEraseEq, hXeq] at hyDiff
  exact (Finset.mem_sdiff.mp hyDiff).2
    (Finset.erase_subset z X (Finset.mem_sdiff.mp hyDiff).1)

/--
For a feasible q-representative rule, a changing fresh insertion has the same
borderline set before insertion as waitlisted set after insertion. Below
capacity both sets are empty; at capacity the ranking argument applies.
-/
theorem paper_q_representative_borderline_eq_waitlisted_after_changing_insert
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X) :
    paper_borderline_set C X = paper_waitlisted_set C (insert x X) := by
  by_cases hcard : q ≤ X.card
  · exact
      borderlineSet_eq_waitlistedSet_insert_of_feasible_of_qRepresentative_of_choice_ne
        (C := C) hfeasible hrep hx hcard hchange
  · have hlt : X.card < q := Nat.lt_of_not_ge hcard
    have hInsertCard : (insert x X).card ≤ q := by
      rw [Finset.card_insert_of_notMem hx]
      omega
    rw [paper_borderline_set_eq_empty_of_card_lt_capacity
          hfeasible hrep.qAcceptant hlt,
      paper_waitlisted_set_eq_empty_of_card_le_capacity
          hfeasible hrep.qAcceptant hInsertCard]

/--
Ranking-m bridge under the paper's characterization hypotheses: feasibility,
q-acceptance, 1-instability, and variability at most one imply the
q-representative insert/remove equality.
-/
theorem paper_acceptant_one_instability_variability_borderline_eq_waitlisted_after_changing_insert
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hunstable : paper_d_unstable 1 C)
    (hvar : paper_variability_at_most 1 C)
    {X : Finset α} {x : α}
    (hx : x ∉ X)
    (hchange : C (insert x X) ≠ C X) :
    paper_borderline_set C X = paper_waitlisted_set C (insert x X) := by
  have hrep : paper_q_representative q C :=
    paper_q_representative_of_q_acceptant_one_instability_variability
      hfeasible haccept hunstable hvar
  exact
    paper_q_representative_borderline_eq_waitlisted_after_changing_insert
      (C := C) hfeasible hrep hx hchange

/-! ## Machine-learning representation models -/

/-- Binary choice label `C(X)_i`: one exactly for chosen applicants. -/
def paperChoiceLabel (C : PaperChoiceRule α) (X : Finset α) (x : α) : ℕ :=
  if x ∈ C X then 1 else 0

/-- The choice label is one exactly when the applicant is selected. -/
theorem paperChoiceLabel_eq_one_iff
    (C : PaperChoiceRule α) (X : Finset α) (x : α) :
    paperChoiceLabel C X x = 1 ↔ x ∈ C X := by
  simp [paperChoiceLabel]

/-- A pool-aware binary predictor, represented propositionally by its positive label. -/
abbrev PaperPoolPredictor (α : Type*) := Finset α → α → Prop

/--
An ML predictor represents a choice rule when it gives exactly the rule's
binary choice label for every offered applicant in every applicant pool.
-/
def paperRepresentsChoice
    (predicts : PaperPoolPredictor α) (C : PaperChoiceRule α) : Prop :=
  ∀ X x, x ∈ X → (predicts X x ↔ x ∈ C X)

/-- Pool-independent fixed-threshold prediction formula `1{s(x) ≥ t}`. -/
def paperFixedThresholdPredictor (score : α → ℝ) (threshold : ℝ) :
    PaperPoolPredictor α :=
  fun _X x => threshold ≤ score x

/-- The source's fixed-threshold classifier, viewed as a finite choice rule. -/
noncomputable def paperFixedThresholdChoice (score : α → ℝ) (threshold : ℝ) :
    PaperChoiceRule α :=
  fun X => X.filter fun x => threshold ≤ score x

/-- Exact displayed fixed-threshold formula for the induced choice rule. -/
theorem paperFixedThresholdChoice_mem_iff
    (score : α → ℝ) (threshold : ℝ) (X : Finset α) (x : α) :
    x ∈ paperFixedThresholdChoice score threshold X ↔
      x ∈ X ∧ paperFixedThresholdPredictor score threshold X x := by
  simp [paperFixedThresholdChoice, paperFixedThresholdPredictor]

/-- The fixed-threshold predictor represents its induced choice rule. -/
theorem paperFixedThresholdPredictor_represents
    (score : α → ℝ) (threshold : ℝ) :
    paperRepresentsChoice
      (paperFixedThresholdPredictor score threshold)
      (paperFixedThresholdChoice score threshold) := by
  intro X x hxX
  simp [paperFixedThresholdPredictor, paperFixedThresholdChoice, hxX]

/--
Any feasible choice rule represented by one fixed-score, fixed-threshold
predictor is exactly the induced fixed-threshold choice rule.
-/
theorem paper_choice_eq_fixed_threshold_of_representation
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hfeasible : paper_feasible C)
    (hrep : paperRepresentsChoice
      (paperFixedThresholdPredictor score threshold) C) :
    C = paperFixedThresholdChoice score threshold := by
  funext X
  ext x
  constructor
  · intro hxC
    have hxX : x ∈ X := hfeasible X hxC
    have hpredict : paperFixedThresholdPredictor score threshold X x :=
      (hrep X x hxX).mpr hxC
    exact Finset.mem_filter.mpr ⟨hxX, hpredict⟩
  · intro hxFixed
    have hmem := Finset.mem_filter.mp hxFixed
    exact (hrep X x hmem.1).mp hmem.2

/-- A fixed-threshold classifier only chooses offered applicants. -/
theorem paperFixedThresholdChoice_feasible
    (score : α → ℝ) (threshold : ℝ) :
    paper_feasible (paperFixedThresholdChoice score threshold) := by
  intro X x hx
  exact (Finset.mem_filter.mp hx).1

/-- Fixed-threshold decisions do not depend on the surrounding applicant pool. -/
theorem paperFixedThresholdChoice_independent
    (score : α → ℝ) (threshold : ℝ) :
    paper_independent (paperFixedThresholdChoice score threshold) := by
  intro x
  by_cases hx : threshold ≤ score x
  · left
    intro X hxX
    exact Finset.mem_filter.mpr ⟨hxX, hx⟩
  · right
    intro X _hxX
    simp [paperFixedThresholdChoice, hx]

/--
ML-representation proposition, independent-prediction side: the source's
fixed-score, fixed-threshold rule is zero-unstable.
-/
theorem paper_fixed_threshold_predictions_zero_unstable
    (score : α → ℝ) (threshold : ℝ) :
    paper_zero_unstable (paperFixedThresholdChoice score threshold) := by
  exact
    (paper_independent_iff_zero_unstable
      (paperFixedThresholdChoice score threshold)
      (paperFixedThresholdChoice_feasible score threshold)).mp
        (paperFixedThresholdChoice_independent score threshold)

/--
Source ML proposition in representation form: if one pool-independent
fixed-threshold predictor represents `C`, then `C` is 0-unstable.
-/
theorem paper_fixed_threshold_representation_zero_unstable
    {C : PaperChoiceRule α} (score : α → ℝ) (threshold : ℝ)
    (hfeasible : paper_feasible C)
    (hrep : paperRepresentsChoice
      (paperFixedThresholdPredictor score threshold) C) :
    paper_zero_unstable C := by
  rw [paper_choice_eq_fixed_threshold_of_representation
    score threshold hfeasible hrep]
  exact paper_fixed_threshold_predictions_zero_unstable score threshold

/--
Structural bridge used by the concrete fixed-threshold theorem: any feasible
choice rule whose decisions are independent of the applicant pool is
zero-unstable.
-/
theorem paper_independent_predictions_zero_unstable
    {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hind : paper_independent C) :
    paper_zero_unstable C := by
  exact (paper_independent_iff_zero_unstable C hfeasible).mp hind

/--
The source's cohort-dependent rank-threshold model. The injectivity premise is
the precise Lean form of the source proof's statement that scores embed
applicants in the reals; higher scores have higher priority.
-/
@[reducible] noncomputable def paperOrderByScore
    (score : α → ℝ) (hinjective : Function.Injective score) : LinearOrder α :=
  LinearOrder.lift' (α := α) (β := OrderDual ℝ)
    (fun a : α => OrderDual.toDual (score a))
    (by
      intro a b h
      exact hinjective h)

/-- Choose the top `q` applicants under the score-induced priority order. -/
noncomputable def paperRankThresholdChoice
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    PaperChoiceRule α :=
  letI : LinearOrder α := paperOrderByScore score hinjective
  linearTopQChoice q

/-- Pool-dependent top-`q` score predictor, i.e. `1{s(x) ≥ t_q(X)}`. -/
noncomputable def paperRankThresholdPredictor
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    PaperPoolPredictor α :=
  fun X x => x ∈ paperRankThresholdChoice q score hinjective X

/-- The cohort-dependent top-`q` score predictor represents its induced rule. -/
theorem paperRankThresholdPredictor_represents
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    paperRepresentsChoice
      (paperRankThresholdPredictor q score hinjective)
      (paperRankThresholdChoice q score hinjective) := by
  intro X x _hxX
  rfl

/-- A feasible rule represented by the top-`q` score predictor is its induced rule. -/
theorem paper_choice_eq_rank_threshold_of_representation
    {C : PaperChoiceRule α} (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score)
    (hfeasible : paper_feasible C)
    (hrep : paperRepresentsChoice
      (paperRankThresholdPredictor q score hinjective) C) :
    C = paperRankThresholdChoice q score hinjective := by
  funext X
  ext x
  constructor
  · intro hxC
    have hxX : x ∈ X := hfeasible X hxC
    exact (hrep X x hxX).mpr hxC
  · intro hxRank
    have hxX : x ∈ X := by
      classical
      unfold paperRankThresholdChoice at hxRank
      letI : LinearOrder α := paperOrderByScore score hinjective
      exact linearTopQChoice_feasible q X hxRank
    exact (hrep X x hxX).mp hxRank

/-- The source's rank-threshold choice rule is feasible. -/
theorem paperRankThresholdChoice_feasible
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    paper_feasible (paperRankThresholdChoice q score hinjective) := by
  classical
  unfold paperRankThresholdChoice
  letI : LinearOrder α := paperOrderByScore score hinjective
  exact linearTopQChoice_feasible (α := α) q

/-- The source's rank-threshold choice rule is represented by one priority order. -/
theorem paperRankThresholdChoice_q_representative
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score) :
    paper_q_representative q (paperRankThresholdChoice q score hinjective) := by
  classical
  unfold paperRankThresholdChoice
  letI : LinearOrder α := paperOrderByScore score hinjective
  exact linearTopQChoice_qRepresentative (α := α) q

/--
Order-statistic form of the cohort-dependent rank model: at positive capacity,
every pool admits exactly the applicants whose scores weakly exceed one
pool-specific threshold `t_q(X)`.
-/
theorem paperRankThresholdPredictor_threshold_formula
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hqpos : 0 < q) (X : Finset α) :
    ∃ threshold : ℝ, ∀ x ∈ X,
      (paperRankThresholdPredictor q score hinjective X x ↔
        threshold ≤ score x) := by
  classical
  by_cases hX : X.Nonempty
  · let C := paperRankThresholdChoice q score hinjective
    have hchoiceNonempty : (C X).Nonempty := by
      apply Finset.card_pos.mp
      rw [(paperRankThresholdChoice_q_representative
        q score hinjective).qAcceptant X]
      have hXcard : 0 < X.card := Finset.card_pos.mpr hX
      omega
    let chosenScores := (C X).image score
    have hscores : chosenScores.Nonempty := hchoiceNonempty.image _
    let threshold := chosenScores.min' hscores
    have hthresholdMem : threshold ∈ chosenScores :=
      chosenScores.min'_mem hscores
    rcases Finset.mem_image.mp hthresholdMem with ⟨y, hyChosen, hyScore⟩
    refine ⟨threshold, ?_⟩
    intro x hxX
    change (x ∈ C X ↔ threshold ≤ score x)
    constructor
    · intro hxChosen
      exact chosenScores.min'_le _
        (Finset.mem_image.mpr ⟨x, hxChosen, rfl⟩)
    · intro hscoreAtLeast
      by_contra hxNot
      letI : LinearOrder α := paperOrderByScore score hinjective
      have hyPriority : y < x := by
        dsimp [C] at hyChosen hxNot
        unfold paperRankThresholdChoice at hyChosen hxNot
        exact linearTopQChoice_priority q hyChosen hxX hxNot
      have hscoreStrict : score x < score y := by
        simpa [paperOrderByScore] using hyPriority
      rw [hyScore] at hscoreStrict
      exact (not_lt_of_ge hscoreAtLeast) hscoreStrict
  · refine ⟨0, ?_⟩
    intro x hxX
    exact False.elim (hX ⟨x, hxX⟩)

/--
Source-facing order-statistic form of the cohort-dependent rank model.  On a
nonempty pool large enough for capacity `q`, the threshold is an offered score
and exactly `q` offered scores weakly exceed it.
-/
theorem paperRankThresholdPredictor_order_statistic_formula
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hqpos : 0 < q) (X : Finset α) (hqcard : q ≤ X.card) :
    ∃ threshold : ℝ,
      threshold ∈ X.image score ∧
        (X.filter (fun x => threshold ≤ score x)).card = q ∧
          ∀ x ∈ X,
            (paperRankThresholdPredictor q score hinjective X x ↔
              threshold ≤ score x) := by
  classical
  let C := paperRankThresholdChoice q score hinjective
  have hXcard : 0 < X.card := lt_of_lt_of_le hqpos hqcard
  have hX : X.Nonempty := Finset.card_pos.mp hXcard
  have hchoiceNonempty : (C X).Nonempty := by
    apply Finset.card_pos.mp
    rw [(paperRankThresholdChoice_q_representative
      q score hinjective).qAcceptant X]
    omega
  let chosenScores := (C X).image score
  have hscores : chosenScores.Nonempty := hchoiceNonempty.image _
  let threshold := chosenScores.min' hscores
  have hthresholdMem : threshold ∈ chosenScores :=
    chosenScores.min'_mem hscores
  rcases Finset.mem_image.mp hthresholdMem with ⟨y, hyChosen, hyScore⟩
  have hyX : y ∈ X :=
    paperRankThresholdChoice_feasible q score hinjective X hyChosen
  have hformula : ∀ x ∈ X,
      (x ∈ C X ↔ threshold ≤ score x) := by
    intro x hxX
    constructor
    · intro hxChosen
      exact chosenScores.min'_le _
        (Finset.mem_image.mpr ⟨x, hxChosen, rfl⟩)
    · intro hscoreAtLeast
      by_contra hxNot
      letI : LinearOrder α := paperOrderByScore score hinjective
      have hyPriority : y < x := by
        dsimp [C] at hyChosen hxNot
        unfold paperRankThresholdChoice at hyChosen hxNot
        exact linearTopQChoice_priority q hyChosen hxX hxNot
      have hscoreStrict : score x < score y := by
        simpa [paperOrderByScore] using hyPriority
      rw [hyScore] at hscoreStrict
      exact (not_lt_of_ge hscoreAtLeast) hscoreStrict
  refine ⟨threshold, Finset.mem_image.mpr ⟨y, hyX, hyScore⟩, ?_, ?_⟩
  · have hfilter : X.filter (fun x => threshold ≤ score x) = C X := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · intro hx
        exact (hformula x hx.1).mpr hx.2
      · intro hx
        have hxX : x ∈ X :=
          paperRankThresholdChoice_feasible q score hinjective X hx
        exact ⟨hxX, (hformula x hxX).mp hx⟩
    rw [hfilter, (paperRankThresholdChoice_q_representative
      q score hinjective).qAcceptant X]
    exact Nat.min_eq_left hqcard
  · intro x hxX
    exact hformula x hxX

/--
ML-representation proposition, rank-threshold side: a feasible q-representative
rule is 1-unstable and has variability at most one.
-/
theorem paper_rank_threshold_one_instability_and_variability
    [Fintype α] {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (hrep : paper_q_representative q C) :
    paper_d_unstable 1 C ∧ paper_variability_at_most 1 C := by
  exact ⟨paper_q_representative_one_instability hfeasible hrep,
    paper_q_representative_variability_at_most_one hfeasible hrep⟩

/--
ML-representation proposition, rank-threshold side: the source's concrete
top-`q` score rule is 1-unstable and has variability at most one.
-/
theorem paper_score_rank_threshold_one_instability_and_variability
    [Fintype α] (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score) :
    paper_d_unstable 1 (paperRankThresholdChoice q score hinjective) ∧
      paper_variability_at_most 1
        (paperRankThresholdChoice q score hinjective) := by
  exact paper_rank_threshold_one_instability_and_variability
    (paperRankThresholdChoice_feasible q score hinjective)
    (paperRankThresholdChoice_q_representative q score hinjective)

/--
Source ML proposition in representation form: any feasible choice rule
represented by a top-`q` score predictor is 1-unstable and at most 1-variable.
-/
theorem paper_rank_threshold_representation_one_instability_and_variability
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_feasible C)
    (hrep : paperRepresentsChoice
      (paperRankThresholdPredictor q score hinjective) C) :
    paper_d_unstable 1 C ∧ paper_variability_at_most 1 C := by
  rw [paper_choice_eq_rank_threshold_of_representation
    q score hinjective hfeasible hrep]
  exact paper_score_rank_threshold_one_instability_and_variability
    q score hinjective

/--
At positive capacity below the finite universe size, the source's concrete
score-rank model is tightly 1-unstable and has exact variability one.
-/
theorem paper_score_rank_threshold_exact_one_nontrivial
    [Fintype α] (q : ℕ) (score : α → ℝ)
    (hinjective : Function.Injective score)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_tightly_d_unstable 1 (paperRankThresholdChoice q score hinjective) ∧
      paper_variability_exactly 1
        (paperRankThresholdChoice q score hinjective) := by
  have hfeasible := paperRankThresholdChoice_feasible q score hinjective
  have hrep := paperRankThresholdChoice_q_representative q score hinjective
  have hdisplacement :
      paper_has_displacement (paperRankThresholdChoice q score hinjective) :=
    paper_has_displacement_of_feasible_q_acceptant_nontrivial
      hfeasible hrep.qAcceptant hqpos hqlt
  exact ⟨paper_q_representative_tightly_one_instability
      hfeasible hrep hdisplacement,
    paper_q_representative_variability_exactly_one_nontrivial
      hfeasible hrep hqpos hqlt⟩

/--
Under the source's implicit nondegeneracy conditions, a represented top-`q`
score rule is tightly 1-unstable and exactly 1-variable.
-/
theorem paper_rank_threshold_representation_exact_one_nontrivial
    [Fintype α] {C : PaperChoiceRule α}
    (q : ℕ) (score : α → ℝ) (hinjective : Function.Injective score)
    (hfeasible : paper_feasible C)
    (hrep : paperRepresentsChoice
      (paperRankThresholdPredictor q score hinjective) C)
    (hqpos : 0 < q)
    (hqlt : q < Fintype.card α) :
    paper_tightly_d_unstable 1 C ∧ paper_variability_exactly 1 C := by
  rw [paper_choice_eq_rank_threshold_of_representation
    q score hinjective hfeasible hrep]
  exact paper_score_rank_threshold_exact_one_nontrivial
    q score hinjective hqpos hqlt

/--
Existence direction of the source ML proposition: every positive capacity has
a finite injectively scored cohort on which a rank-threshold model is tightly
1-unstable and exactly 1-variable.
-/
theorem paper_rank_threshold_can_represent_exact_one (q : ℕ) (hqpos : 0 < q) :
    ∃ (score : Fin (q + 1) → ℝ) (hinjective : Function.Injective score),
      paper_tightly_d_unstable 1
          (paperRankThresholdChoice q score hinjective) ∧
        paper_variability_exactly 1
          (paperRankThresholdChoice q score hinjective) := by
  let score : Fin (q + 1) → ℝ := fun a => a.val
  have hinjective : Function.Injective score := by
    intro a b hab
    apply Fin.ext
    change (a.val : ℝ) = (b.val : ℝ) at hab
    exact_mod_cast hab
  refine ⟨score, hinjective, ?_⟩
  exact paper_score_rank_threshold_exact_one_nontrivial
    q score hinjective hqpos (by simp)

/-- Sequential composition of feasible choice functions is feasible. -/
theorem paper_sequential_composition_feasible
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_feasible C) :
    paper_feasible (paper_sequential_composition Cs) := by
  exact feasible_sequentialComposition_of_forall_mem hfeasible

/--
Sequential composition of feasible q-acceptant queues is q-acceptant with
capacity equal to the sum of the stage capacities.
-/
theorem paper_sequential_composition_q_acceptant
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hstages : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_acceptant q C) qs Cs) :
    paper_q_acceptant qs.sum (paper_sequential_composition Cs) := by
  exact qAcceptant_sequentialComposition_of_forall₂_feasible_qAcceptant hstages

/--
Sequential composition of feasible substitutable choice functions is
substitutable.
-/
theorem paper_sequential_composition_substitutable
    {Cs : List (PaperChoiceRule α)}
    (hfeasible : ∀ C ∈ Cs, paper_feasible C)
    (hsub : ∀ C ∈ Cs, paper_substitutable C) :
    paper_substitutable (paper_sequential_composition Cs) := by
  exact substitutable_sequentialComposition_of_forall_mem hfeasible hsub

/--
Appendix additive variability theorem: sequential composition of feasible
q-acceptant 1-unstable stages has variability bounded by the sum of the stage
variability bounds.
-/
theorem paper_sequential_additive_variability_bound
    [Fintype α] {qms : List (ℕ × ℕ)} {Cs : List (PaperChoiceRule α)}
    (hstages : List.Forall₂
      (fun qm C =>
        paper_feasible C ∧ paper_q_acceptant qm.1 C ∧ paper_d_unstable 1 C ∧
          paper_variability_at_most qm.2 C)
      qms Cs) :
    paper_variability_at_most
      (qms.map Prod.snd).sum (paper_sequential_composition Cs) := by
  exact
    variabilityAtMost_sequentialComposition_of_forall₂_feasible_qAcceptant_dUnstable
      hstages

/--
Source-facing additive variability theorem with capacity and variability
ledgers exposed separately. This avoids making the paper-facing statement rely
on anonymous pair projections for stage data.
-/
theorem paper_sequential_additive_variability_bound_of_stage_lists
    [Fintype α] {qs ms : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hcapacity : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_acceptant q C ∧
        paper_d_unstable 1 C)
      qs Cs)
    (hvariability : List.Forall₂
      (fun m C => paper_variability_at_most m C)
      ms Cs) :
    paper_variability_at_most ms.sum (paper_sequential_composition Cs) := by
  let qms := qs.zip ms
  have hstages : List.Forall₂
      (fun qm C =>
        paper_feasible C ∧ paper_q_acceptant qm.1 C ∧ paper_d_unstable 1 C ∧
          paper_variability_at_most qm.2 C)
      qms Cs := by
    subst qms
    induction hcapacity generalizing ms with
    | nil =>
        cases hvariability
        exact List.Forall₂.nil
    | cons hcap _htail ih =>
        cases hvariability with
        | cons hvar hvar_tail =>
            exact List.Forall₂.cons ⟨hcap.1, hcap.2.1, hcap.2.2, hvar⟩
              (ih hvar_tail)
  have hsum : (qms.map Prod.snd).sum = ms.sum := by
    subst qms
    clear hstages
    induction hcapacity generalizing ms with
    | nil =>
        cases hvariability
        simp
    | cons _hcap _htail ih =>
        cases hvariability with
        | cons _hvar hvar_tail =>
            simp [ih hvar_tail]
  rw [← hsum]
  exact paper_sequential_additive_variability_bound hstages

/--
Main variability theorem, upper-bound direction: a sequential composition of
feasible single-order queues has variability at most the number of queues.
-/
theorem paper_sequential_q_representative_variability_at_most_length
    [Fintype α] {Cs : List (PaperChoiceRule α)}
    (hqueues : ∀ C ∈ Cs, ∃ q, paper_feasible C ∧ paper_q_representative q C) :
    paper_variability_at_most Cs.length (paper_sequential_composition Cs) := by
  exact variabilityAtMost_length_of_forall_mem_qRepresentative hqueues

/-- Helper: a q-representative queue ledger gives feasibility for every stage. -/
theorem forall_mem_feasible_of_forall₂_qRepresentative
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs) :
    ∀ C ∈ Cs, paper_feasible C := by
  intro D hD
  induction hqueues with
  | nil =>
      simp at hD
  | @cons q C qs Cs hhead _htail ih =>
      simp at hD
      rcases hD with rfl | hD
      · exact hhead.1
      · exact ih hD

/-- Helper: a q-representative queue ledger gives q-acceptance for every stage. -/
theorem forall₂_qAcceptant_of_forall₂_qRepresentative
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs) :
    List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_acceptant q C) qs Cs := by
  induction hqueues with
  | nil =>
      exact List.Forall₂.nil
  | cons hhead _htail ih =>
      exact List.Forall₂.cons ⟨hhead.1, hhead.2.qAcceptant⟩ ih

/-- Helper: a q-representative queue ledger gives substitutability for every stage. -/
theorem forall_mem_substitutable_of_forall₂_qRepresentative
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs) :
    ∀ C ∈ Cs, paper_substitutable C := by
  intro D hD
  induction hqueues with
  | nil =>
      simp at hD
  | @cons q C qs Cs hhead _htail ih =>
      simp at hD
      rcases hD with rfl | hD
      · exact paper_q_representative_substitutable hhead.1 hhead.2
      · exact ih hD

/-- Helper: a q-representative queue ledger gives the member-indexed queue premise. -/
theorem forall_mem_exists_qRepresentative_of_forall₂_qRepresentative
    {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs) :
    ∀ C ∈ Cs, ∃ q, paper_feasible C ∧ paper_q_representative q C := by
  intro D hD
  induction hqueues with
  | nil =>
      simp at hD
  | @cons q C qs Cs hhead _htail ih =>
      simp at hD
      rcases hD with rfl | hD
      · exact ⟨q, hhead⟩
      · exact ih hD

/--
Main sequential-queue package: a sequential composition of feasible
q-representative queues is feasible, q-acceptant at total capacity, 1-unstable,
and has variability at most the number of queues.
-/
theorem paper_sequential_q_representative_choice_properties
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs) :
    paper_feasible (paper_sequential_composition Cs) ∧
      paper_q_acceptant qs.sum (paper_sequential_composition Cs) ∧
        paper_d_unstable 1 (paper_sequential_composition Cs) ∧
          paper_variability_at_most Cs.length (paper_sequential_composition Cs) := by
  have hfeasible_all : ∀ C ∈ Cs, paper_feasible C :=
    forall_mem_feasible_of_forall₂_qRepresentative hqueues
  have hstageAccept : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_acceptant q C) qs Cs :=
    forall₂_qAcceptant_of_forall₂_qRepresentative hqueues
  have hsub_all : ∀ C ∈ Cs, paper_substitutable C :=
    forall_mem_substitutable_of_forall₂_qRepresentative hqueues
  have hqueues_mem :
      ∀ C ∈ Cs, ∃ q, paper_feasible C ∧ paper_q_representative q C :=
    forall_mem_exists_qRepresentative_of_forall₂_qRepresentative hqueues
  have hfeas_comp :
      paper_feasible (paper_sequential_composition Cs) :=
    paper_sequential_composition_feasible hfeasible_all
  have haccept_comp :
      paper_q_acceptant qs.sum (paper_sequential_composition Cs) :=
    paper_sequential_composition_q_acceptant hstageAccept
  have hsub_comp :
      paper_substitutable (paper_sequential_composition Cs) :=
    paper_sequential_composition_substitutable hfeasible_all hsub_all
  have hunstable_comp :
    paper_d_unstable 1 (paper_sequential_composition Cs) :=
    paper_one_instability_of_q_acceptant_substitutable
      hfeas_comp haccept_comp hsub_comp
  exact ⟨hfeas_comp, haccept_comp, hunstable_comp,
    paper_sequential_q_representative_variability_at_most_length hqueues_mem⟩

/--
Source-corrected main variability range: a nontrivial sequential composition
of `n` single-order queues realizes some variability `m` with `1 ≤ m ≤ n`.
-/
theorem paper_sequential_q_representative_variability_range
    [Fintype α] {qs : List ℕ} {Cs : List (PaperChoiceRule α)}
    (hqueues : List.Forall₂
      (fun q C => paper_feasible C ∧ paper_q_representative q C) qs Cs)
    (hqpos : 0 < qs.sum)
    (hqlt : qs.sum < Fintype.card α) :
    ∃ m, 1 ≤ m ∧ m ≤ Cs.length ∧
      paper_variability_exactly m (paper_sequential_composition Cs) := by
  let C := paper_sequential_composition Cs
  let m := paperRealizedVariability C
  have hprops := paper_sequential_q_representative_choice_properties hqueues
  have hexact : paper_variability_exactly m C :=
    paper_variability_exactly_realized C
  have hdisp : paper_has_displacement C :=
    paper_has_displacement_of_feasible_q_acceptant_nontrivial
      hprops.1 hprops.2.1 hqpos hqlt
  rcases hdisp with ⟨X, x, y, hxX, hyOld, hyNew⟩
  have hyBorder : y ∈ paper_borderline_set C X := by
    rw [paper_borderline_set, borderlineSet]
    exact Finset.mem_biUnion.mpr
      ⟨x, Finset.mem_univ x,
        Finset.mem_sdiff.mpr ⟨hyOld, hyNew⟩⟩
  have hmpos : 1 ≤ m := by
    have hcardpos : 0 < (paper_borderline_set C X).card :=
      Finset.card_pos.mpr ⟨y, hyBorder⟩
    exact hcardpos.trans_le (hexact.1 X)
  obtain ⟨Y, hYeq⟩ := hexact.2
  have hmle : m ≤ Cs.length := by
    rw [← hYeq]
    exact hprops.2.2.2 Y
  exact ⟨m, hmpos, hmle, hexact⟩

/-! ## Abstract source queue procedures -/

/-- Abstract one-queue procedure for the Screened/Open source class. -/
abbrev paperScreenedOpenProgramChoice : PaperChoiceRule (Fin 2) :=
  ProgramClasses.choice 1

/-- Abstract two-queue procedure for the Screened/Open-with-DIA source class. -/
abbrev paperScreenedOpenDIAProgramChoice : PaperChoiceRule (Fin 4) :=
  ProgramClasses.choice 2

/-- Abstract three-queue procedure for the Educational Option source class. -/
abbrev paperEducationalOptionProgramChoice : PaperChoiceRule (Fin 6) :=
  ProgramClasses.choice 3

/-- Abstract six-queue procedure for the Educational Option-with-DIA source class. -/
abbrev paperEducationalOptionDIAProgramChoice : PaperChoiceRule (Fin 12) :=
  ProgramClasses.choice 6

/-- The abstract Screened/Open procedure is 1-unstable and exactly 1-variable. -/
theorem paper_screened_open_program_properties :
    paper_feasible paperScreenedOpenProgramChoice ∧
      paper_q_acceptant 1 paperScreenedOpenProgramChoice ∧
      paper_d_unstable 1 paperScreenedOpenProgramChoice ∧
      paper_variability_exactly 1 paperScreenedOpenProgramChoice := by
  exact ProgramClasses.one_queue_properties

/-- The abstract Screened/Open-with-DIA procedure is 1-unstable and exactly 2-variable. -/
theorem paper_screened_open_dia_program_properties :
    paper_feasible paperScreenedOpenDIAProgramChoice ∧
      paper_q_acceptant 2 paperScreenedOpenDIAProgramChoice ∧
      paper_d_unstable 1 paperScreenedOpenDIAProgramChoice ∧
      paper_variability_exactly 2 paperScreenedOpenDIAProgramChoice := by
  exact ProgramClasses.two_queue_properties

/-- The abstract Educational Option procedure is 1-unstable and exactly 3-variable. -/
theorem paper_educational_option_program_properties :
    paper_feasible paperEducationalOptionProgramChoice ∧
      paper_q_acceptant 3 paperEducationalOptionProgramChoice ∧
      paper_d_unstable 1 paperEducationalOptionProgramChoice ∧
      paper_variability_exactly 3 paperEducationalOptionProgramChoice := by
  exact ProgramClasses.three_queue_properties

/-- The abstract Educational Option-with-DIA procedure is 1-unstable and exactly 6-variable. -/
theorem paper_educational_option_dia_program_properties :
    paper_feasible paperEducationalOptionDIAProgramChoice ∧
      paper_q_acceptant 6 paperEducationalOptionDIAProgramChoice ∧
      paper_d_unstable 1 paperEducationalOptionDIAProgramChoice ∧
      paper_variability_exactly 6 paperEducationalOptionDIAProgramChoice := by
  exact ProgramClasses.six_queue_properties

/-- All four abstract source queue procedures satisfy 1-instability. -/
theorem paper_program_classes_one_instability :
    paper_d_unstable 1 paperScreenedOpenProgramChoice ∧
      paper_d_unstable 1 paperScreenedOpenDIAProgramChoice ∧
      paper_d_unstable 1 paperEducationalOptionProgramChoice ∧
      paper_d_unstable 1 paperEducationalOptionDIAProgramChoice := by
  exact ⟨paper_screened_open_program_properties.2.2.1,
    paper_screened_open_dia_program_properties.2.2.1,
    paper_educational_option_program_properties.2.2.1,
    paper_educational_option_dia_program_properties.2.2.1⟩

/--
An assignment selector that returns a feasible assignment for every applicant
pool induces a feasible finite choice function by taking the applicants assigned
to some slot.
-/
theorem paper_lap_assignment_selector_feasible_choice
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, LAP.Assignment.Feasible X (select X)) :
    paper_feasible (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact LAP.Assignment.feasible_choiceRuleOfAssignment hfeas

/--
Feasible capacity-filling assignment selectors induce q-acceptant choice rules
at capacity equal to the number of slots.
-/
theorem paper_lap_assignment_selector_q_acceptant
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {select : Finset α → LAP.Assignment α σ}
    (hfeas : ∀ X, LAP.Assignment.Feasible X (select X))
    (hfill : ∀ X, LAP.Assignment.CapacityFilling X (select X)) :
    paper_q_acceptant
      (Fintype.card σ) (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact LAP.Assignment.qAcceptant_choiceRuleOfAssignment_of_feasible_of_capacityFilling
    hfeas hfill

/--
LAP instability bridge: unique global-optimum selectors are 1-unstable once the
single-addition matching-exchange preservation certificate is proved.
-/
theorem paper_lap_assignment_selector_one_instability_of_exchange_preservation
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hpreserve : LAP.Assignment.SingleAddOldChosenPreservation w select) :
    paper_d_unstable 1 (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddOldChosenPreservation
      hselect hpreserve

/--
Lower-level LAP instability bridge: it suffices to repair each one-fresh
larger optimum into an old-pool optimum preserving the old chosen applicant.
-/
theorem paper_lap_assignment_selector_one_instability_of_exchange_repair
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hrepair : LAP.Assignment.SingleAddExchangeRepair w select) :
    paper_d_unstable 1 (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_singleAddExchangeRepair
      hselect hrepair

/--
Linear assignment instability: a selector returning unique finite global
optima induces a 1-unstable choice rule. The required single-addition exchange
repair is derived by the directed alternating-splice proof in `LAP.lean`.
-/
theorem paper_lap_assignment_selector_one_instability
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select) :
    paper_d_unstable 1 (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.dUnstable_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima
      hselect

/-- Choice rule induced by an operational LAP score. Its `w` argument is the
fixed generic refinement after raw-primary ties have been resolved. -/
noncomputable def paperLAPChoiceRule
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (w : α → σ → ℝ) (hwell : LAP.Assignment.WellPosedObjective w) :
    PaperChoiceRule α :=
  LAP.Assignment.choiceRuleOfAssignment
    (LAP.Assignment.canonicalOptimalAssignment w hwell)

/-- An operationally tie-broken finite LAP induces a 1-unstable choice rule.
The well-posedness premise is about the operational score, not raw-primary
uniqueness. -/
theorem paper_lap_well_posed_choice_one_instability
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} (hwell : LAP.Assignment.WellPosedObjective w) :
    paper_d_unstable 1 (paperLAPChoiceRule w hwell) := by
  exact paper_lap_assignment_selector_one_instability
    (LAP.Assignment.canonicalOptimalAssignment_selectsUniqueGlobalOptima hwell)

/-- A finite-slot assignment chooses no more applicants than there are slots. -/
theorem paper_lap_chosen_set_card_le_slots
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    (A : LAP.Assignment α σ) :
    A.chosenSet.card ≤ Fintype.card σ := by
  exact LAP.Assignment.chosenSet_card_le_slots A

/--
The borderline set of any assignment-induced choice rule is bounded by the
number of assignment slots.
-/
theorem paper_lap_assignment_selector_borderline_card_le_slots
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) (X : Finset α) :
    (paper_borderline_set
      (LAP.Assignment.choiceRuleOfAssignment select) X).card ≤ Fintype.card σ := by
  exact LAP.Assignment.borderlineSet_choiceRuleOfAssignment_card_le_slots select X

/-- Assignment-induced choice rules have variability at most the number of slots. -/
theorem paper_lap_assignment_selector_variability_at_most_slots
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    (select : Finset α → LAP.Assignment α σ) :
    paper_variability_at_most
      (Fintype.card σ) (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact LAP.Assignment.variabilityAtMost_choiceRuleOfAssignment_slots select

/--
One-order LAP variability: if all finite assignment slots induce the same
strict applicant order, unique global optima have variability at most one.
-/
theorem paper_lap_assignment_selector_variability_at_most_one_of_common_slot_order
    [Fintype α] [LinearOrder α]
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (horder : ∀ s a b, a < b ↔ w b s < w a s) :
    paper_variability_at_most 1
      (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.variabilityAtMost_one_choiceRuleOfAssignment_of_selectsUniqueGlobalOptima_of_common_slot_order
      hselect horder

/--
LAP distinct-ordering counting bridge: once borderline applicants are known to
inject into the supplied slot-order classes via their old assigned slots, the
assignment-induced choice rule has variability bounded by the number of those
classes.
-/
theorem paper_lap_assignment_selector_variability_at_most_slot_order_classes
    [Fintype α] {σ κ : Type*} [DecidableEq σ] [Fintype σ] [DecidableEq κ]
    {select : Finset α → LAP.Assignment α σ} {classOf : σ → κ}
    (hinj :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ paper_borderline_set
          (LAP.Assignment.choiceRuleOfAssignment select) X →
        z ∈ paper_borderline_set
          (LAP.Assignment.choiceRuleOfAssignment select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        classOf sy = classOf sz →
        y = z) :
    paper_variability_at_most
      ((Finset.univ : Finset σ).image classOf).card
      (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.variabilityAtMost_choiceRuleOfAssignment_of_borderline_slot_class_injective
      hinj

/--
Paper-shaped LAP distinct-ordering bridge: it is enough to prove that two
borderline applicants assigned to same-order slots are equal.
-/
theorem paper_lap_assignment_selector_variability_at_most_slot_order_classes_of_same_order_kernel
    [Fintype α] {σ κ : Type*} [DecidableEq σ] [Fintype σ] [DecidableEq κ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    {classOf : σ → κ}
    (hclass : ∀ {s t : σ}, classOf s = classOf t →
      LAP.Assignment.SameSlotOrder w s t)
    (hkernel :
      ∀ {X : Finset α} {y z : α} {sy sz : σ},
        y ∈ paper_borderline_set
          (LAP.Assignment.choiceRuleOfAssignment select) X →
        z ∈ paper_borderline_set
          (LAP.Assignment.choiceRuleOfAssignment select) X →
        (select X).matchSlot sy = some y →
        (select X).matchSlot sz = some z →
        LAP.Assignment.SameSlotOrder w sy sz →
        y = z) :
    paper_variability_at_most
      ((Finset.univ : Finset σ).image classOf).card
      (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.variabilityAtMost_choiceRuleOfAssignment_of_same_slot_order_borderline_injective
      hclass hkernel

/--
LAP distinct-ordering variability theorem: a unique-global-optimum finite
linear assignment selector with no ties within each slot has variability
bounded by the number of represented slot-induced applicant orders.
-/
theorem paper_lap_assignment_selector_variability_at_most_slot_order_classes_of_unique_global_optima
    [Fintype α] {σ κ : Type*} [DecidableEq σ] [Fintype σ] [DecidableEq κ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    {classOf : σ → κ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s)
    (hclass : ∀ {s t : σ}, classOf s = classOf t →
      LAP.Assignment.SameSlotOrder w s t) :
    paper_variability_at_most
      ((Finset.univ : Finset σ).image classOf).card
      (LAP.Assignment.choiceRuleOfAssignment select) := by
  exact
    LAP.Assignment.variabilityAtMost_choiceRuleOfAssignment_of_distinct_slot_orders
      hselect hnoTies hclass

/--
Canonical source form of the LAP variability theorem: quotient slots by
equality of their induced applicant orders and count those classes directly.
-/
theorem paper_lap_assignment_selector_variability_at_most_distinct_slot_orders
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} {select : Finset α → LAP.Assignment α σ}
    (hselect : LAP.Assignment.SelectsUniqueGlobalOptima w select)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s) :
    paper_variability_at_most
      (LAP.Assignment.distinctSlotOrderCount w)
      (LAP.Assignment.choiceRuleOfAssignment select) := by
  classical
  unfold LAP.Assignment.distinctSlotOrderCount
  exact
    paper_lap_assignment_selector_variability_at_most_slot_order_classes_of_unique_global_optima
      (classOf := LAP.Assignment.slotOrderClass w) hselect hnoTies
      (fun h => LAP.Assignment.sameSlotOrder_of_slotOrderClass_eq h)

/--
An operationally tie-broken finite LAP has variability bounded by its canonical
number of distinct slot-induced applicant orders.
-/
theorem paper_lap_well_posed_choice_variability_at_most_distinct_slot_orders
    [Fintype α] {σ : Type*} [DecidableEq σ] [Fintype σ]
    {w : α → σ → ℝ} (hwell : LAP.Assignment.WellPosedObjective w)
    (hnoTies : ∀ s : σ, LAP.Assignment.SlotNoTies w s) :
    paper_variability_at_most
      (LAP.Assignment.distinctSlotOrderCount w)
      (paperLAPChoiceRule w hwell) := by
  exact paper_lap_assignment_selector_variability_at_most_distinct_slot_orders
    (LAP.Assignment.canonicalOptimalAssignment_selectsUniqueGlobalOptima hwell)
    hnoTies

/--
Global linear-assignment optimality implies the local no-profitable-one-slot
swap condition used in the LAP ordering lemma.
-/
theorem paper_lap_no_profitable_one_slot_swap_of_objective_optimal
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hopt : A.ObjectiveOptimal X w)
    (hfill : A.CapacityFilling X) :
    A.NoProfitableOneSlotSwap X w := by
  exact LAP.Assignment.noProfitableOneSlotSwap_of_objectiveOptimal
    hopt hfill

/--
Appendix Lemma, LAP Ordering: local optimality of a finite linear assignment
implies that the assigned applicant at a slot is at least as high as any
rejected applicant in that slot's weight order.
-/
theorem paper_lap_slot_ordering
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hopt : A.NoProfitableOneSlotSwap X w)
    (hassign : LAP.Assignment.Feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hrej : A.Rejected X x) :
    LAP.Assignment.SlotAtLeast w s y x := by
  exact LAP.Assignment.slotAtLeast_rejected_of_noProfitableOneSlotSwap_of_feasible
    hopt hassign hslot hrej

/--
LAP ordering, chosen-side form: if an offered applicant strictly outranks a
slot occupant in that slot's order, the applicant is assigned somewhere.
-/
theorem paper_lap_strictly_higher_slot_applicant_assigned
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hopt : A.NoProfitableOneSlotSwap X w)
    (hassign : LAP.Assignment.Feasible X A)
    {s : σ} {y x : α}
    (hslot : A.matchSlot s = some y)
    (hxX : x ∈ X)
    (hbelow : LAP.Assignment.SlotBelow w s y x) :
    A.Assigned x := by
  exact LAP.Assignment.assigned_of_slotBelow_occupant_of_noProfitableOneSlotSwap_of_feasible
    hopt hassign hslot hxX hbelow

/--
LAP ordering in contradiction form: no rejected applicant strictly outranks an
assigned slot occupant in a feasible locally optimal finite assignment.
-/
theorem paper_lap_no_rejected_slot_below
    {σ : Type*} [DecidableEq σ] [Fintype σ]
    {X : Finset α} {w : α → σ → ℝ} {A : LAP.Assignment α σ}
    (hopt : A.NoProfitableOneSlotSwap X w)
    (hassign : LAP.Assignment.Feasible X A) :
    ¬ ∃ s y x, A.matchSlot s = some y ∧ A.Rejected X x ∧
      LAP.Assignment.SlotBelow w s y x := by
  exact LAP.Assignment.not_exists_rejected_slotBelow_of_noProfitableOneSlotSwap_of_feasible
    hopt hassign

/--
No zero instability under a nontrivial capacity constraint.

This is the precise condition needed for the paper's "q-acceptant choice
function cannot be 0-unstable" claim: there must be some feasible applicant
pool with more applicants than the positive capacity `q`.
-/
theorem paper_no_zero_unstable_of_q_acceptant_nontrivial
    {q : ℕ} {C : PaperChoiceRule α}
    (hfeasible : paper_feasible C)
    (haccept : paper_q_acceptant q C)
    (hqpos : 0 < q)
    {U : Finset α} (hUcard : q < U.card) :
    ¬ paper_zero_unstable C := by
  intro hzero
  have hmono : paper_monotonic C :=
    (paper_zero_distance_iff_substitutable_and_monotonic C).mp hzero |>.2
  exact false_of_feasible_of_monotonic_of_qAcceptant_of_card_gt
    (C := C) hfeasible hmono haccept hqpos hUcard

end DGD26AdmissionsPredictability
