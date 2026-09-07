import AppliedModelingLib.GameTheory.Choice.Binary
import AppliedModelingLib.GameTheory.Choice.EquilibriumAE
import Mathlib.Tactic.Linarith

open MeasureTheory

namespace AppliedModelingLib

/-!
# Almost-Everywhere Binary Choice Best Responses

Reusable a.e. variants of the binary-choice best-response lemmas.  These are
for continuous type spaces where cutoff ties or off-support states should not
be pointwise equilibrium obligations.

## Main declarations

- `NoProfitableBinaryChoiceDeviationAE`
- `noProfitableBinaryChoiceDeviationAE_of_pointwise`
- `noProfitableBinaryChoiceDeviationAE_of_forall_not_mem_null`
- `noProfitableBinaryChoiceDeviationAE_of_bool_best_response_forall_not_mem_null`
- `noProfitableBinaryChoiceDeviationAE_of_bool_best_response_ae`
- `bool_best_response_ae_of_noProfitableBinaryChoiceDeviationAE`
- `noProfitableBinaryChoiceDeviationAE_of_choiceEquilibriumAE_payoff_projection`
- `choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie`
- `choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`
- `bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie`
- `bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie`
- `chosen_reference_le_value_ae_of_affine_noProfitableBinaryChoiceDeviationAE`
- `unchosen_value_le_reference_ae_of_affine_noProfitableBinaryChoiceDeviationAE`
-/

/--
Two-sided binary best-response condition holding almost everywhere under `μ`.
Choosing weakly dominates not choosing at chosen values, and not choosing
weakly dominates choosing at unchosen values, outside a null set.
-/
def NoProfitableBinaryChoiceDeviationAE
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (chooses : α → Prop)
    (choosePayoff otherPayoff : α → ℝ) : Prop :=
  (∀ᵐ a ∂μ, chooses a → otherPayoff a ≤ choosePayoff a) ∧
    (∀ᵐ a ∂μ, ¬ chooses a → choosePayoff a ≤ otherPayoff a)

theorem noProfitableBinaryChoiceDeviationAE_chosen_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff) :
    ∀ᵐ a ∂μ, chooses a → otherPayoff a ≤ choosePayoff a :=
  hbest.1

theorem noProfitableBinaryChoiceDeviationAE_unchosen_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff) :
    ∀ᵐ a ∂μ, ¬ chooses a → choosePayoff a ≤ otherPayoff a :=
  hbest.2

/-- Every pointwise binary best response is an a.e. binary best response. -/
theorem noProfitableBinaryChoiceDeviationAE_of_pointwise
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    (hbest : NoProfitableBinaryChoiceDeviation chooses choosePayoff otherPayoff) :
    NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff :=
  ⟨Filter.Eventually.of_forall hbest.1,
    Filter.Eventually.of_forall hbest.2⟩

/--
Build an a.e. binary no-deviation certificate from pointwise chosen/unchosen
payoff comparisons outside a null exception set.
-/
theorem noProfitableBinaryChoiceDeviationAE_of_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    {exception : Set α}
    (hexception : μ exception = 0)
    (hchosen :
      ∀ a, a ∉ exception → chooses a → otherPayoff a ≤ choosePayoff a)
    (hunchosen :
      ∀ a, a ∉ exception → ¬ chooses a → choosePayoff a ≤ otherPayoff a) :
    NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff :=
  ⟨ae_of_forall_not_mem_null (μ := μ) hexception hchosen,
    ae_of_forall_not_mem_null (μ := μ) hexception hunchosen⟩

/--
Convert a raw a.e. Boolean best-response condition into the named binary
no-profitable-deviation predicate.
-/
theorem noProfitableBinaryChoiceDeviationAE_of_bool_best_response_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (chooses : α → Bool) {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      ∀ᵐ a ∂μ, ∀ action : Bool,
        (if action then choosePayoff a else otherPayoff a) ≤
          if chooses a then choosePayoff a else otherPayoff a) :
    NoProfitableBinaryChoiceDeviationAE μ (fun a => chooses a = true)
      choosePayoff otherPayoff := by
  constructor
  · filter_upwards [hbest] with a hbest_a hchoose
    have h := hbest_a false
    simpa [hchoose] using h
  · filter_upwards [hbest] with a hbest_a hnotChoose
    have h := hbest_a true
    have hchoose_false : chooses a = false := by
      cases hchoose : chooses a
      · rfl
      · exact False.elim (hnotChoose hchoose)
    simpa [hchoose_false] using h

/--
Convert a raw Boolean best-response condition outside a null exception set into
the named a.e. binary no-profitable-deviation predicate.
-/
theorem noProfitableBinaryChoiceDeviationAE_of_bool_best_response_forall_not_mem_null
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (chooses : α → Bool) {choosePayoff otherPayoff : α → ℝ}
    {exception : Set α}
    (hexception : μ exception = 0)
    (hbest :
      ∀ a, a ∉ exception → ∀ action : Bool,
        (if action then choosePayoff a else otherPayoff a) ≤
          if chooses a then choosePayoff a else otherPayoff a) :
    NoProfitableBinaryChoiceDeviationAE μ (fun a => chooses a = true)
      choosePayoff otherPayoff :=
  noProfitableBinaryChoiceDeviationAE_of_bool_best_response_ae chooses
    (ae_of_forall_not_mem_null (μ := μ) hexception hbest)

/--
Convert the named a.e. binary no-profitable-deviation predicate back into the
raw Boolean best-response form.
-/
theorem bool_best_response_ae_of_noProfitableBinaryChoiceDeviationAE
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (chooses : α → Bool) {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ (fun a => chooses a = true)
        choosePayoff otherPayoff) :
    ∀ᵐ a ∂μ, ∀ action : Bool,
      (if action then choosePayoff a else otherPayoff a) ≤
        if chooses a then choosePayoff a else otherPayoff a := by
  filter_upwards [hbest.1, hbest.2] with a hchosen hunchosen action
  by_cases hchoose : chooses a = true
  · cases action
    · simpa [hchoose] using hchosen hchoose
    · simp [hchoose]
  · have hchoose_false : chooses a = false := by
      cases h : chooses a
      · rfl
      · exact False.elim (hchoose h)
    cases action
    · simp [hchoose_false]
    · simpa [hchoose_false] using hunchosen hchoose

/--
Project an a.e. static choice equilibrium onto an a.e. two-sided binary
best-response condition by naming the two deviation actions and rewriting the
chosen payoff in the chosen and unchosen cases.
-/
theorem noProfitableBinaryChoiceDeviationAE_of_choiceEquilibriumAE_payoff_projection
    {α Action : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop} {choosePayoff otherPayoff : α → ℝ}
    {E : ChoiceEquilibriumData α Action}
    (hEq : IsChoiceEquilibriumAE μ E)
    (chooseAction otherAction : α → Action)
    (hchooseFeasible :
      ∀ a, E.actionFeasible a (chooseAction a))
    (hotherFeasible :
      ∀ a, E.actionFeasible a (otherAction a))
    (hchoosePayoff :
      ∀ a, E.payoff a (chooseAction a) = choosePayoff a)
    (hotherPayoff :
      ∀ a, E.payoff a (otherAction a) = otherPayoff a)
    (hchosenChoosePayoff :
      ∀ a, chooses a →
        E.payoff a (E.chosenAction a) = choosePayoff a)
    (hchosenOtherPayoff :
      ∀ a, ¬ chooses a →
        E.payoff a (E.chosenAction a) = otherPayoff a) :
    NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff := by
  constructor
  · filter_upwards [isChoiceEquilibriumAE_best_response_ae hEq] with a hbest
    intro hchoose
    have h :=
      hbest (otherAction a) (hotherFeasible a)
    rw [hotherPayoff a, hchosenChoosePayoff a hchoose] at h
    exact h
  · filter_upwards [isChoiceEquilibriumAE_best_response_ae hEq] with a hbest
    intro hnotChoose
    have h :=
      hbest (chooseAction a) (hchooseFeasible a)
    rw [hchoosePayoff a, hchosenOtherPayoff a hnotChoose] at h
    exact h

/--
A.e. binary threshold identification away from ties.  This is the a.e. analogue
of `choice_rule_iff_threshold_of_noProfitableBinaryChoiceDeviation_tiebreak`,
but replaces pointwise tie-breaking with an a.e. no-tie premise.
-/
theorem choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses threshold : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff)
    (hthreshold :
      ∀ a, otherPayoff a ≤ choosePayoff a ↔ threshold a)
    (hnoTie : ∀ᵐ a ∂μ, choosePayoff a ≠ otherPayoff a) :
    ∀ᵐ a ∂μ, chooses a ↔ threshold a := by
  filter_upwards [hbest.1, hbest.2, hnoTie] with
    a hchosen_best hunchosen_best hnoTie_a
  constructor
  · intro hchoose
    exact (hthreshold a).1 (hchosen_best hchoose)
  · intro hthreshold_a
    by_cases hchoose : chooses a
    · exact hchoose
    · have hchoose_le_other := hunchosen_best hchoose
      have hother_le_choose := (hthreshold a).2 hthreshold_a
      exact False.elim (hnoTie_a (le_antisymm hchoose_le_other hother_le_choose))

/--
A.e. binary threshold identification when the tie set itself is null.  This is
the cutoff-boundary form usually supplied by continuous laws or no-atoms facts.
-/
theorem choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses threshold : α → Prop}
    {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses choosePayoff otherPayoff)
    (hthreshold :
      ∀ a, otherPayoff a ≤ choosePayoff a ↔ threshold a)
    (htie : μ {a | choosePayoff a = otherPayoff a} = 0) :
    ∀ᵐ a ∂μ, chooses a ↔ threshold a :=
  choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie
    hbest hthreshold
    (ae_of_forall_not_mem_null (μ := μ) htie
      (fun a ha hEq => ha hEq))

/--
Boolean a.e. threshold identification away from ties.  The chosen action is
represented as a `Bool` and is equal a.e. to `decide (threshold a)`.
-/
theorem bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (chooses : α → Bool) {threshold : α → Prop} [DecidablePred threshold]
    {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ (fun a => chooses a = true)
        choosePayoff otherPayoff)
    (hthreshold :
      ∀ a, otherPayoff a ≤ choosePayoff a ↔ threshold a)
    (hnoTie : ∀ᵐ a ∂μ, choosePayoff a ≠ otherPayoff a) :
    ∀ᵐ a ∂μ, chooses a = decide (threshold a) := by
  have hiff :=
    choice_rule_iff_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie
      (chooses := fun a => chooses a = true) hbest hthreshold hnoTie
  filter_upwards [hiff] with a hiff_a
  by_cases hthreshold_a : threshold a
  · have htrue : chooses a = true := hiff_a.2 hthreshold_a
    simp [hthreshold_a, htrue]
  · have hnotTrue : chooses a ≠ true := fun htrue =>
      hthreshold_a (hiff_a.1 htrue)
    cases hchoose : chooses a
    · simp [hthreshold_a]
    · exact False.elim (hnotTrue hchoose)

/--
Boolean a.e. threshold identification when the payoff tie set is null.
-/
theorem bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_null_tie
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (chooses : α → Bool) {threshold : α → Prop} [DecidablePred threshold]
    {choosePayoff otherPayoff : α → ℝ}
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ (fun a => chooses a = true)
        choosePayoff otherPayoff)
    (hthreshold :
      ∀ a, otherPayoff a ≤ choosePayoff a ↔ threshold a)
    (htie : μ {a | choosePayoff a = otherPayoff a} = 0) :
    ∀ᵐ a ∂μ, chooses a = decide (threshold a) :=
  bool_choice_eq_decide_threshold_ae_of_noProfitableBinaryChoiceDeviationAE_no_tie
    chooses hbest hthreshold
    (ae_of_forall_not_mem_null (μ := μ) htie
      (fun a ha hEq => ha hEq))

/--
Affine chosen-payoff specialization: if choosing has positive-slope affine
payoff in `value` and the outside payoff is the same affine expression at
`reference`, then every a.e. chooser has `reference ≤ value`.
-/
theorem chosen_reference_le_value_ae_of_affine_noProfitableBinaryChoiceDeviationAE
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop}
    (base slope denom reference value : α → ℝ)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses
        (fun a => (base a + slope a * value a) / denom a)
        (fun a => (base a + slope a * reference a) / denom a))
    (hslope : ∀ a, 0 < slope a)
    (hdenom : ∀ a, 0 < denom a) :
    ∀ᵐ a ∂μ, chooses a → reference a ≤ value a := by
  filter_upwards [hbest.1] with a hbest_a hchoose
  have hmul :=
    mul_le_mul_of_nonneg_right (hbest_a hchoose) (le_of_lt (hdenom a))
  have hsimpl :
      base a + slope a * reference a ≤
        base a + slope a * value a := by
    simpa [div_mul_cancel₀ _ (ne_of_gt (hdenom a))] using hmul
  nlinarith [hslope a]

/--
Affine unchosen-payoff specialization: if choosing has positive-slope affine
payoff in `value` and the outside payoff is the same affine expression at
`reference`, then every a.e. unchosen value has `value ≤ reference`.
-/
theorem unchosen_value_le_reference_ae_of_affine_noProfitableBinaryChoiceDeviationAE
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {chooses : α → Prop}
    (base slope denom reference value : α → ℝ)
    (hbest :
      NoProfitableBinaryChoiceDeviationAE μ chooses
        (fun a => (base a + slope a * value a) / denom a)
        (fun a => (base a + slope a * reference a) / denom a))
    (hslope : ∀ a, 0 < slope a)
    (hdenom : ∀ a, 0 < denom a) :
    ∀ᵐ a ∂μ, ¬ chooses a → value a ≤ reference a := by
  filter_upwards [hbest.2] with a hbest_a hnotChoose
  have hmul :=
    mul_le_mul_of_nonneg_right (hbest_a hnotChoose) (le_of_lt (hdenom a))
  have hsimpl :
      base a + slope a * value a ≤
        base a + slope a * reference a := by
    simpa [div_mul_cancel₀ _ (ne_of_gt (hdenom a))] using hmul
  nlinarith [hslope a]

end AppliedModelingLib
