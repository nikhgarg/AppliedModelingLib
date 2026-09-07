import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic

open scoped BigOperators

namespace AppliedModelingLib
namespace Decision

/-!
# Finite Argmax Decision Lemmas

Reusable finite lemmas for paper arguments where a decision rule maximizes a
pointwise score, such as a Bayes posterior probability of correctness.
-/

/-- A decision rule is pointwise score-maximizing if it picks an action whose
score is at least the score of every alternative action for each instance. -/
def IsPointwiseMax {ι α : Type*} (score : ι → α → ℝ) (choose : ι → α) : Prop :=
  ∀ i a, score i a ≤ score i (choose i)

/-- Total finite score is maximized by any pointwise score-maximizing rule. -/
theorem sum_score_le_of_isPointwiseMax {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) {choose opt : ι → α}
    (hopt : IsPointwiseMax score opt) :
    (∑ i : ι, score i (choose i)) ≤ ∑ i : ι, score i (opt i) := by
  exact Finset.sum_le_sum (by
    intro i _
    exact hopt i (choose i))

/-- Average finite score for a deterministic decision rule. -/
noncomputable def averageScore {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) (choose : ι → α) : ℝ :=
  (∑ i : ι, score i (choose i)) / (Fintype.card ι : ℝ)

/-- Average finite score is maximized by any pointwise score-maximizing rule. -/
theorem averageScore_le_of_isPointwiseMax {ι α : Type*} [Fintype ι]
    (score : ι → α → ℝ) {choose opt : ι → α}
    (hopt : IsPointwiseMax score opt) :
    averageScore score choose ≤ averageScore score opt := by
  unfold averageScore
  exact div_le_div_of_nonneg_right
    (sum_score_le_of_isPointwiseMax score hopt)
    (Nat.cast_nonneg (Fintype.card ι))

/-- A monotone expectation-like functional on real-valued random variables. -/
def MonotoneExpectation {ω : Type*} (expect : (ω → ℝ) → ℝ) : Prop :=
  ∀ f g, (∀ x, f x ≤ g x) → expect f ≤ expect g

/--
An expectation-like functional that is monotone and linear over finite sums.

This is intentionally abstract: finite PMF expectations, integrals of bounded
functions, or a paper-local expectation operator can instantiate it when the
needed monotonicity and finite linearity laws are available.
-/
def FiniteLinearExpectation {ω : Type*} (expect : (ω → ℝ) → ℝ) : Prop :=
  MonotoneExpectation expect ∧
    (∀ c f, expect (fun x => c * f x) = c * expect f) ∧
    (∀ f g, expect (fun x => f x + g x) = expect f + expect g)

theorem FiniteLinearExpectation.monotone {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect) :
    MonotoneExpectation expect :=
  hlin.1

theorem FiniteLinearExpectation.const_mul {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (c : ℝ) (f : ω → ℝ) :
    expect (fun x => c * f x) = c * expect f :=
  hlin.2.1 c f

theorem FiniteLinearExpectation.add {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (f g : ω → ℝ) :
    expect (fun x => f x + g x) = expect f + expect g :=
  hlin.2.2 f g

/-- A finite-linear expectation commutes with pointwise negation. -/
theorem FiniteLinearExpectation.neg {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (f : ω → ℝ) :
    expect (fun x => -f x) = -expect f := by
  simpa using FiniteLinearExpectation.const_mul hlin (-1) f

/-- A finite-linear expectation commutes with pointwise subtraction. -/
theorem FiniteLinearExpectation.sub {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (f g : ω → ℝ) :
    expect (fun x => f x - g x) = expect f - expect g := by
  simpa [sub_eq_add_neg, FiniteLinearExpectation.neg hlin g] using
    FiniteLinearExpectation.add hlin f (fun x => -g x)

theorem FiniteLinearExpectation.zero {ω : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect) :
    expect (fun _ : ω => 0) = 0 := by
  simpa using FiniteLinearExpectation.const_mul hlin 0 (fun _ : ω => 0)

theorem FiniteLinearExpectation.sum_finset {ω ι : Type*}
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (s : Finset ι) (f : ι → ω → ℝ) :
    expect (fun x => s.sum (fun i => f i x)) = s.sum (fun i => expect (f i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using FiniteLinearExpectation.zero hlin
  · intro a s has ih
    simp [Finset.sum_insert, has, FiniteLinearExpectation.add hlin, ih]

theorem FiniteLinearExpectation.sum {ω ι : Type*} [Fintype ι]
    {expect : (ω → ℝ) → ℝ} (hlin : FiniteLinearExpectation expect)
    (f : ι → ω → ℝ) :
    expect (fun x => ∑ i : ι, f i x) = ∑ i : ι, expect (f i) :=
  FiniteLinearExpectation.sum_finset hlin Finset.univ f

/--
Expected objective of a rule that observes `obs x` and then chooses an action.

This abstracts over the source of randomness.  A finite PMF expectation,
Lebesgue integral, or caller-specific expectation operator can instantiate
`expect` as long as it is monotone.
-/
noncomputable def expectedObjective {ω σ β : Type*}
    (expect : (ω → ℝ) → ℝ) (obs : ω → σ)
    (objective : σ → β → ℝ) (rule : σ → β) : ℝ :=
  expect (fun x => objective (obs x) (rule (obs x)))

/-- Finite linearity of expected objectives. -/
theorem expectedObjective_linear_combination {ω σ β : Type*}
    (expect : (ω → ℝ) → ℝ) (hlin : FiniteLinearExpectation expect)
    (obs : ω → σ) (objective₁ objective₂ : σ → β → ℝ)
    (c d : ℝ) (rule : σ → β) :
    expectedObjective expect obs
        (fun s action => c * objective₁ s action + d * objective₂ s action) rule =
      c * expectedObjective expect obs objective₁ rule +
        d * expectedObjective expect obs objective₂ rule := by
  unfold expectedObjective
  rw [FiniteLinearExpectation.add hlin]
  rw [FiniteLinearExpectation.const_mul hlin]
  rw [FiniteLinearExpectation.const_mul hlin]

/--
If every observed state has a pointwise optimizer, choosing one pointwise
maximizes any monotone expected objective.
-/
theorem exists_rule_maximizing_expectedObjective_of_pointwise_exists
    {ω σ β : Type*}
    (expect : (ω → ℝ) → ℝ) (hmono : MonotoneExpectation expect)
    (obs : ω → σ) (objective : σ → β → ℝ)
    (hpoint : ∀ s, ∃ opt : β, ∀ action : β, objective s action ≤ objective s opt) :
    ∃ optRule : σ → β,
      ∀ rule : σ → β,
        expectedObjective expect obs objective rule ≤
          expectedObjective expect obs objective optRule := by
  classical
  let optRule : σ → β := fun s => Classical.choose (hpoint s)
  refine ⟨optRule, ?_⟩
  intro rule
  unfold expectedObjective
  exact hmono _ _ (fun x =>
    Classical.choose_spec (hpoint (obs x)) (rule (obs x)))

/-- Average 0-1 accuracy of one dataset's decisions against its true labels. -/
noncomputable def datasetAccuracy {ι α : Type*} [Fintype ι] [DecidableEq α]
    (truth decision : ι → α) : ℝ :=
  averageScore (fun i a => if a = truth i then (1 : ℝ) else 0) decision

/-- Expected dataset accuracy of a rule under an arbitrary expectation operator. -/
noncomputable def expectedDecisionAccuracy {ω σ ι α : Type*}
    [Fintype ι] [DecidableEq α]
    (expect : (ω → ℝ) → ℝ) (obs : ω → σ)
    (truth : ω → ι → α) (rule : σ → ι → α) : ℝ :=
  expect (fun x => datasetAccuracy (truth x) (rule (obs x)))

/--
Expected posterior-score accuracy of a rule.

For a Bayes-optimal posterior, this is equal to expected 0-1 accuracy by the
tower property.
-/
noncomputable def expectedDecisionScore {ω σ ι α : Type*} [Fintype ι]
    (expect : (ω → ℝ) → ℝ) (obs : ω → σ)
    (score : σ → ι → α → ℝ) (rule : σ → ι → α) : ℝ :=
  expect (fun x => averageScore (score (obs x)) (rule (obs x)))

/--
Row-wise Bayes identities imply the full expected-accuracy tower bridge.

The row-wise hypothesis is the reusable core of the paper step
`E[I[Y_i = decision_i] | observed data] = posterior_i(decision_i)`.
-/
theorem expectedDecisionAccuracy_eq_expectedDecisionScore_of_row_bayes
    {ω σ α : Type*} {ι : Type} [Fintype ι] [DecidableEq α]
    (expect : (ω → ℝ) → ℝ) (hlin : FiniteLinearExpectation expect)
    (obs : ω → σ) (truth : ω → ι → α)
    (score : σ → ι → α → ℝ)
    (hrow : ∀ i (choose : σ → α),
      expect (fun x => if choose (obs x) = truth x i then (1 : ℝ) else 0) =
        expect (fun x => score (obs x) i (choose (obs x)))) :
    ∀ rule : σ → ι → α,
      expectedDecisionAccuracy expect obs truth rule =
        expectedDecisionScore expect obs score rule := by
  classical
  intro rule
  unfold expectedDecisionAccuracy expectedDecisionScore datasetAccuracy averageScore
  have hacc :
      expect
          (fun x =>
            (∑ i : ι, if rule (obs x) i = truth x i then (1 : ℝ) else 0) /
              (Fintype.card ι : ℝ)) =
        ((Fintype.card ι : ℝ)⁻¹) *
          ∑ i : ι,
            expect (fun x => if rule (obs x) i = truth x i then (1 : ℝ) else 0) := by
    calc
      expect
          (fun x =>
            (∑ i : ι, if rule (obs x) i = truth x i then (1 : ℝ) else 0) /
              (Fintype.card ι : ℝ)) =
          expect
            (fun x =>
              ((Fintype.card ι : ℝ)⁻¹) *
                ∑ i : ι, if rule (obs x) i = truth x i then (1 : ℝ) else 0) := by
            congr 1
            ext x
            rw [div_eq_mul_inv, mul_comm]
      _ = ((Fintype.card ι : ℝ)⁻¹) *
          expect
            (fun x =>
              ∑ i : ι, if rule (obs x) i = truth x i then (1 : ℝ) else 0) := by
            rw [FiniteLinearExpectation.const_mul hlin]
      _ = ((Fintype.card ι : ℝ)⁻¹) *
          ∑ i : ι,
            expect (fun x => if rule (obs x) i = truth x i then (1 : ℝ) else 0) := by
            rw [FiniteLinearExpectation.sum hlin]
  have hscore :
      expect
          (fun x =>
            (∑ i : ι, score (obs x) i (rule (obs x) i)) /
              (Fintype.card ι : ℝ)) =
        ((Fintype.card ι : ℝ)⁻¹) *
          ∑ i : ι,
            expect (fun x => score (obs x) i (rule (obs x) i)) := by
    calc
      expect
          (fun x =>
            (∑ i : ι, score (obs x) i (rule (obs x) i)) /
              (Fintype.card ι : ℝ)) =
          expect
            (fun x =>
              ((Fintype.card ι : ℝ)⁻¹) *
                ∑ i : ι, score (obs x) i (rule (obs x) i)) := by
            congr 1
            ext x
            rw [div_eq_mul_inv, mul_comm]
      _ = ((Fintype.card ι : ℝ)⁻¹) *
          expect (fun x => ∑ i : ι, score (obs x) i (rule (obs x) i)) := by
            rw [FiniteLinearExpectation.const_mul hlin]
      _ = ((Fintype.card ι : ℝ)⁻¹) *
          ∑ i : ι,
            expect (fun x => score (obs x) i (rule (obs x) i)) := by
            rw [FiniteLinearExpectation.sum hlin]
  rw [hacc, hscore]
  congr 1
  exact Finset.sum_congr rfl (by
    intro i _
    exact hrow i (fun s => rule s i))

/-- Pointwise argmax rules maximize expected posterior-score accuracy. -/
theorem expectedDecisionScore_le_of_pointwiseMax
    {ω σ ι α : Type*} [Fintype ι]
    (expect : (ω → ℝ) → ℝ) (hmono : MonotoneExpectation expect)
    (obs : ω → σ) (score : σ → ι → α → ℝ)
    {rule argmaxRule : σ → ι → α}
    (hargmax : ∀ s, IsPointwiseMax (score s) (argmaxRule s)) :
    expectedDecisionScore expect obs score rule ≤
      expectedDecisionScore expect obs score argmaxRule := by
  unfold expectedDecisionScore
  exact hmono _ _ (fun x =>
    averageScore_le_of_isPointwiseMax (score (obs x)) (hargmax (obs x)))

/--
Bayes posterior argmax maximizes expected 0-1 accuracy.

The hypothesis `hbayes` is the tower-property step: expected 0-1 accuracy
equals expected posterior score for every rule.
-/
theorem expectedDecisionAccuracy_le_of_bayesScore_pointwiseMax
    {ω σ ι α : Type*} [Fintype ι] [DecidableEq α]
    (expect : (ω → ℝ) → ℝ) (hmono : MonotoneExpectation expect)
    (obs : ω → σ) (truth : ω → ι → α)
    (score : σ → ι → α → ℝ)
    {rule argmaxRule : σ → ι → α}
    (hargmax : ∀ s, IsPointwiseMax (score s) (argmaxRule s))
    (hbayes : ∀ r : σ → ι → α,
      expectedDecisionAccuracy expect obs truth r =
        expectedDecisionScore expect obs score r) :
    expectedDecisionAccuracy expect obs truth rule ≤
      expectedDecisionAccuracy expect obs truth argmaxRule := by
  rw [hbayes rule, hbayes argmaxRule]
  exact expectedDecisionScore_le_of_pointwiseMax
    expect hmono obs score hargmax

/-- Every real-valued objective over a finite nonempty type has a maximizer. -/
theorem exists_maximizingFinite {β : Type*} [Fintype β] [Nonempty β]
    (objective : β → ℝ) :
    ∃ opt : β, ∀ action : β, objective action ≤ objective opt := by
  classical
  let defaultAction : β := Classical.choice inferInstance
  have hnonempty : (Finset.univ : Finset β).Nonempty :=
    ⟨defaultAction, by simp⟩
  obtain ⟨opt, _hmem, hopt⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset β))
      (H := hnonempty) (f := objective)
  refine ⟨opt, ?_⟩
  intro action
  have hle :
      objective action ≤
        (Finset.univ : Finset β).sup' hnonempty objective :=
    Finset.le_sup' (s := (Finset.univ : Finset β)) (f := objective) (by simp)
  rwa [hopt] at hle

/--
Every real-valued objective over finite deterministic decision rules has a
maximizing rule.

This is the reusable finite-existence core behind paper statements that define
an optimization over deterministic rules and then assert an optimal rule exists.
-/
theorem exists_maximizingDecisionRule {ι α : Type*}
    [Fintype ι] [Fintype α] [Nonempty α]
    (objective : (ι → α) → ℝ) :
    ∃ opt : ι → α, ∀ rule : ι → α, objective rule ≤ objective opt := by
  classical
  let defaultRule : ι → α := fun _ => Classical.choice inferInstance
  have hnonempty : (Finset.univ : Finset (ι → α)).Nonempty :=
    ⟨defaultRule, by simp⟩
  obtain ⟨opt, _hmem, hopt⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (ι → α)))
      (H := hnonempty) (f := objective)
  refine ⟨opt, ?_⟩
  intro rule
  have hle :
      objective rule ≤
        (Finset.univ : Finset (ι → α)).sup' hnonempty objective :=
    Finset.le_sup' (s := (Finset.univ : Finset (ι → α)))
      (f := objective) (by simp)
  rwa [hopt] at hle

/--
Every finite action problem has a pointwise optimizer at each observed state,
hence a joint rule maximizing the monotone expected objective.
-/
theorem exists_rule_maximizing_expectedObjective_finite_actions
    {ω σ β : Type*} [Fintype β] [Nonempty β]
    (expect : (ω → ℝ) → ℝ) (hmono : MonotoneExpectation expect)
    (obs : ω → σ) (objective : σ → β → ℝ) :
    ∃ optRule : σ → β,
      ∀ rule : σ → β,
        expectedObjective expect obs objective rule ≤
          expectedObjective expect obs objective optRule := by
  classical
  refine exists_rule_maximizing_expectedObjective_of_pointwise_exists
    expect hmono obs objective ?_
  intro s
  exact exists_maximizingFinite (objective s)

end Decision
end AppliedModelingLib
