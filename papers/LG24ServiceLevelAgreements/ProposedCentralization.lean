import LG24ServiceLevelAgreements.ProposedFixedLoad
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Proposed theory: centralization and endogenous admission

This file records finite-dimensional algebraic consequences of the July 2026
revision memo.  It separates deterministic fixed-load feasibility from the
dynamic pooling mechanism, gives the two-Borough category-pooling comparison
and its exact threshold, exhibits strict one-period pooling, distinguishes
conditional-delay and all-request objectives, and closes the zero-penalty
one-class endogenous-admission endpoint.

The results do not identify the deterministic benchmark with the stochastic
City-budget simulator and do not import a queueing tail theorem.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Deterministic fixed-load pooled and Borough feasibility -/

/-- A pooled deterministic allocation is feasible when total cell capacity fits. -/
def pooledFixedLoadFeasible
    {Borough Cell : Type*} [Fintype Borough] [Fintype Cell]
    (required : Borough → Cell → ℝ) (capacity : ℝ) : Prop :=
  ∑ b, ∑ i, required b i ≤ capacity

/--
Optimized Borough budgets are feasible when each Borough can cover its cells
and the Borough budgets fit inside the same City capacity.
-/
def optimizedBoroughFixedLoadFeasible
    {Borough Cell : Type*} [Fintype Borough] [Fintype Cell]
    (required : Borough → Cell → ℝ) (capacity : ℝ) : Prop :=
  ∃ budget : Borough → ℝ,
    (∀ b, ∑ i, required b i ≤ budget b) ∧ ∑ b, budget b ≤ capacity

/--
With freely optimized Borough budgets and preserved Borough-cell controls,
pooled and Borough-budget deterministic feasible sets are identical.
-/
theorem pooledFixedLoadFeasible_iff_optimizedBoroughFixedLoadFeasible
    {Borough Cell : Type*} [Fintype Borough] [Fintype Cell]
    (required : Borough → Cell → ℝ) (capacity : ℝ) :
    pooledFixedLoadFeasible required capacity ↔
      optimizedBoroughFixedLoadFeasible required capacity := by
  constructor
  · intro hpooled
    refine ⟨fun b ↦ ∑ i, required b i, ?_, ?_⟩
    · intro b
      exact le_rfl
    · exact hpooled
  · rintro ⟨budget, hborough, hbudget⟩
    exact le_trans (Finset.sum_le_sum fun b _ ↦ hborough b) hbudget

/-! ## Category-pooling benchmark and the exact two-Borough threshold -/

/-- Numerator of the two-Borough conditional price of equity. -/
def twoBoroughConditionalPriceNumerator (u v : ℝ) : ℝ :=
  (u - v) ^ 2

/-- Numerator of the two-Borough category-pooling gain. -/
def twoBoroughCategoryPoolingNumerator (u v : ℝ) : ℝ :=
  2 * u * v

/-- The comparison is governed by `(u-v)^2 - 2uv`. -/
theorem twoBorough_price_sub_categoryPooling_eq (u v : ℝ) :
    twoBoroughConditionalPriceNumerator u v -
        twoBoroughCategoryPoolingNumerator u v =
      (u - v) ^ 2 - 2 * u * v := by
  rfl

/-- Equal square-root loads make the pooling benchmark strictly larger. -/
theorem twoBorough_categoryPooling_gt_price_at_equal_load :
    twoBoroughConditionalPriceNumerator 1 1 <
      twoBoroughCategoryPoolingNumerator 1 1 := by
  norm_num [twoBoroughConditionalPriceNumerator,
    twoBoroughCategoryPoolingNumerator]

/-- A sufficiently imbalanced load pair makes the price of equity larger. -/
theorem twoBorough_price_gt_categoryPooling_at_four_one :
    twoBoroughCategoryPoolingNumerator 4 1 <
      twoBoroughConditionalPriceNumerator 4 1 := by
  norm_num [twoBoroughConditionalPriceNumerator,
    twoBoroughCategoryPoolingNumerator]

/--
Exact root threshold for the normalized comparison
`(q-1)^2 ≥ 2q`: it holds outside `[2-√3, 2+√3]`.
-/
theorem twoBorough_categoryPooling_ratio_threshold (q : ℝ) :
    2 * q ≤ (q - 1) ^ 2 ↔
      q ≤ 2 - Real.sqrt 3 ∨ 2 + Real.sqrt 3 ≤ q := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg 3
  have hsqrt_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    by_contra houtside
    push Not at houtside
    have hleft : 0 < q - (2 - Real.sqrt 3) := by linarith
    have hright : q - (2 + Real.sqrt 3) < 0 := by linarith
    have hprod :
        (q - (2 - Real.sqrt 3)) * (q - (2 + Real.sqrt 3)) < 0 :=
      mul_neg_of_pos_of_neg hleft hright
    nlinarith
  · rintro (hlow | hhigh)
    · have hleft : q - (2 - Real.sqrt 3) ≤ 0 := by linarith
      have hright : q - (2 + Real.sqrt 3) ≤ 0 := by
        nlinarith [show (0 : ℝ) ≤ 2 * Real.sqrt 3 by positivity]
      have hprod : 0 ≤
          (q - (2 - Real.sqrt 3)) * (q - (2 + Real.sqrt 3)) :=
        mul_nonneg_of_nonpos_of_nonpos hleft hright
      nlinarith
    · have hleft : 0 ≤ q - (2 - Real.sqrt 3) := by
        nlinarith [show (0 : ℝ) ≤ 2 * Real.sqrt 3 by positivity]
      have hright : 0 ≤ q - (2 + Real.sqrt 3) := by linarith
      have hprod : 0 ≤
          (q - (2 - Real.sqrt 3)) * (q - (2 + Real.sqrt 3)) :=
        mul_nonneg hleft hright
      nlinarith

/-! ## Strict one-period pooling -/

/--
With two equal fixed shares, one unit of backlog concentrated in one Borough
leaves half a unit of capacity stranded in the other Borough.
-/
theorem poolingOpportunity_strict_two_borough_example :
    poolingOpportunity
        (fun b : Fin 2 ↦ if b = 0 then (1 : ℝ) else 0)
        (fun _ : Fin 2 ↦ (1 / 2 : ℝ)) 1 = 1 / 2 := by
  norm_num [poolingOpportunity, pooledServed, fixedShareServed,
    Fin.sum_univ_two]

/-! ## Conditional-delay versus all-request accounting -/

/-- The all-request burden differs from inspected-request burden by a selection term. -/
theorem allRequestBurden_sub_conditionalBurden
    (risk inspectionProbability conditionalDelay noninspectionPenalty : ℝ) :
    allRequestBurden risk inspectionProbability conditionalDelay
        noninspectionPenalty - risk * conditionalDelay =
      risk * (1 - inspectionProbability) *
        (noninspectionPenalty - conditionalDelay) := by
  simp only [allRequestBurden]
  ring

/--
Equal conditional delays can coexist with unequal all-request burdens when
inspection probabilities differ.
-/
theorem equalConditionalDelay_but_distinctAllRequestBurden :
    twoBoroughRange (1 : ℝ) 1 = 0 ∧
      twoBoroughRange
        (allRequestBurden 1 1 1 3)
        (allRequestBurden 1 0 1 3) = 2 := by
  norm_num [twoBoroughRange, allRequestBurden]

/-- Unconditional nonservice includes both nonadmission and admitted violations. -/
def unconditionalNonserviceProbability
    (admissionProbability conditionalViolationProbability : ℝ) : ℝ :=
  (1 - admissionProbability) +
    admissionProbability * conditionalViolationProbability

/--
Under nonnegative probabilities, an unconditional SLA forces admission
probability to be at least one minus the unconditional violation allowance.
-/
theorem admissionProbability_lower_bound_of_unconditionalSLA
    (admissionProbability conditionalViolationProbability
      unconditionalAllowance : ℝ)
    (hadmission : 0 ≤ admissionProbability)
    (hconditional : 0 ≤ conditionalViolationProbability)
    (hsla : unconditionalNonserviceProbability admissionProbability
      conditionalViolationProbability ≤ unconditionalAllowance) :
    1 - unconditionalAllowance ≤ admissionProbability := by
  have hproduct :
      0 ≤ admissionProbability * conditionalViolationProbability :=
    mul_nonneg hadmission hconditional
  simp only [unconditionalNonserviceProbability] at hsla
  linarith

/-! ## One-class endogenous admission with no noninspection penalty -/

/-- The one-class served-delay term when the noninspection penalty is zero. -/
def oneClassNoPenaltyEndogenousCost
    (reliability capacity admitted : ℝ) : ℝ :=
  reliability * admitted / (capacity - admitted)

/-- At zero admitted load, the no-penalty one-class cost is zero. -/
theorem oneClassNoPenaltyEndogenousCost_zero
    (reliability capacity : ℝ) :
    oneClassNoPenaltyEndogenousCost reliability capacity 0 = 0 := by
  simp [oneClassNoPenaltyEndogenousCost]

/--
For nonnegative reliability and a feasible admitted load below capacity, the
zero-admission endpoint minimizes the no-penalty one-class objective.
-/
theorem oneClassNoPenaltyEndogenousCost_zero_is_minimizer
    (reliability capacity admitted : ℝ)
    (hreliability : 0 ≤ reliability)
    (hadmitted : 0 ≤ admitted)
    (hcapacity : admitted < capacity) :
    oneClassNoPenaltyEndogenousCost reliability capacity 0 ≤
      oneClassNoPenaltyEndogenousCost reliability capacity admitted := by
  rw [oneClassNoPenaltyEndogenousCost_zero]
  apply div_nonneg
  · exact mul_nonneg hreliability hadmitted
  · linarith

end

end LG24ServiceLevelAgreements
