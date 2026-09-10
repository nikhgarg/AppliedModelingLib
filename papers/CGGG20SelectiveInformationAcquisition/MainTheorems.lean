import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Optimization.LinearProgram
import AppliedModelingLib.Foundations.Optimization.MeasureThreshold
import AppliedModelingLib.Foundations.Optimization.ThresholdExchange
import AppliedModelingLib.Foundations.Probability.RealDistribution

/-!
# Paper-Facing Theorems: Fair Allocation through Selective Information Acquisition

This file starts the source-faithful Lean surface for Cai, Gaebler, Garg, and
Goel, "Fair Allocation through Selective Information Acquisition".

The first closed slice formalizes the fixed-threshold linear program in Section
3: the displayed expected-utility objective, budget constraint, and diversity
constraints are affine functions of the screening probabilities.  The global
threshold-reduction theorem from the appendix is intentionally not claimed here
yet; it requires a separate threshold/knapsack dominance proof.
-/

open scoped BigOperators
open MeasureTheory

namespace CGGG20SelectiveInformationAcquisition

open AppliedModelingLib.Decision
open AppliedModelingLib.Optimization
open AppliedModelingLib.Probability

/--
Finite-state data for the appendix's single-group cost-aware threshold
exchange argument.

The source proof works with expectations of posterior utilities `\hat U_i`.
Here those expectations are represented as finite weighted sums over `State`.
-/
structure CostAwareThresholdData (Applicant State : Type*) where
  weight : State → ℝ
  posteriorUtility : Applicant → State → ℝ
  allocCost : Applicant → ℝ

namespace CostAwareThresholdData

variable {Applicant State : Type*} [Fintype Applicant] [Fintype State]

/-- An allocation policy is a state-dependent allocation probability. -/
abbrev AllocationPolicy (Applicant State : Type*) :=
  Applicant → State → ℝ

/-- Source allocation policies have probabilities in `[0,1]`. -/
def AllocationPolicyBounds
    (policy : AllocationPolicy Applicant State) : Prop :=
  ∀ item state, 0 ≤ policy item state ∧ policy item state ≤ 1

/--
Single-threshold cost-aware policy, written without division.

For positive costs this is equivalent to thresholding `\hat U_i / c_i` at `t`.
The boundary probability is the common `alpha`, matching the single-group
appendix proof.
-/
def IsSingleCostAwareThresholdPolicy
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  0 ≤ alpha ∧ alpha ≤ 1 ∧
    ∀ item state,
      (D.allocCost item * t < D.posteriorUtility item state →
        policy item state = 1) ∧
      (D.posteriorUtility item state = D.allocCost item * t →
        policy item state = alpha) ∧
      (D.posteriorUtility item state < D.allocCost item * t →
        policy item state = 0)

/-- The canonical boundary-randomized single-threshold policy. -/
noncomputable def singleThresholdPolicy
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ) :
    AllocationPolicy Applicant State :=
  fun item state =>
    if D.allocCost item * t < D.posteriorUtility item state then
      1
    else if D.posteriorUtility item state < D.allocCost item * t then
      0
    else
      alpha

/-- The canonical single-threshold policy satisfies the source definition. -/
theorem singleThresholdPolicy_isSingleCostAwareThresholdPolicy
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    D.IsSingleCostAwareThresholdPolicy t alpha
      (D.singleThresholdPolicy t alpha) := by
  classical
  refine ⟨halpha_nonneg, halpha_le_one, ?_⟩
  intro item state
  constructor
  · intro habove
    simp [singleThresholdPolicy, habove]
  constructor
  · intro heq
    have hnot_above :
        ¬ D.allocCost item * t < D.posteriorUtility item state := by
      rw [heq]
      exact not_lt.mpr le_rfl
    have hnot_below :
        ¬ D.posteriorUtility item state < D.allocCost item * t := by
      rw [heq]
      exact not_lt.mpr le_rfl
    simp [singleThresholdPolicy, hnot_above, hnot_below]
  · intro hbelow
    have hnot_above :
        ¬ D.allocCost item * t < D.posteriorUtility item state :=
      not_lt.mpr hbelow.le
    simp [singleThresholdPolicy, hnot_above, hbelow]

/--
Endpoint-aware cost-aware threshold policy.

The source definition permits thresholds in `ℝ ∪ {-∞, ∞}`.  The formal
endpoints allocate to everyone (`-∞`) or no one (`∞`); finite thresholds use
the ordinary cost-aware comparison.
-/
def IsSingleCostAwareExtendedThresholdPolicy
    (D : CostAwareThresholdData Applicant State)
    (threshold : RealThreshold) (alpha : ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  match threshold with
  | RealThreshold.negInf =>
      0 ≤ alpha ∧ alpha ≤ 1 ∧ ∀ item state, policy item state = 1
  | RealThreshold.finite t =>
      D.IsSingleCostAwareThresholdPolicy t alpha policy
  | RealThreshold.posInf =>
      0 ≤ alpha ∧ alpha ≤ 1 ∧ ∀ item state, policy item state = 0

/-- Canonical endpoint-aware cost-aware threshold policy. -/
noncomputable def extendedSingleThresholdPolicy
    (D : CostAwareThresholdData Applicant State)
    (threshold : RealThreshold) (alpha : ℝ) :
    AllocationPolicy Applicant State :=
  match threshold with
  | RealThreshold.negInf => fun _ _ => 1
  | RealThreshold.finite t => D.singleThresholdPolicy t alpha
  | RealThreshold.posInf => fun _ _ => 0

/-- The canonical endpoint-aware rule satisfies the source definition. -/
theorem extendedSingleThresholdPolicy_isSingleCostAwareExtendedThresholdPolicy
    (D : CostAwareThresholdData Applicant State)
    (threshold : RealThreshold) (alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    D.IsSingleCostAwareExtendedThresholdPolicy threshold alpha
      (D.extendedSingleThresholdPolicy threshold alpha) := by
  cases threshold with
  | negInf =>
      exact ⟨halpha_nonneg, halpha_le_one, by intro item state; rfl⟩
  | finite t =>
      exact
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          t alpha halpha_nonneg halpha_le_one
  | posInf =>
      exact ⟨halpha_nonneg, halpha_le_one, by intro item state; rfl⟩

/-- Expected posterior utility of an allocation policy. -/
noncomputable def expectedPosteriorUtility
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        policy item state * D.posteriorUtility item state

/-- Expected allocation cost of an allocation policy. -/
noncomputable def expectedCost
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        D.allocCost item * policy item state

/-- Expected posterior utility strictly above a threshold. -/
noncomputable def strictAbovePosteriorUtility
    (D : CostAwareThresholdData Applicant State) (t : ℝ) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.allocCost item * t < D.posteriorUtility item state then
          D.posteriorUtility item state
        else
          0

/-- Expected posterior utility exactly on a threshold boundary. -/
noncomputable def boundaryPosteriorUtility
    (D : CostAwareThresholdData Applicant State) (t : ℝ) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.posteriorUtility item state = D.allocCost item * t then
          D.posteriorUtility item state
        else
          0

/--
The canonical threshold policy's expected posterior utility is affine in its
boundary randomization probability.
-/
theorem expectedPosteriorUtility_singleThresholdPolicy_eq
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ) :
    D.expectedPosteriorUtility (D.singleThresholdPolicy t alpha) =
      D.strictAbovePosteriorUtility t +
        alpha * D.boundaryPosteriorUtility t := by
  classical
  let aboveSum : State → ℝ := fun state =>
    ∑ item : Applicant,
      if D.allocCost item * t < D.posteriorUtility item state then
        D.posteriorUtility item state
      else
        0
  let boundarySum : State → ℝ := fun state =>
    ∑ item : Applicant,
      if D.posteriorUtility item state = D.allocCost item * t then
        D.posteriorUtility item state
      else
        0
  have hinner :
      ∀ state,
        (∑ item : Applicant,
          D.singleThresholdPolicy t alpha item state *
            D.posteriorUtility item state) =
          aboveSum state + alpha * boundarySum state := by
    intro state
    calc
      (∑ item : Applicant,
        D.singleThresholdPolicy t alpha item state *
          D.posteriorUtility item state)
          =
          ∑ item : Applicant,
            ((if D.allocCost item * t < D.posteriorUtility item state then
                D.posteriorUtility item state
              else
                0) +
              alpha *
                (if D.posteriorUtility item state = D.allocCost item * t then
                  D.posteriorUtility item state
                else
                  0)) := by
        refine Finset.sum_congr rfl ?_
        intro item _
        by_cases habove :
            D.allocCost item * t < D.posteriorUtility item state
        · have hne :
              D.posteriorUtility item state ≠ D.allocCost item * t := by
            exact ne_of_gt habove
          simp [singleThresholdPolicy, habove, hne]
        · by_cases hbelow :
              D.posteriorUtility item state < D.allocCost item * t
          · have hne :
                D.posteriorUtility item state ≠ D.allocCost item * t := by
              exact ne_of_lt hbelow
            simp [singleThresholdPolicy, habove, hbelow, hne]
          · have heq :
                D.posteriorUtility item state = D.allocCost item * t :=
              le_antisymm (le_of_not_gt habove) (le_of_not_gt hbelow)
            simp [singleThresholdPolicy, heq]
      _ =
          aboveSum state + alpha * boundarySum state := by
        simp only [aboveSum, boundarySum]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
  simp only [expectedPosteriorUtility]
  calc
    (∑ state : State,
      D.weight state *
        ∑ item : Applicant,
          D.singleThresholdPolicy t alpha item state *
            D.posteriorUtility item state)
        =
        ∑ state : State,
          D.weight state * (aboveSum state + alpha * boundarySum state) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      rw [hinner state]
    _ =
        D.strictAbovePosteriorUtility t +
          alpha * D.boundaryPosteriorUtility t := by
      have hsplit :
          (∑ state : State,
            D.weight state * (aboveSum state + alpha * boundarySum state)) =
            (∑ state : State, D.weight state * aboveSum state) +
              ∑ state : State,
                D.weight state * (alpha * boundarySum state) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro state _
        ring
      have hsecond :
          (∑ state : State,
            D.weight state * (alpha * boundarySum state)) =
            alpha *
              ∑ state : State, D.weight state * boundarySum state := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro state _
        ring
      simp only [strictAbovePosteriorUtility, boundaryPosteriorUtility,
        aboveSum, boundarySum]
      rw [hsplit, hsecond]

/-- Expected cost strictly above a threshold. -/
noncomputable def strictAboveCost
    (D : CostAwareThresholdData Applicant State) (t : ℝ) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.allocCost item * t < D.posteriorUtility item state then
          D.allocCost item
        else
          0

/-- Expected cost exactly on a threshold boundary. -/
noncomputable def boundaryCost
    (D : CostAwareThresholdData Applicant State) (t : ℝ) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.posteriorUtility item state = D.allocCost item * t then
          D.allocCost item
        else
          0

/-- Finite atoms for threshold bracketing: a state and an applicant. -/
abbrev ThresholdAtom (Applicant State : Type*) :=
  State × Applicant

/-- The cost-aware score of a finite atom, `\hat U_i / c_i`. -/
noncomputable def atomScore
    (D : CostAwareThresholdData Applicant State)
    (atom : ThresholdAtom Applicant State) : ℝ :=
  D.posteriorUtility atom.2 atom.1 / D.allocCost atom.2

/-- Cost mass of a finite atom. -/
noncomputable def costAtomMass
    (D : CostAwareThresholdData Applicant State)
    (atom : ThresholdAtom Applicant State) : ℝ :=
  D.weight atom.1 * D.allocCost atom.2

/-- Posterior-utility mass of a finite atom. -/
noncomputable def utilityAtomMass
    (D : CostAwareThresholdData Applicant State)
    (atom : ThresholdAtom Applicant State) : ℝ :=
  D.weight atom.1 * D.posteriorUtility atom.2 atom.1

/-- Strict-above cost is the finite atom strict-above mass. -/
theorem strictAboveCost_eq_finiteAtomStrictAboveMass
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.strictAboveCost t =
      finiteAtomStrictAboveMass D.atomScore D.costAtomMass t := by
  classical
  simp only [strictAboveCost, finiteAtomStrictAboveMass, atomScore,
    costAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  by_cases habove : D.allocCost item * t < D.posteriorUtility item state
  · have hscore : t < D.posteriorUtility item state / D.allocCost item := by
      rw [lt_div_iff₀ (hcost_pos item), mul_comm]
      exact habove
    simp [habove, hscore]
  · have hscore_not :
        ¬ t < D.posteriorUtility item state / D.allocCost item := by
      intro hscore
      exact habove (by
        rw [mul_comm]
        exact (lt_div_iff₀ (hcost_pos item)).mp hscore)
    simp [habove, hscore_not]

/-- Boundary cost is the finite atom boundary mass. -/
theorem boundaryCost_eq_finiteAtomBoundaryMass
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.boundaryCost t =
      finiteAtomBoundaryMass D.atomScore D.costAtomMass t := by
  classical
  simp only [boundaryCost, finiteAtomBoundaryMass, atomScore, costAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  have heq_iff :
      D.posteriorUtility item state = D.allocCost item * t ↔
        D.posteriorUtility item state / D.allocCost item = t := by
    rw [mul_comm]
    exact (div_eq_iff (ne_of_gt (hcost_pos item))).symm
  by_cases heq : D.posteriorUtility item state = D.allocCost item * t
  · have hscore : D.posteriorUtility item state / D.allocCost item = t :=
      heq_iff.mp heq
    rw [if_pos heq, if_pos hscore]
  · have hscore_not :
        D.posteriorUtility item state / D.allocCost item ≠ t := by
      intro hscore
      exact heq (heq_iff.mpr hscore)
    rw [if_neg heq, if_neg hscore_not]
    simp

/-- Strict-above utility is the finite atom strict-above utility mass. -/
theorem strictAbovePosteriorUtility_eq_finiteAtomStrictAboveMass
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.strictAbovePosteriorUtility t =
      finiteAtomStrictAboveMass D.atomScore D.utilityAtomMass t := by
  classical
  simp only [strictAbovePosteriorUtility, finiteAtomStrictAboveMass, atomScore,
    utilityAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  by_cases habove : D.allocCost item * t < D.posteriorUtility item state
  · have hscore : t < D.posteriorUtility item state / D.allocCost item := by
      rw [lt_div_iff₀ (hcost_pos item), mul_comm]
      exact habove
    simp [habove, hscore]
  · have hscore_not :
        ¬ t < D.posteriorUtility item state / D.allocCost item := by
      intro hscore
      exact habove (by
        rw [mul_comm]
        exact (lt_div_iff₀ (hcost_pos item)).mp hscore)
    simp [habove, hscore_not]

/-- Boundary utility is the finite atom boundary utility mass. -/
theorem boundaryPosteriorUtility_eq_finiteAtomBoundaryMass
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.boundaryPosteriorUtility t =
      finiteAtomBoundaryMass D.atomScore D.utilityAtomMass t := by
  classical
  simp only [boundaryPosteriorUtility, finiteAtomBoundaryMass, atomScore,
    utilityAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  have heq_iff :
      D.posteriorUtility item state = D.allocCost item * t ↔
        D.posteriorUtility item state / D.allocCost item = t := by
    rw [mul_comm]
    exact (div_eq_iff (ne_of_gt (hcost_pos item))).symm
  by_cases heq : D.posteriorUtility item state = D.allocCost item * t
  · have hscore : D.posteriorUtility item state / D.allocCost item = t :=
      heq_iff.mp heq
    rw [if_pos heq, if_pos hscore]
  · have hscore_not :
        D.posteriorUtility item state / D.allocCost item ≠ t := by
      intro hscore
      exact heq (heq_iff.mpr hscore)
    rw [if_neg heq, if_neg hscore_not]
    simp

/-- Expected cost as a finite atom sum weighted by the policy. -/
theorem expectedCost_eq_finiteAtomPolicyMass
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) :
    D.expectedCost policy =
      ∑ atom : ThresholdAtom Applicant State,
        D.costAtomMass atom * policy atom.2 atom.1 := by
  classical
  simp only [expectedCost, costAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/-- Expected posterior utility as a finite atom sum weighted by the policy. -/
theorem expectedPosteriorUtility_eq_finiteAtomPolicyMass
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) :
    D.expectedPosteriorUtility policy =
      ∑ atom : ThresholdAtom Applicant State,
        D.utilityAtomMass atom * policy atom.2 atom.1 := by
  classical
  simp only [expectedPosteriorUtility, utilityAtomMass]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/--
The positive-part reduction of a finite allocation policy.

It keeps the original allocation probability on atoms with strictly positive
posterior utility and allocates zero on nonpositive-utility atoms.
-/
noncomputable def positivePartPolicy
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) :
    AllocationPolicy Applicant State :=
  fun item state =>
    if 0 < D.posteriorUtility item state then
      policy item state
    else
      0

/-- Positive-part reduction preserves allocation-policy bounds. -/
theorem positivePartPolicy_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hpolicy : AllocationPolicyBounds policy) :
    AllocationPolicyBounds (D.positivePartPolicy policy) := by
  intro item state
  by_cases hpos : 0 < D.posteriorUtility item state
  · simpa [positivePartPolicy, hpos] using hpolicy item state
  · exact ⟨by simp [positivePartPolicy, hpos],
      by simp [positivePartPolicy, hpos]⟩

/-- Positive-part reduction is pointwise no larger than the original policy. -/
theorem positivePartPolicy_le_policy
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hpolicy : AllocationPolicyBounds policy) :
    ∀ item state,
      D.positivePartPolicy policy item state ≤ policy item state := by
  intro item state
  by_cases hpos : 0 < D.posteriorUtility item state
  · simp [positivePartPolicy, hpos]
  · simpa [positivePartPolicy, hpos] using (hpolicy item state).1

/- On a nonzero positive-part atom, posterior utility is strictly positive. -/
theorem positivePartPolicy_pos_utility_of_ne_zero
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    {item : Applicant} {state : State}
    (hne : D.positivePartPolicy policy item state ≠ 0) :
    0 < D.posteriorUtility item state := by
  by_contra hnot
  exact hne (by simp [positivePartPolicy, hnot])

/--
Removing nonpositive-utility atoms cannot decrease expected posterior utility
when state weights and allocation probabilities are nonnegative.
-/
theorem expectedPosteriorUtility_le_positivePartPolicy
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤
      D.expectedPosteriorUtility (D.positivePartPolicy policy) := by
  classical
  rw [D.expectedPosteriorUtility_eq_finiteAtomPolicyMass policy]
  rw [D.expectedPosteriorUtility_eq_finiteAtomPolicyMass
    (D.positivePartPolicy policy)]
  refine Finset.sum_le_sum ?_
  intro atom _
  by_cases hpos : 0 < D.posteriorUtility atom.2 atom.1
  · simp [positivePartPolicy, hpos]
  · have hutility_nonpos :
        D.posteriorUtility atom.2 atom.1 ≤ 0 := le_of_not_gt hpos
    have hmass_nonpos : D.utilityAtomMass atom ≤ 0 := by
      simpa [utilityAtomMass] using
        mul_nonpos_of_nonneg_of_nonpos (hweight atom.1) hutility_nonpos
    have hterm_nonpos :
        D.utilityAtomMass atom * policy atom.2 atom.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmass_nonpos
        (hpolicy atom.2 atom.1).1
    simpa [positivePartPolicy, hpos] using hterm_nonpos

/-- Positive-part reduction cannot increase expected allocation cost. -/
theorem expectedCost_positivePartPolicy_le
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedCost (D.positivePartPolicy policy) ≤ D.expectedCost policy := by
  classical
  rw [D.expectedCost_eq_finiteAtomPolicyMass (D.positivePartPolicy policy)]
  rw [D.expectedCost_eq_finiteAtomPolicyMass policy]
  refine Finset.sum_le_sum ?_
  intro atom _
  have hmass_nonneg : 0 ≤ D.costAtomMass atom := by
    simpa [costAtomMass] using
      mul_nonneg (hweight atom.1) (hcost_nonneg atom.2)
  exact mul_le_mul_of_nonneg_left
    (D.positivePartPolicy_le_policy policy hpolicy atom.2 atom.1)
    hmass_nonneg

/--
Finite signed positive-part reduction for the equality-target proof chain.

Given a bounded allocation whose expected utility is a nonnegative target,
zeroing all nonpositive-utility atoms preserves enough utility for the target,
does not increase cost, and leaves support only on strictly positive utility
atoms.
-/
theorem finitePositivePartPolicy_cost_le
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (target : ℝ)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hpolicy : AllocationPolicyBounds policy)
    (htarget_nonneg : 0 ≤ target)
    (htarget_eq : D.expectedPosteriorUtility policy = target) :
    AllocationPolicyBounds (D.positivePartPolicy policy) ∧
      0 ≤ target ∧
      target ≤ D.expectedPosteriorUtility (D.positivePartPolicy policy) ∧
      D.expectedCost (D.positivePartPolicy policy) ≤ D.expectedCost policy ∧
      (∀ item state,
        D.positivePartPolicy policy item state ≠ 0 →
          0 < D.posteriorUtility item state) := by
  refine ⟨D.positivePartPolicy_bounds policy hpolicy, htarget_nonneg, ?_, ?_, ?_⟩
  · calc
      target = D.expectedPosteriorUtility policy := htarget_eq.symm
      _ ≤ D.expectedPosteriorUtility (D.positivePartPolicy policy) :=
        D.expectedPosteriorUtility_le_positivePartPolicy
          policy hweight hpolicy
  · exact D.expectedCost_positivePartPolicy_le
      policy hweight (fun item => (hcost_pos item).le) hpolicy
  · intro item state hne
    exact D.positivePartPolicy_pos_utility_of_ne_zero policy hne

/-- Cost atom masses are nonnegative under nonnegative weights and costs. -/
theorem costAtomMass_nonneg
    (D : CostAwareThresholdData Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item) :
    ∀ atom : ThresholdAtom Applicant State, 0 ≤ D.costAtomMass atom := by
  intro atom
  exact mul_nonneg (hweight atom.1) (hcost_nonneg atom.2)

/-- Utility atom masses are nonnegative under nonnegative weights/utilities. -/
theorem utilityAtomMass_nonneg
    (D : CostAwareThresholdData Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state) :
    ∀ atom : ThresholdAtom Applicant State, 0 ≤ D.utilityAtomMass atom := by
  intro atom
  exact mul_nonneg (hweight atom.1) (hutility_nonneg atom.2 atom.1)

/--
Positive-utility atom mass for the signed finite Lemma 3 route.

Atoms with nonpositive posterior utility are deliberately assigned zero mass;
this avoids smuggling pointwise utility nonnegativity into the signed statement.
-/
noncomputable def positiveUtilityAtomMass
    (D : CostAwareThresholdData Applicant State)
    (atom : ThresholdAtom Applicant State) : ℝ :=
  if 0 < D.posteriorUtility atom.2 atom.1 then D.utilityAtomMass atom else 0

/-- Positive-utility atom mass is nonnegative under nonnegative state weights. -/
theorem positiveUtilityAtomMass_nonneg
    (D : CostAwareThresholdData Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state) :
    ∀ atom : ThresholdAtom Applicant State,
      0 ≤ D.positiveUtilityAtomMass atom := by
  intro atom
  classical
  by_cases hutility_pos : 0 < D.posteriorUtility atom.2 atom.1
  · have hmass_nonneg : 0 ≤ D.utilityAtomMass atom := by
      exact mul_nonneg (hweight atom.1) hutility_pos.le
    simpa [positiveUtilityAtomMass, hutility_pos] using hmass_nonneg
  · simp [positiveUtilityAtomMass, hutility_pos]

/-- Positive-utility mass selected by a policy. -/
noncomputable def positiveUtilityPolicyMass
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  ∑ atom : ThresholdAtom Applicant State,
    D.positiveUtilityAtomMass atom * policy atom.2 atom.1

/--
A bounded policy's signed expected utility is bounded above by its selected
positive-utility mass.  Negative and zero utility atoms can only lower the
signed expectation.
-/
theorem expectedPosteriorUtility_le_positiveUtilityPolicyMass_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤
      D.positiveUtilityPolicyMass policy := by
  classical
  rw [D.expectedPosteriorUtility_eq_finiteAtomPolicyMass policy]
  simp only [positiveUtilityPolicyMass]
  refine Finset.sum_le_sum ?_
  intro atom _
  by_cases hutility_pos : 0 < D.posteriorUtility atom.2 atom.1
  · simp [positiveUtilityAtomMass, hutility_pos]
  · have hutility_nonpos : D.posteriorUtility atom.2 atom.1 ≤ 0 :=
      le_of_not_gt hutility_pos
    have hmass_nonpos : D.utilityAtomMass atom ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hweight atom.1) hutility_nonpos
    have hpolicy_nonneg : 0 ≤ policy atom.2 atom.1 :=
      (hpolicy atom.2 atom.1).1
    have hterm_nonpos :
        D.utilityAtomMass atom * policy atom.2 atom.1 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hmass_nonpos hpolicy_nonneg
    simpa [positiveUtilityAtomMass, hutility_pos] using hterm_nonpos

/-- A bounded policy selects at most the total positive-utility atom mass. -/
theorem positiveUtilityPolicyMass_le_total_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hpolicy : AllocationPolicyBounds policy) :
    D.positiveUtilityPolicyMass policy ≤
      finiteAtomTotalMass D.positiveUtilityAtomMass := by
  classical
  simp only [positiveUtilityPolicyMass, finiteAtomTotalMass]
  exact Finset.sum_le_sum fun atom _ =>
    mul_le_of_le_one_right
      (D.positiveUtilityAtomMass_nonneg hweight atom)
      (hpolicy atom.2 atom.1).2

/--
The expected utility of a bounded signed policy is at most the available
positive-utility atom mass.
-/
theorem expectedPosteriorUtility_le_positiveUtilityTotalMass_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤
      finiteAtomTotalMass D.positiveUtilityAtomMass :=
  (D.expectedPosteriorUtility_le_positiveUtilityPolicyMass_of_bounds
      policy hweight hpolicy).trans
    (D.positiveUtilityPolicyMass_le_total_of_bounds policy hweight hpolicy)

/--
For a strictly positive threshold, the strict-above positive-utility atom mass
equals the ordinary signed utility mass: positive cost makes every selected
atom's posterior utility strictly positive.
-/
theorem finiteAtomStrictAboveMass_positiveUtilityAtomMass_eq
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) (ht_pos : 0 < t) :
    finiteAtomStrictAboveMass D.atomScore D.positiveUtilityAtomMass t =
      finiteAtomStrictAboveMass D.atomScore D.utilityAtomMass t := by
  classical
  simp only [finiteAtomStrictAboveMass]
  refine Finset.sum_congr rfl ?_
  intro atom _
  by_cases hscore : t < D.atomScore atom
  · have hscore_pos : 0 < D.posteriorUtility atom.2 atom.1 / D.allocCost atom.2 := by
      simpa [atomScore] using lt_trans ht_pos hscore
    have hutility_pos : 0 < D.posteriorUtility atom.2 atom.1 := by
      have hmul :=
        mul_lt_mul_of_pos_right hscore_pos (hcost_pos atom.2)
      simpa [div_mul_cancel₀ _ (ne_of_gt (hcost_pos atom.2))] using hmul
    simp [hscore, positiveUtilityAtomMass, hutility_pos]
  · simp [hscore]

/--
For a strictly positive threshold, the boundary positive-utility atom mass
equals the ordinary signed utility boundary mass.
-/
theorem finiteAtomBoundaryMass_positiveUtilityAtomMass_eq
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item) (ht_pos : 0 < t) :
    finiteAtomBoundaryMass D.atomScore D.positiveUtilityAtomMass t =
      finiteAtomBoundaryMass D.atomScore D.utilityAtomMass t := by
  classical
  simp only [finiteAtomBoundaryMass]
  refine Finset.sum_congr rfl ?_
  intro atom _
  by_cases hscore : D.atomScore atom = t
  · have hscore_pos :
        0 < D.posteriorUtility atom.2 atom.1 / D.allocCost atom.2 := by
      have hscore_pos' : 0 < D.atomScore atom := by
        simpa [hscore] using ht_pos
      simpa [atomScore] using hscore_pos'
    have hutility_pos : 0 < D.posteriorUtility atom.2 atom.1 := by
      have hmul :=
        mul_lt_mul_of_pos_right hscore_pos (hcost_pos atom.2)
      simpa [div_mul_cancel₀ _ (ne_of_gt (hcost_pos atom.2))] using hmul
    simp [hscore, positiveUtilityAtomMass, hutility_pos]
  · simp [hscore]

/--
Positive boundary mass for the positive-utility atom measure can only appear at
a positive score threshold.
-/
theorem threshold_pos_of_positiveUtilityAtomBoundaryMass_pos
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hboundary :
      0 < finiteAtomBoundaryMass D.atomScore D.positiveUtilityAtomMass t) :
    0 < t := by
  classical
  have hzero_sum :
      (∑ atom : ThresholdAtom Applicant State, (0 : ℝ)) <
        ∑ atom : ThresholdAtom Applicant State,
          if D.atomScore atom = t then
            D.positiveUtilityAtomMass atom
          else
            0 := by
    simpa [finiteAtomBoundaryMass] using hboundary
  rcases Finset.exists_lt_of_sum_lt hzero_sum with ⟨atom, _, hterm_pos⟩
  by_cases hscore : D.atomScore atom = t
  · have hmass_pos : 0 < D.positiveUtilityAtomMass atom := by
      simpa [hscore] using hterm_pos
    by_cases hutility_pos : 0 < D.posteriorUtility atom.2 atom.1
    · have hscore_pos : 0 < D.atomScore atom := by
        dsimp [atomScore]
        exact div_pos hutility_pos (hcost_pos atom.2)
      simpa [hscore] using hscore_pos
    · simp [positiveUtilityAtomMass, hutility_pos] at hmass_pos
  · simp [hscore] at hterm_pos

/-- A finite real threshold strictly above every atom score. -/
noncomputable def finiteAtomScoreCeiling
    (D : CostAwareThresholdData Applicant State) : ℝ :=
  1 + ∑ atom : ThresholdAtom Applicant State, |D.atomScore atom|

/-- The finite score ceiling is strictly positive. -/
theorem finiteAtomScoreCeiling_pos
    (D : CostAwareThresholdData Applicant State) :
    0 < D.finiteAtomScoreCeiling := by
  classical
  have hsum_nonneg :
      0 ≤ ∑ atom : ThresholdAtom Applicant State, |D.atomScore atom| :=
    Finset.sum_nonneg fun atom _ => abs_nonneg (D.atomScore atom)
  dsimp [finiteAtomScoreCeiling]
  linarith

/-- Every atom score is strictly below the finite score ceiling. -/
theorem atomScore_lt_finiteAtomScoreCeiling
    (D : CostAwareThresholdData Applicant State) :
    ∀ atom : ThresholdAtom Applicant State,
      D.atomScore atom < D.finiteAtomScoreCeiling := by
  classical
  intro atom
  have hterm_nonneg :
      ∀ x ∈ (Finset.univ : Finset (ThresholdAtom Applicant State)),
        0 ≤ |D.atomScore x| := by
    intro x _
    exact abs_nonneg (D.atomScore x)
  have hle_sum :
      |D.atomScore atom| ≤
        ∑ x : ThresholdAtom Applicant State, |D.atomScore x| :=
    Finset.single_le_sum hterm_nonneg (Finset.mem_univ atom)
  have hscore_le_abs : D.atomScore atom ≤ |D.atomScore atom| :=
    le_abs_self (D.atomScore atom)
  dsimp [finiteAtomScoreCeiling]
  linarith

/-- The score-ceiling threshold with zero boundary randomization allocates nothing. -/
theorem singleThresholdPolicy_finiteAtomScoreCeiling_eq_zero
    (D : CostAwareThresholdData Applicant State)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.singleThresholdPolicy D.finiteAtomScoreCeiling 0 =
      fun _ _ => 0 := by
  classical
  funext item state
  have hscore :
      D.posteriorUtility item state / D.allocCost item <
        D.finiteAtomScoreCeiling := by
    simpa [atomScore] using
      D.atomScore_lt_finiteAtomScoreCeiling
        (atom := (state, item))
  have hbelow :
      D.posteriorUtility item state <
        D.allocCost item * D.finiteAtomScoreCeiling := by
    have hmul := (div_lt_iff₀ (hcost_pos item)).mp hscore
    simpa [mul_comm] using hmul
  have hnot_above :
      ¬ D.allocCost item * D.finiteAtomScoreCeiling <
        D.posteriorUtility item state :=
    not_lt.mpr hbelow.le
  simp [singleThresholdPolicy, hnot_above, hbelow]

/-- A bounded allocation has nonnegative expected cost. -/
theorem expectedCost_nonneg_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy : AllocationPolicyBounds policy) :
    0 ≤ D.expectedCost policy := by
  rw [D.expectedCost_eq_finiteAtomPolicyMass policy]
  exact Finset.sum_nonneg fun atom _ =>
    mul_nonneg
      (D.costAtomMass_nonneg hweight hcost_nonneg atom)
      (hpolicy atom.2 atom.1).1

/-- A bounded allocation's expected cost is at most total cost atom mass. -/
theorem expectedCost_le_finiteAtomTotalMass_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedCost policy ≤ finiteAtomTotalMass D.costAtomMass := by
  rw [D.expectedCost_eq_finiteAtomPolicyMass policy]
  simp only [finiteAtomTotalMass]
  exact Finset.sum_le_sum fun atom _ =>
    mul_le_of_le_one_right
      (D.costAtomMass_nonneg hweight hcost_nonneg atom)
      (hpolicy atom.2 atom.1).2

/-- A bounded allocation has nonnegative expected posterior utility. -/
theorem expectedPosteriorUtility_nonneg_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hpolicy : AllocationPolicyBounds policy) :
    0 ≤ D.expectedPosteriorUtility policy := by
  rw [D.expectedPosteriorUtility_eq_finiteAtomPolicyMass policy]
  exact Finset.sum_nonneg fun atom _ =>
    mul_nonneg
      (D.utilityAtomMass_nonneg hweight hutility_nonneg atom)
      (hpolicy atom.2 atom.1).1

/--
A bounded allocation's expected posterior utility is at most total utility atom
mass.
-/
theorem expectedPosteriorUtility_le_finiteAtomTotalMass_of_bounds
    (D : CostAwareThresholdData Applicant State)
    (policy : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hpolicy : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤ finiteAtomTotalMass D.utilityAtomMass := by
  rw [D.expectedPosteriorUtility_eq_finiteAtomPolicyMass policy]
  simp only [finiteAtomTotalMass]
  exact Finset.sum_le_sum fun atom _ =>
    mul_le_of_le_one_right
      (D.utilityAtomMass_nonneg hweight hutility_nonneg atom)
      (hpolicy atom.2 atom.1).2

/--
The canonical threshold policy's expected cost is affine in its boundary
randomization probability.
-/
theorem expectedCost_singleThresholdPolicy_eq
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ) :
    D.expectedCost (D.singleThresholdPolicy t alpha) =
      D.strictAboveCost t + alpha * D.boundaryCost t := by
  classical
  let aboveSum : State → ℝ := fun state =>
    ∑ item : Applicant,
      if D.allocCost item * t < D.posteriorUtility item state then
        D.allocCost item
      else
        0
  let boundarySum : State → ℝ := fun state =>
    ∑ item : Applicant,
      if D.posteriorUtility item state = D.allocCost item * t then
        D.allocCost item
      else
        0
  have hinner :
      ∀ state,
        (∑ item : Applicant,
          D.allocCost item *
            D.singleThresholdPolicy t alpha item state) =
          aboveSum state + alpha * boundarySum state := by
    intro state
    calc
      (∑ item : Applicant,
        D.allocCost item *
          D.singleThresholdPolicy t alpha item state)
          =
          ∑ item : Applicant,
            ((if D.allocCost item * t < D.posteriorUtility item state then
                D.allocCost item
              else
                0) +
              alpha *
                (if D.posteriorUtility item state = D.allocCost item * t then
                  D.allocCost item
                else
                  0)) := by
        refine Finset.sum_congr rfl ?_
        intro item _
        by_cases habove :
            D.allocCost item * t < D.posteriorUtility item state
        · have hne :
              D.posteriorUtility item state ≠ D.allocCost item * t := by
            exact ne_of_gt habove
          simp [singleThresholdPolicy, habove, hne]
        · by_cases hbelow :
              D.posteriorUtility item state < D.allocCost item * t
          · have hne :
                D.posteriorUtility item state ≠ D.allocCost item * t := by
              exact ne_of_lt hbelow
            simp [singleThresholdPolicy, habove, hbelow, hne]
          · have heq :
                D.posteriorUtility item state = D.allocCost item * t :=
              le_antisymm (le_of_not_gt habove) (le_of_not_gt hbelow)
            simp [singleThresholdPolicy, heq]
            ring
      _ =
          aboveSum state + alpha * boundarySum state := by
        simp only [aboveSum, boundarySum]
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
  simp only [expectedCost]
  calc
    (∑ state : State,
      D.weight state *
        ∑ item : Applicant,
          D.allocCost item *
            D.singleThresholdPolicy t alpha item state)
        =
        ∑ state : State,
          D.weight state * (aboveSum state + alpha * boundarySum state) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      rw [hinner state]
    _ =
        D.strictAboveCost t + alpha * D.boundaryCost t := by
      have hsplit :
          (∑ state : State,
            D.weight state * (aboveSum state + alpha * boundarySum state)) =
            (∑ state : State, D.weight state * aboveSum state) +
              ∑ state : State,
                D.weight state * (alpha * boundarySum state) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro state _
        ring
      have hsecond :
          (∑ state : State,
            D.weight state * (alpha * boundarySum state)) =
            alpha *
              ∑ state : State, D.weight state * boundarySum state := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro state _
        ring
      simp only [strictAboveCost, boundaryCost, aboveSum, boundarySum]
      rw [hsplit, hsecond]

/--
Boundary randomization hits any posterior-utility target between the strict
above-threshold utility and the closed-threshold utility.
-/
theorem exists_alpha_singleThresholdPolicy_expectedPosteriorUtility_eq
    (D : CostAwareThresholdData Applicant State) (t target : ℝ)
    (hboundary : 0 < D.boundaryPosteriorUtility t)
    (hlower : D.strictAbovePosteriorUtility t ≤ target)
    (hupper :
      target ≤ D.strictAbovePosteriorUtility t +
        D.boundaryPosteriorUtility t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedPosteriorUtility (D.singleThresholdPolicy t alpha) =
          target := by
  let alpha : ℝ :=
    (target - D.strictAbovePosteriorUtility t) /
      D.boundaryPosteriorUtility t
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr hlower) hboundary.le
  have halpha_le_one : alpha ≤ 1 := by
    dsimp [alpha]
    have hnum :
        target - D.strictAbovePosteriorUtility t ≤
          D.boundaryPosteriorUtility t := by
      linarith
    exact (div_le_one hboundary).mpr hnum
  have halpha_mul :
      alpha * D.boundaryPosteriorUtility t =
        target - D.strictAbovePosteriorUtility t := by
    dsimp [alpha]
    field_simp [ne_of_gt hboundary]
  refine ⟨alpha, halpha_nonneg, halpha_le_one, ?_⟩
  rw [D.expectedPosteriorUtility_singleThresholdPolicy_eq]
  linarith

/--
Boundary randomization hits any cost target between the strict above-threshold
cost and the closed-threshold cost.
-/
theorem exists_alpha_singleThresholdPolicy_expectedCost_eq
    (D : CostAwareThresholdData Applicant State) (t target : ℝ)
    (hboundary : 0 < D.boundaryCost t)
    (hlower : D.strictAboveCost t ≤ target)
    (hupper : target ≤ D.strictAboveCost t + D.boundaryCost t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedCost (D.singleThresholdPolicy t alpha) = target := by
  let alpha : ℝ := (target - D.strictAboveCost t) / D.boundaryCost t
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr hlower) hboundary.le
  have halpha_le_one : alpha ≤ 1 := by
    dsimp [alpha]
    have hnum : target - D.strictAboveCost t ≤ D.boundaryCost t := by
      linarith
    exact (div_le_one hboundary).mpr hnum
  have halpha_mul : alpha * D.boundaryCost t = target - D.strictAboveCost t := by
    dsimp [alpha]
    field_simp [ne_of_gt hboundary]
  refine ⟨alpha, halpha_nonneg, halpha_le_one, ?_⟩
  rw [D.expectedCost_singleThresholdPolicy_eq]
  linarith

/--
Boundary randomization hits any posterior-utility target bracketed by the
strict and closed threshold values. This variant also covers atomless
thresholds, where the boundary mass is zero.
-/
theorem exists_alpha_singleThresholdPolicy_expectedPosteriorUtility_eq_of_closed_bracket
    (D : CostAwareThresholdData Applicant State) (t target : ℝ)
    (hlower : D.strictAbovePosteriorUtility t ≤ target)
    (hupper :
      target ≤ D.strictAbovePosteriorUtility t +
        D.boundaryPosteriorUtility t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedPosteriorUtility (D.singleThresholdPolicy t alpha) =
          target := by
  have hlow_le_high :
      D.strictAbovePosteriorUtility t ≤
        D.strictAbovePosteriorUtility t +
          D.boundaryPosteriorUtility t :=
    hlower.trans hupper
  rcases exists_unit_interval_interpolation
      hlow_le_high hlower hupper with
    ⟨alpha, halpha_nonneg, halpha_le_one, halpha⟩
  have halpha' :
      D.strictAbovePosteriorUtility t +
          alpha * D.boundaryPosteriorUtility t =
        target := by
    calc
      D.strictAbovePosteriorUtility t +
          alpha * D.boundaryPosteriorUtility t =
          D.strictAbovePosteriorUtility t +
            alpha *
              ((D.strictAbovePosteriorUtility t +
                  D.boundaryPosteriorUtility t) -
                D.strictAbovePosteriorUtility t) := by
            ring
      _ = target := halpha
  refine ⟨alpha, halpha_nonneg, halpha_le_one, ?_⟩
  rw [D.expectedPosteriorUtility_singleThresholdPolicy_eq]
  exact halpha'

/--
Boundary randomization hits any cost target bracketed by the strict and closed
threshold values. This variant also covers atomless thresholds, where the
boundary mass is zero.
-/
theorem exists_alpha_singleThresholdPolicy_expectedCost_eq_of_closed_bracket
    (D : CostAwareThresholdData Applicant State) (t target : ℝ)
    (hlower : D.strictAboveCost t ≤ target)
    (hupper : target ≤ D.strictAboveCost t + D.boundaryCost t) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        D.expectedCost (D.singleThresholdPolicy t alpha) = target := by
  have hlow_le_high :
      D.strictAboveCost t ≤ D.strictAboveCost t + D.boundaryCost t :=
    hlower.trans hupper
  rcases exists_unit_interval_interpolation
      hlow_le_high hlower hupper with
    ⟨alpha, halpha_nonneg, halpha_le_one, halpha⟩
  have halpha' :
      D.strictAboveCost t + alpha * D.boundaryCost t = target := by
    calc
      D.strictAboveCost t + alpha * D.boundaryCost t =
          D.strictAboveCost t +
            alpha * ((D.strictAboveCost t + D.boundaryCost t) -
              D.strictAboveCost t) := by
            ring
      _ = target := halpha
  refine ⟨alpha, halpha_nonneg, halpha_le_one, ?_⟩
  rw [D.expectedCost_singleThresholdPolicy_eq]
  exact halpha'

/-- A single cost-aware threshold policy is an allocation policy. -/
theorem singleCostAwareThresholdPolicy_bounds
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold : AllocationPolicy Applicant State)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold) :
    AllocationPolicyBounds threshold := by
  classical
  rcases hthreshold with ⟨halpha_nonneg, halpha_le_one, hcases⟩
  intro item state
  rcases lt_trichotomy (D.posteriorUtility item state)
      (D.allocCost item * t) with hbelow | heq | habove
  · have hzero : threshold item state = 0 := (hcases item state).2.2 hbelow
    simp [hzero]
  · have halpha : threshold item state = alpha := (hcases item state).2.1 heq
    exact ⟨by simpa [halpha] using halpha_nonneg,
      by simpa [halpha] using halpha_le_one⟩
  · have hone : threshold item state = 1 := (hcases item state).1 habove
    simp [hone]

/-- An endpoint-aware cost-aware threshold policy is an allocation policy. -/
theorem singleCostAwareExtendedThresholdPolicy_bounds
    (D : CostAwareThresholdData Applicant State)
    (threshold : RealThreshold) (alpha : ℝ)
    (policy : AllocationPolicy Applicant State)
    (hthreshold :
      D.IsSingleCostAwareExtendedThresholdPolicy threshold alpha policy) :
    AllocationPolicyBounds policy := by
  cases threshold with
  | negInf =>
      rcases hthreshold with ⟨_, _, hall⟩
      intro item state
      simp [hall item state]
  | finite t =>
      exact D.singleCostAwareThresholdPolicy_bounds t alpha policy hthreshold
  | posInf =>
      rcases hthreshold with ⟨_, _, hall⟩
      intro item state
      simp [hall item state]

/-- Positive deltas from a threshold policy occur only weakly above threshold. -/
theorem threshold_bound_le_posteriorUtility_of_delta_pos
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant State)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    ∀ item state,
      0 < threshold item state - other item state →
        D.allocCost item * t ≤ D.posteriorUtility item state := by
  classical
  rcases hthreshold with ⟨_, _, hcases⟩
  intro item state hdelta
  by_contra hnot
  have hbelow : D.posteriorUtility item state < D.allocCost item * t :=
    lt_of_not_ge hnot
  have hzero : threshold item state = 0 := (hcases item state).2.2 hbelow
  have hother_nonneg : 0 ≤ other item state := (hother item state).1
  rw [hzero] at hdelta
  linarith

/-- Negative deltas from a threshold policy occur only weakly below threshold. -/
theorem posteriorUtility_le_threshold_bound_of_delta_neg
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant State)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    ∀ item state,
      threshold item state - other item state < 0 →
        D.posteriorUtility item state ≤ D.allocCost item * t := by
  classical
  rcases hthreshold with ⟨_, _, hcases⟩
  intro item state hdelta
  by_contra hnot
  have habove : D.allocCost item * t < D.posteriorUtility item state :=
    lt_of_not_ge hnot
  have hone : threshold item state = 1 := (hcases item state).1 habove
  have hother_le_one : other item state ≤ 1 := (hother item state).2
  rw [hone] at hdelta
  linarith

/-- Difference in expected posterior utility is the weighted value delta. -/
theorem expectedPosteriorUtility_sub_eq_weightedDeltaValue
    (D : CostAwareThresholdData Applicant State)
    (threshold other : AllocationPolicy Applicant State) :
    D.expectedPosteriorUtility threshold - D.expectedPosteriorUtility other =
      weightedDeltaValue D.weight D.posteriorUtility threshold other := by
  classical
  simp only [expectedPosteriorUtility, weightedDeltaValue]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/-- Difference in expected cost is the weighted cost delta. -/
theorem expectedCost_sub_eq_weightedDeltaCost
    (D : CostAwareThresholdData Applicant State)
    (threshold other : AllocationPolicy Applicant State) :
    D.expectedCost threshold - D.expectedCost other =
      weightedDeltaCost D.weight D.allocCost threshold other := by
  classical
  simp only [expectedCost, weightedDeltaCost]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro state _
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/--
Appendix Lemma 1 key inequality:
`E[sum_i (T_i - A_i) \hat U_i] >=
 t * E[sum_i c_i (T_i - A_i)]`.
-/
theorem singleCostAwareThreshold_expected_delta_key
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    t * (D.expectedCost threshold - D.expectedCost other) ≤
      D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other := by
  have hmain :=
    mul_weightedDeltaCost_le_weightedDeltaValue
      D.weight D.posteriorUtility D.allocCost threshold other t hweight
      (D.threshold_bound_le_posteriorUtility_of_delta_pos
        t alpha threshold other hthreshold hother)
      (D.posteriorUtility_le_threshold_bound_of_delta_neg
        t alpha threshold other hthreshold hother)
  rwa [D.expectedCost_sub_eq_weightedDeltaCost threshold other,
    D.expectedPosteriorUtility_sub_eq_weightedDeltaValue threshold other]

/--
Appendix Lemma 1, Case 1: at the same expected cost, a single-threshold
cost-aware policy has weakly higher expected posterior utility.
-/
theorem singleCostAwareThreshold_expectedPosteriorUtility_ge_of_expectedCost_eq
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other)
    (hcost : D.expectedCost threshold = D.expectedCost other) :
    D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility threshold := by
  have hkey :=
    D.singleCostAwareThreshold_expected_delta_key
      t alpha threshold other hweight hthreshold hother
  have hcost_zero :
      D.expectedCost threshold - D.expectedCost other = 0 := by
    linarith
  rw [hcost_zero, mul_zero] at hkey
  linarith

/--
Appendix Lemma 1, Case 2: at the same expected posterior utility, a
positive-threshold cost-aware policy has weakly lower expected cost.
-/
theorem singleCostAwareThreshold_expectedCost_le_of_expectedPosteriorUtility_eq
    (D : CostAwareThresholdData Applicant State) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant State)
    (ht : 0 < t)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other)
    (hutility :
      D.expectedPosteriorUtility threshold =
        D.expectedPosteriorUtility other) :
    D.expectedCost threshold ≤ D.expectedCost other := by
  have hkey :=
    D.singleCostAwareThreshold_expected_delta_key
      t alpha threshold other hweight hthreshold hother
  have hutility_zero :
      D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other = 0 := by
    linarith
  rw [hutility_zero] at hkey
  have hcost_nonpos :
      D.expectedCost threshold - D.expectedCost other ≤ 0 := by
    have hmul :
        (D.expectedCost threshold - D.expectedCost other) * t ≤ 0 := by
      simpa [mul_comm] using hkey
    exact nonpos_of_mul_nonpos_left hmul ht
  linarith

/--
Certificate form of the source Lemma 2 cost-attainment output for one group:
it stores a cost-aware threshold policy with the same expected cost as an
original allocation policy.
-/
structure SameCostThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State) where
  t : ℝ
  alpha : ℝ
  threshold : AllocationPolicy Applicant State
  threshold_policy : D.IsSingleCostAwareThresholdPolicy t alpha threshold
  same_cost : D.expectedCost threshold = D.expectedCost original

/--
Once a same-cost threshold replacement is available, Lemma 1 proves that it
weakly improves expected posterior utility.
-/
theorem sameCostThresholdReplacement_expectedPosteriorUtility_ge
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (C : D.SameCostThresholdReplacement original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (horiginal : AllocationPolicyBounds original) :
    D.expectedPosteriorUtility original ≤
      D.expectedPosteriorUtility C.threshold :=
  D.singleCostAwareThreshold_expectedPosteriorUtility_ge_of_expectedCost_eq
    C.t C.alpha C.threshold original hweight C.threshold_policy horiginal
    C.same_cost

/--
Certificate form of the source Lemma 2 utility-attainment output for one
group: it stores a positive-threshold cost-aware policy with the same expected
posterior utility as an original allocation policy.
-/
structure SameUtilityThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State) where
  t : ℝ
  alpha : ℝ
  threshold : AllocationPolicy Applicant State
  threshold_pos : 0 < t
  threshold_policy : D.IsSingleCostAwareThresholdPolicy t alpha threshold
  same_utility :
    D.expectedPosteriorUtility threshold =
      D.expectedPosteriorUtility original

/--
Once a same-utility threshold replacement is available, Lemma 1 proves that it
weakly lowers expected cost.
-/
theorem sameUtilityThresholdReplacement_expectedCost_le
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (C : D.SameUtilityThresholdReplacement original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (horiginal : AllocationPolicyBounds original) :
    D.expectedCost C.threshold ≤ D.expectedCost original :=
  D.singleCostAwareThreshold_expectedCost_le_of_expectedPosteriorUtility_eq
    C.t C.alpha C.threshold original C.threshold_pos hweight
    C.threshold_policy horiginal C.same_utility

/--
Finite bracketing certificate for the utility part of Lemma 2.

It records a threshold whose strict-above utility and closed-threshold utility
surround the target.  The existence of such a bracket is the nontrivial
finite-support/analytic part of Lemma 2.
-/
structure UtilityThresholdBracket
    (D : CostAwareThresholdData Applicant State) (target : ℝ) where
  t : ℝ
  threshold_pos : 0 < t
  boundary_pos : 0 < D.boundaryPosteriorUtility t
  strict_le_target : D.strictAbovePosteriorUtility t ≤ target
  target_le_closed :
    target ≤ D.strictAbovePosteriorUtility t + D.boundaryPosteriorUtility t

/--
Closed-bracket certificate for the utility part of Lemma 2.

Unlike `UtilityThresholdBracket`, this version does not require positive
boundary mass, so it also covers atomless thresholds where the strict and
closed threshold values coincide.
-/
structure ClosedUtilityThresholdBracket
    (D : CostAwareThresholdData Applicant State) (target : ℝ) where
  t : ℝ
  threshold_pos : 0 < t
  strict_le_target : D.strictAbovePosteriorUtility t ≤ target
  target_le_closed :
    target ≤ D.strictAbovePosteriorUtility t + D.boundaryPosteriorUtility t

/-- A positive-boundary utility bracket is a closed utility bracket. -/
def UtilityThresholdBracket.toClosed
    (D : CostAwareThresholdData Applicant State) {target : ℝ}
    (B : D.UtilityThresholdBracket target) :
    D.ClosedUtilityThresholdBracket target where
  t := B.t
  threshold_pos := B.threshold_pos
  strict_le_target := B.strict_le_target
  target_le_closed := B.target_le_closed

/--
A utility bracketing certificate constructs a same-utility threshold
replacement.
-/
noncomputable def UtilityThresholdBracket.toSameUtilityThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (B : D.UtilityThresholdBracket (D.expectedPosteriorUtility original)) :
    D.SameUtilityThresholdReplacement original := by
  let alpha : ℝ :=
    (D.expectedPosteriorUtility original -
        D.strictAbovePosteriorUtility B.t) /
      D.boundaryPosteriorUtility B.t
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr B.strict_le_target)
      B.boundary_pos.le
  have halpha_le_one : alpha ≤ 1 := by
    dsimp [alpha]
    have hnum :
        D.expectedPosteriorUtility original -
            D.strictAbovePosteriorUtility B.t ≤
          D.boundaryPosteriorUtility B.t := by
      linarith [B.target_le_closed]
    exact (div_le_one B.boundary_pos).mpr hnum
  have halpha_mul :
      alpha * D.boundaryPosteriorUtility B.t =
        D.expectedPosteriorUtility original -
          D.strictAbovePosteriorUtility B.t := by
    dsimp [alpha]
    field_simp [ne_of_gt B.boundary_pos]
  have halpha :
      D.expectedPosteriorUtility (D.singleThresholdPolicy B.t alpha) =
        D.expectedPosteriorUtility original := by
    rw [D.expectedPosteriorUtility_singleThresholdPolicy_eq]
    linarith
  exact
    { t := B.t
      alpha := alpha
      threshold := D.singleThresholdPolicy B.t alpha
      threshold_pos := B.threshold_pos
      threshold_policy :=
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          B.t alpha halpha_nonneg halpha_le_one
      same_utility := halpha }

/--
A closed utility bracketing certificate constructs a same-utility threshold
replacement, including the atomless case where the boundary mass is zero.
-/
noncomputable def ClosedUtilityThresholdBracket.toSameUtilityThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (B : D.ClosedUtilityThresholdBracket
      (D.expectedPosteriorUtility original)) :
    D.SameUtilityThresholdReplacement original := by
  let H :=
    D.exists_alpha_singleThresholdPolicy_expectedPosteriorUtility_eq_of_closed_bracket
      B.t (D.expectedPosteriorUtility original)
      B.strict_le_target B.target_le_closed
  let alpha : ℝ := Classical.choose H
  have hspec := Classical.choose_spec H
  exact
    { t := B.t
      alpha := alpha
      threshold := D.singleThresholdPolicy B.t alpha
      threshold_pos := B.threshold_pos
      threshold_policy :=
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          B.t alpha hspec.1 hspec.2.1
      same_utility := hspec.2.2 }

/--
Zero-target signed utility replacement using a finite real cutoff above every
atom score.  This is the finite-threshold counterpart of the all-zero endpoint.
-/
noncomputable def zeroSameUtilityThresholdReplacement_of_expectedUtility_zero
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hutility_zero : D.expectedPosteriorUtility original = 0) :
    D.SameUtilityThresholdReplacement original := by
  exact
    { t := D.finiteAtomScoreCeiling
      alpha := 0
      threshold := D.singleThresholdPolicy D.finiteAtomScoreCeiling 0
      threshold_pos := D.finiteAtomScoreCeiling_pos
      threshold_policy :=
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          D.finiteAtomScoreCeiling 0 (by norm_num) (by norm_num)
      same_utility := by
        rw [D.singleThresholdPolicy_finiteAtomScoreCeiling_eq_zero hcost_pos]
        simpa [expectedPosteriorUtility] using hutility_zero.symm }

/--
Signed finite positive-target utility bracketing.  The sweep is run over only
positive-utility atom mass, then translated back to the ordinary signed utility
formula once the boundary threshold is proved positive.
-/
theorem exists_closedUtilityThresholdBracket_of_finite_signed_positive_target
    (D : CostAwareThresholdData Applicant State)
    (target : ℝ)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htarget_pos : 0 < target)
    (htarget_le_total :
      target ≤ finiteAtomTotalMass D.positiveUtilityAtomMass) :
    Nonempty (D.ClosedUtilityThresholdBracket target) := by
  classical
  have hmass_nonneg :
      ∀ atom : ThresholdAtom Applicant State,
        0 ≤ D.positiveUtilityAtomMass atom :=
    D.positiveUtilityAtomMass_nonneg hweight
  have htotal_pos : 0 < finiteAtomTotalMass D.positiveUtilityAtomMass :=
    lt_of_lt_of_le htarget_pos htarget_le_total
  rcases exists_finiteAtom_threshold_bracket
      D.atomScore D.positiveUtilityAtomMass target
      hmass_nonneg htotal_pos htarget_pos.le htarget_le_total with
    ⟨t, hboundary, hstrict, hclosed⟩
  have ht_pos : 0 < t :=
    D.threshold_pos_of_positiveUtilityAtomBoundaryMass_pos
      t hcost_pos hboundary
  refine ⟨
    { t := t
      threshold_pos := ht_pos
      strict_le_target := ?_
      target_le_closed := ?_ }⟩
  · rw [D.strictAbovePosteriorUtility_eq_finiteAtomStrictAboveMass
      t hcost_pos]
    rw [← D.finiteAtomStrictAboveMass_positiveUtilityAtomMass_eq
      t hcost_pos ht_pos]
    exact hstrict
  · rw [D.strictAbovePosteriorUtility_eq_finiteAtomStrictAboveMass
      t hcost_pos]
    rw [D.boundaryPosteriorUtility_eq_finiteAtomBoundaryMass
      t hcost_pos]
    rw [← D.finiteAtomStrictAboveMass_positiveUtilityAtomMass_eq
      t hcost_pos ht_pos]
    rw [← D.finiteAtomBoundaryMass_positiveUtilityAtomMass_eq
      t hcost_pos ht_pos]
    exact hclosed

/--
Signed finite utility replacement for a bounded policy with nonnegative
expected utility.  No pointwise utility nonnegativity or positive total utility
mass premise is used.
-/
theorem exists_sameUtilityThresholdReplacement_of_finite_signed_nonnegative_target
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : AllocationPolicyBounds original)
    (htarget_nonneg : 0 ≤ D.expectedPosteriorUtility original) :
    Nonempty (D.SameUtilityThresholdReplacement original) := by
  classical
  by_cases htarget_zero : D.expectedPosteriorUtility original = 0
  · exact
      ⟨D.zeroSameUtilityThresholdReplacement_of_expectedUtility_zero
        original hcost_pos htarget_zero⟩
  · have htarget_pos : 0 < D.expectedPosteriorUtility original :=
      lt_of_le_of_ne htarget_nonneg (Ne.symm htarget_zero)
    have htarget_le_total :
        D.expectedPosteriorUtility original ≤
          finiteAtomTotalMass D.positiveUtilityAtomMass :=
      D.expectedPosteriorUtility_le_positiveUtilityTotalMass_of_bounds
        original hweight horiginal
    rcases
        D.exists_closedUtilityThresholdBracket_of_finite_signed_positive_target
          (D.expectedPosteriorUtility original) hweight hcost_pos
          htarget_pos htarget_le_total with
      ⟨B⟩
    exact ⟨B.toSameUtilityThresholdReplacement D original⟩

/--
Finite bracketing certificate for the cost part of Lemma 2.

It records a threshold whose strict-above cost and closed-threshold cost
surround the target.
-/
structure CostThresholdBracket
    (D : CostAwareThresholdData Applicant State) (target : ℝ) where
  t : ℝ
  boundary_pos : 0 < D.boundaryCost t
  strict_le_target : D.strictAboveCost t ≤ target
  target_le_closed : target ≤ D.strictAboveCost t + D.boundaryCost t

/--
Closed-bracket certificate for the cost part of Lemma 2.

Unlike `CostThresholdBracket`, this version does not require positive boundary
mass, so it also covers atomless thresholds where the strict and closed
threshold values coincide.
-/
structure ClosedCostThresholdBracket
    (D : CostAwareThresholdData Applicant State) (target : ℝ) where
  t : ℝ
  strict_le_target : D.strictAboveCost t ≤ target
  target_le_closed : target ≤ D.strictAboveCost t + D.boundaryCost t

/-- A positive-boundary cost bracket is a closed cost bracket. -/
def CostThresholdBracket.toClosed
    (D : CostAwareThresholdData Applicant State) {target : ℝ}
    (B : D.CostThresholdBracket target) :
    D.ClosedCostThresholdBracket target where
  t := B.t
  strict_le_target := B.strict_le_target
  target_le_closed := B.target_le_closed

/--
A cost bracketing certificate constructs a same-cost threshold replacement.
-/
noncomputable def CostThresholdBracket.toSameCostThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (B : D.CostThresholdBracket (D.expectedCost original)) :
    D.SameCostThresholdReplacement original := by
  let alpha : ℝ :=
    (D.expectedCost original - D.strictAboveCost B.t) / D.boundaryCost B.t
  have halpha_nonneg : 0 ≤ alpha := by
    dsimp [alpha]
    exact div_nonneg (sub_nonneg.mpr B.strict_le_target)
      B.boundary_pos.le
  have halpha_le_one : alpha ≤ 1 := by
    dsimp [alpha]
    have hnum :
        D.expectedCost original - D.strictAboveCost B.t ≤
          D.boundaryCost B.t := by
      linarith [B.target_le_closed]
    exact (div_le_one B.boundary_pos).mpr hnum
  have halpha_mul :
      alpha * D.boundaryCost B.t =
        D.expectedCost original - D.strictAboveCost B.t := by
    dsimp [alpha]
    field_simp [ne_of_gt B.boundary_pos]
  have halpha :
      D.expectedCost (D.singleThresholdPolicy B.t alpha) =
        D.expectedCost original := by
    rw [D.expectedCost_singleThresholdPolicy_eq]
    linarith
  exact
    { t := B.t
      alpha := alpha
      threshold := D.singleThresholdPolicy B.t alpha
      threshold_policy :=
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          B.t alpha halpha_nonneg halpha_le_one
      same_cost := halpha }

/--
A closed cost bracketing certificate constructs a same-cost threshold
replacement, including the atomless case where the boundary mass is zero.
-/
noncomputable def ClosedCostThresholdBracket.toSameCostThresholdReplacement
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (B : D.ClosedCostThresholdBracket (D.expectedCost original)) :
    D.SameCostThresholdReplacement original := by
  let H :=
    D.exists_alpha_singleThresholdPolicy_expectedCost_eq_of_closed_bracket
      B.t (D.expectedCost original)
      B.strict_le_target B.target_le_closed
  let alpha : ℝ := Classical.choose H
  have hspec := Classical.choose_spec H
  exact
    { t := B.t
      alpha := alpha
      threshold := D.singleThresholdPolicy B.t alpha
      threshold_policy :=
        D.singleThresholdPolicy_isSingleCostAwareThresholdPolicy
          B.t alpha hspec.1 hspec.2.1
      same_cost := hspec.2.2 }

/--
Finite-support cost-attainment part of Appendix Lemma 2.

When allocation costs are positive and the total finite atom cost mass is
positive, every bounded allocation's expected cost lies in a boundary jump of
the cost-aware threshold sweep.
-/
theorem exists_costThresholdBracket_of_finite_positive_costs
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : AllocationPolicyBounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.costAtomMass) :
    Nonempty (D.CostThresholdBracket (D.expectedCost original)) := by
  have hcost_nonneg : ∀ item, 0 ≤ D.allocCost item :=
    fun item => (hcost_pos item).le
  have hmass_nonneg :
      ∀ atom : ThresholdAtom Applicant State, 0 ≤ D.costAtomMass atom :=
    D.costAtomMass_nonneg hweight hcost_nonneg
  have htarget_nonneg : 0 ≤ D.expectedCost original :=
    D.expectedCost_nonneg_of_bounds original hweight hcost_nonneg horiginal
  have htarget_le_total :
      D.expectedCost original ≤ finiteAtomTotalMass D.costAtomMass :=
    D.expectedCost_le_finiteAtomTotalMass_of_bounds
      original hweight hcost_nonneg horiginal
  rcases exists_finiteAtom_threshold_bracket
      D.atomScore D.costAtomMass (D.expectedCost original)
      hmass_nonneg htotal_pos htarget_nonneg htarget_le_total with
    ⟨t, hboundary, hstrict, hclosed⟩
  refine ⟨
    { t := t
      boundary_pos := ?_
      strict_le_target := ?_
      target_le_closed := ?_ }⟩
  · rw [D.boundaryCost_eq_finiteAtomBoundaryMass t hcost_pos]
    exact hboundary
  · rw [D.strictAboveCost_eq_finiteAtomStrictAboveMass t hcost_pos]
    exact hstrict
  · rw [D.strictAboveCost_eq_finiteAtomStrictAboveMass t hcost_pos]
    rw [D.boundaryCost_eq_finiteAtomBoundaryMass t hcost_pos]
    exact hclosed

/--
Positive boundary utility mass can only occur at a positive cost-aware
threshold when utilities are nonnegative and costs are positive.
-/
theorem threshold_pos_of_boundaryPosteriorUtility_pos
    (D : CostAwareThresholdData Applicant State) (t : ℝ)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hboundary : 0 < D.boundaryPosteriorUtility t) :
    0 < t := by
  classical
  have hboundary_atom :
      0 < finiteAtomBoundaryMass D.atomScore D.utilityAtomMass t := by
    simpa [D.boundaryPosteriorUtility_eq_finiteAtomBoundaryMass t hcost_pos]
      using hboundary
  have hzero_sum :
      (∑ atom : ThresholdAtom Applicant State, (0 : ℝ)) <
        ∑ atom : ThresholdAtom Applicant State,
          if D.atomScore atom = t then D.utilityAtomMass atom else 0 := by
    simpa [finiteAtomBoundaryMass] using hboundary_atom
  rcases Finset.exists_lt_of_sum_lt hzero_sum with ⟨atom, _, hterm_pos⟩
  by_cases hscore : D.atomScore atom = t
  · have hmass_pos : 0 < D.utilityAtomMass atom := by
      simpa [hscore] using hterm_pos
    have hutility_pos : 0 < D.posteriorUtility atom.2 atom.1 := by
      by_contra hnot
      have hutility_le : D.posteriorUtility atom.2 atom.1 ≤ 0 :=
        le_of_not_gt hnot
      have hprod_nonpos :
          D.weight atom.1 * D.posteriorUtility atom.2 atom.1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hweight atom.1) hutility_le
      exact not_lt_of_ge hprod_nonpos hmass_pos
    have hscore_pos : 0 < D.atomScore atom := by
      exact div_pos hutility_pos (hcost_pos atom.2)
    simpa [hscore] using hscore_pos
  · simp [hscore] at hterm_pos

/--
Finite-support utility-attainment part of Appendix Lemma 2.

Under nonnegative utilities, positive costs, and positive total finite atom
utility mass, every bounded allocation's expected utility lies in a positive
boundary jump of the cost-aware threshold sweep.
-/
theorem exists_utilityThresholdBracket_of_finite_positive_costs
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : AllocationPolicyBounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.utilityAtomMass) :
    Nonempty (D.UtilityThresholdBracket
      (D.expectedPosteriorUtility original)) := by
  have hmass_nonneg :
      ∀ atom : ThresholdAtom Applicant State, 0 ≤ D.utilityAtomMass atom :=
    D.utilityAtomMass_nonneg hweight hutility_nonneg
  have htarget_nonneg :
      0 ≤ D.expectedPosteriorUtility original :=
    D.expectedPosteriorUtility_nonneg_of_bounds
      original hweight hutility_nonneg horiginal
  have htarget_le_total :
      D.expectedPosteriorUtility original ≤
        finiteAtomTotalMass D.utilityAtomMass :=
    D.expectedPosteriorUtility_le_finiteAtomTotalMass_of_bounds
      original hweight hutility_nonneg horiginal
  rcases exists_finiteAtom_threshold_bracket
      D.atomScore D.utilityAtomMass (D.expectedPosteriorUtility original)
      hmass_nonneg htotal_pos htarget_nonneg htarget_le_total with
    ⟨t, hboundary, hstrict, hclosed⟩
  have hboundaryD : 0 < D.boundaryPosteriorUtility t := by
    rw [D.boundaryPosteriorUtility_eq_finiteAtomBoundaryMass t hcost_pos]
    exact hboundary
  refine ⟨
    { t := t
      threshold_pos := ?_
      boundary_pos := hboundaryD
      strict_le_target := ?_
      target_le_closed := ?_ }⟩
  · exact
      D.threshold_pos_of_boundaryPosteriorUtility_pos
        t hweight hutility_nonneg hcost_pos hboundaryD
  · rw [D.strictAbovePosteriorUtility_eq_finiteAtomStrictAboveMass t hcost_pos]
    exact hstrict
  · rw [D.strictAbovePosteriorUtility_eq_finiteAtomStrictAboveMass t hcost_pos]
    rw [D.boundaryPosteriorUtility_eq_finiteAtomBoundaryMass t hcost_pos]
    exact hclosed

/--
Finite-support Lemma 2, cost version: construct a same-cost threshold
replacement for any bounded allocation.
-/
theorem exists_sameCostThresholdReplacement_of_finite_positive_costs
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : AllocationPolicyBounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.costAtomMass) :
    Nonempty (D.SameCostThresholdReplacement original) := by
  rcases D.exists_costThresholdBracket_of_finite_positive_costs
      original hweight hcost_pos horiginal htotal_pos with
    ⟨B⟩
  exact ⟨B.toSameCostThresholdReplacement D original⟩

/--
Finite-support Lemma 2, utility version: construct a same-utility threshold
replacement for any bounded allocation.
-/
theorem exists_sameUtilityThresholdReplacement_of_finite_positive_costs
    (D : CostAwareThresholdData Applicant State)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : AllocationPolicyBounds original)
    (htotal_pos : 0 < finiteAtomTotalMass D.utilityAtomMass) :
    Nonempty (D.SameUtilityThresholdReplacement original) := by
  rcases D.exists_utilityThresholdBracket_of_finite_positive_costs
      original hweight hutility_nonneg hcost_pos horiginal htotal_pos with
    ⟨B⟩
  exact ⟨B.toSameUtilityThresholdReplacement D original⟩

end CostAwareThresholdData

/-! ## Abstract-expectation cost-aware threshold exchange -/

/--
Cost-aware threshold data over an arbitrary outcome space.

The expectation operator is kept abstract but required to be monotone and
finite-linear.  This captures the appendix exchange argument without assuming
that the underlying distribution has finite support.
-/
structure ExpectedCostAwareData (Applicant Outcome : Type*) where
  expect : (Outcome → ℝ) → ℝ
  expect_finiteLinear : FiniteLinearExpectation expect
  posteriorUtility : Applicant → Outcome → ℝ
  allocCost : Applicant → ℝ

namespace ExpectedCostAwareData

variable {Applicant Outcome : Type*} [Fintype Applicant]

/-- An allocation policy is an outcome-dependent allocation probability. -/
abbrev AllocationPolicy (Applicant Outcome : Type*) :=
  Applicant → Outcome → ℝ

/-- Source allocation policies have probabilities in `[0,1]`. -/
def AllocationPolicyBounds
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  ∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1

/--
Single-threshold cost-aware policy over an arbitrary outcome space.

This is the source comparison `\hat U_i / c_i` against a common threshold,
written without division.
-/
def IsSingleCostAwareThresholdPolicy
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  0 ≤ alpha ∧ alpha ≤ 1 ∧
    ∀ item outcome,
      (D.allocCost item * t < D.posteriorUtility item outcome →
        policy item outcome = 1) ∧
      (D.posteriorUtility item outcome = D.allocCost item * t →
        policy item outcome = alpha) ∧
      (D.posteriorUtility item outcome < D.allocCost item * t →
        policy item outcome = 0)

/-- The canonical arbitrary-outcome single-threshold policy. -/
noncomputable def singleThresholdPolicy
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome =>
    if D.allocCost item * t < D.posteriorUtility item outcome then
      1
    else if D.posteriorUtility item outcome < D.allocCost item * t then
      0
    else
      alpha

/-- The canonical arbitrary-outcome threshold policy satisfies the definition. -/
theorem singleThresholdPolicy_isSingleCostAwareThresholdPolicy
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    D.IsSingleCostAwareThresholdPolicy t alpha
      (D.singleThresholdPolicy t alpha) := by
  classical
  refine ⟨halpha_nonneg, halpha_le_one, ?_⟩
  intro item outcome
  constructor
  · intro habove
    simp [singleThresholdPolicy, habove]
  constructor
  · intro heq
    have hnot_above :
        ¬ D.allocCost item * t < D.posteriorUtility item outcome := by
      rw [heq]
      exact not_lt.mpr le_rfl
    have hnot_below :
        ¬ D.posteriorUtility item outcome < D.allocCost item * t := by
      rw [heq]
      exact not_lt.mpr le_rfl
    simp [singleThresholdPolicy, hnot_above, hnot_below]
  · intro hbelow
    have hnot_above :
        ¬ D.allocCost item * t < D.posteriorUtility item outcome :=
      not_lt.mpr hbelow.le
    simp [singleThresholdPolicy, hnot_above, hbelow]

/-- Expected posterior utility of an arbitrary-outcome allocation policy. -/
noncomputable def expectedPosteriorUtility
    (D : ExpectedCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  D.expect fun outcome =>
    ∑ item : Applicant, policy item outcome * D.posteriorUtility item outcome

/-- Expected allocation cost of an arbitrary-outcome allocation policy. -/
noncomputable def expectedCost
    (D : ExpectedCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  D.expect fun outcome =>
    ∑ item : Applicant, D.allocCost item * policy item outcome

/-- A single cost-aware threshold policy is an allocation policy. -/
theorem singleCostAwareThresholdPolicy_bounds
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold : AllocationPolicy Applicant Outcome)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold) :
    AllocationPolicyBounds threshold := by
  classical
  rcases hthreshold with ⟨halpha_nonneg, halpha_le_one, hcases⟩
  intro item outcome
  rcases lt_trichotomy (D.posteriorUtility item outcome)
      (D.allocCost item * t) with hbelow | heq | habove
  · have hzero : threshold item outcome = 0 :=
      (hcases item outcome).2.2 hbelow
    simp [hzero]
  · have halpha : threshold item outcome = alpha :=
      (hcases item outcome).2.1 heq
    exact ⟨by simpa [halpha] using halpha_nonneg,
      by simpa [halpha] using halpha_le_one⟩
  · have hone : threshold item outcome = 1 :=
      (hcases item outcome).1 habove
    simp [hone]

/-- Positive deltas from a threshold policy occur only weakly above threshold. -/
theorem threshold_bound_le_posteriorUtility_of_delta_pos
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    ∀ item outcome,
      0 < threshold item outcome - other item outcome →
        D.allocCost item * t ≤ D.posteriorUtility item outcome := by
  classical
  rcases hthreshold with ⟨_, _, hcases⟩
  intro item outcome hdelta
  by_contra hnot
  have hbelow : D.posteriorUtility item outcome < D.allocCost item * t :=
    lt_of_not_ge hnot
  have hzero : threshold item outcome = 0 :=
    (hcases item outcome).2.2 hbelow
  have hother_nonneg : 0 ≤ other item outcome :=
    (hother item outcome).1
  rw [hzero] at hdelta
  linarith

/-- Negative deltas from a threshold policy occur only weakly below threshold. -/
theorem posteriorUtility_le_threshold_bound_of_delta_neg
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    ∀ item outcome,
      threshold item outcome - other item outcome < 0 →
        D.posteriorUtility item outcome ≤ D.allocCost item * t := by
  classical
  rcases hthreshold with ⟨_, _, hcases⟩
  intro item outcome hdelta
  by_contra hnot
  have habove : D.allocCost item * t < D.posteriorUtility item outcome :=
    lt_of_not_ge hnot
  have hone : threshold item outcome = 1 :=
    (hcases item outcome).1 habove
  have hother_le_one : other item outcome ≤ 1 :=
    (hother item outcome).2
  rw [hone] at hdelta
  linarith

/-- Difference in expected posterior utility is the abstract value delta. -/
theorem expectedPosteriorUtility_sub_eq_expectedDeltaValue
    (D : ExpectedCostAwareData Applicant Outcome)
    (threshold other : AllocationPolicy Applicant Outcome) :
    D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other =
      expectedDeltaValue D.expect D.posteriorUtility threshold other := by
  classical
  simp only [expectedPosteriorUtility, expectedDeltaValue]
  rw [← FiniteLinearExpectation.sub D.expect_finiteLinear]
  congr 1
  funext outcome
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/-- Difference in expected cost is the abstract cost delta. -/
theorem expectedCost_sub_eq_expectedDeltaCost
    (D : ExpectedCostAwareData Applicant Outcome)
    (threshold other : AllocationPolicy Applicant Outcome) :
    D.expectedCost threshold - D.expectedCost other =
      expectedDeltaCost D.expect D.allocCost threshold other := by
  classical
  simp only [expectedCost, expectedDeltaCost]
  rw [← FiniteLinearExpectation.sub D.expect_finiteLinear]
  congr 1
  funext outcome
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro item _
  ring

/--
Appendix Lemma 1 key inequality under an arbitrary finite-linear expectation.
-/
theorem singleCostAwareThreshold_expected_delta_key
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other) :
    t * (D.expectedCost threshold - D.expectedCost other) ≤
      D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other := by
  have hmain :=
    mul_expectedDeltaCost_le_expectedDeltaValue
      D.expect D.expect_finiteLinear D.posteriorUtility D.allocCost
      threshold other t
      (D.threshold_bound_le_posteriorUtility_of_delta_pos
        t alpha threshold other hthreshold hother)
      (D.posteriorUtility_le_threshold_bound_of_delta_neg
        t alpha threshold other hthreshold hother)
  rwa [D.expectedCost_sub_eq_expectedDeltaCost threshold other,
    D.expectedPosteriorUtility_sub_eq_expectedDeltaValue threshold other]

/--
Appendix Lemma 1, Case 1, under an arbitrary finite-linear expectation.
-/
theorem singleCostAwareThreshold_expectedPosteriorUtility_ge_of_expectedCost_eq
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other)
    (hcost : D.expectedCost threshold = D.expectedCost other) :
    D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility threshold := by
  have hkey :=
    D.singleCostAwareThreshold_expected_delta_key
      t alpha threshold other hthreshold hother
  have hcost_zero :
      D.expectedCost threshold - D.expectedCost other = 0 := by
    linarith
  rw [hcost_zero, mul_zero] at hkey
  linarith

/--
Appendix Lemma 1, Case 2, under an arbitrary finite-linear expectation.
-/
theorem singleCostAwareThreshold_expectedCost_le_of_expectedPosteriorUtility_eq
    (D : ExpectedCostAwareData Applicant Outcome) (t alpha : ℝ)
    (threshold other : AllocationPolicy Applicant Outcome)
    (ht : 0 < t)
    (hthreshold : D.IsSingleCostAwareThresholdPolicy t alpha threshold)
    (hother : AllocationPolicyBounds other)
    (hutility :
      D.expectedPosteriorUtility threshold =
        D.expectedPosteriorUtility other) :
    D.expectedCost threshold ≤ D.expectedCost other := by
  have hkey :=
    D.singleCostAwareThreshold_expected_delta_key
      t alpha threshold other hthreshold hother
  have hutility_zero :
      D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other = 0 := by
    linarith
  rw [hutility_zero] at hkey
  have hcost_nonpos :
      D.expectedCost threshold - D.expectedCost other ≤ 0 := by
    have hmul :
        (D.expectedCost threshold - D.expectedCost other) * t ≤ 0 := by
      simpa [mul_comm] using hkey
    exact nonpos_of_mul_nonpos_left hmul ht
  linarith

end ExpectedCostAwareData

/-! ## Measure-based cost-aware threshold attainment -/

/--
Single-group cost-aware allocation data on a measurable outcome space.

This is the source-general version of Lemma 2: applicants have posterior
utility random variables on a common probability space, and allocation costs
are deterministic constants.
-/
structure MeasureCostAwareData (Applicant Outcome : Type*)
    [MeasurableSpace Outcome] where
  law : Measure Outcome
  posteriorUtility : Applicant → Outcome → ℝ
  posteriorUtility_measurable :
    ∀ item, Measurable (posteriorUtility item)
  posteriorUtility_integrable :
    ∀ item, Integrable (posteriorUtility item) law
  allocCost : Applicant → ℝ

namespace MeasureCostAwareData

variable {Applicant Outcome : Type*} [Fintype Applicant]
variable [MeasurableSpace Outcome]

/-- An allocation policy on the measurable outcome space. -/
abbrev AllocationPolicy (Applicant Outcome : Type*) :=
  Applicant → Outcome → ℝ

/-- Allocation probabilities lie in `[0,1]`. -/
def AllocationPolicyBounds
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  ∀ item outcome, 0 ≤ policy item outcome ∧ policy item outcome ≤ 1

/-- Allocation policies over arbitrary outcome spaces are measurable. -/
def AllocationPolicyMeasurable
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  ∀ item, Measurable (policy item)

/-- Cost-aware score `\hat U_i / c_i`. -/
noncomputable def score
    (D : MeasureCostAwareData Applicant Outcome) (item : Applicant)
    (outcome : Outcome) : ℝ :=
  D.posteriorUtility item outcome / D.allocCost item

/-- The score random variable is measurable. -/
theorem score_measurable
    (D : MeasureCostAwareData Applicant Outcome) (item : Applicant) :
    Measurable (D.score item) := by
  unfold score
  exact (D.posteriorUtility_measurable item).div_const (D.allocCost item)

/-- Canonical score-threshold policy with boundary randomization. -/
noncomputable def scoreThresholdPolicy
    (D : MeasureCostAwareData Applicant Outcome) (t alpha : ℝ) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome =>
    if t < D.score item outcome then
      1
    else if D.score item outcome < t then
      0
    else
      alpha

/-- Cost-aware score measure for a single group. -/
noncomputable def costScoreMeasure
    (D : MeasureCostAwareData Applicant Outcome) : Measure ℝ :=
  finiteWeightedScoreMeasureSum D.allocCost
    (fun _ : Applicant => D.law) D.score

/-- Utility-weighted score measure for a single group. -/
noncomputable def utilityScoreMeasure
    (D : MeasureCostAwareData Applicant Outcome) : Measure ℝ :=
  finiteValueWeightedScoreMeasureSum
    (fun _ : Applicant => D.law) D.score D.posteriorUtility

/-- Expected posterior utility of an allocation policy. -/
noncomputable def expectedPosteriorUtility
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  ∫ outcome,
    ∑ item : Applicant,
      policy item outcome * D.posteriorUtility item outcome ∂D.law

/-- Expected allocation cost of an allocation policy. -/
noncomputable def expectedCost
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  ∫ outcome,
    ∑ item : Applicant,
      D.allocCost item * policy item outcome ∂D.law

/--
The positive-part reduction of a measure allocation policy.

It keeps the original allocation probability only at outcomes where the
posterior utility is strictly positive, and assigns zero otherwise.
-/
noncomputable def positivePartPolicy
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome =>
    if 0 < D.posteriorUtility item outcome then
      policy item outcome
    else
      0

/--
Copy of the measure data in which posterior utilities are truncated below at
zero.  This is used to run the nonnegative-utility threshold sweep without
adding a sign assumption to the original paper statement.
-/
noncomputable def positivePosteriorUtilityData
    (D : MeasureCostAwareData Applicant Outcome) :
    MeasureCostAwareData Applicant Outcome where
  law := D.law
  posteriorUtility item outcome := max (D.posteriorUtility item outcome) 0
  posteriorUtility_measurable item :=
    (D.posteriorUtility_measurable item).max measurable_const
  posteriorUtility_integrable item := by
    refine (D.posteriorUtility_integrable item).mono ?_ ?_
    · exact
        ((D.posteriorUtility_measurable item).max
          measurable_const).aestronglyMeasurable
    · exact ae_of_all D.law fun outcome => by
        by_cases hnonneg : 0 ≤ D.posteriorUtility item outcome
        · rw [max_eq_left hnonneg]
        · have hle : D.posteriorUtility item outcome ≤ 0 :=
            le_of_not_ge hnonneg
          rw [max_eq_right hle]
          simpa using norm_nonneg (D.posteriorUtility item outcome)
  allocCost := D.allocCost

/-- The positive-posterior copy has nonnegative utilities almost everywhere. -/
theorem positivePosteriorUtilityData_nonneg
    (D : MeasureCostAwareData Applicant Outcome) :
    ∀ item,
      0 ≤ᵐ[D.law]
        (D.positivePosteriorUtilityData).posteriorUtility item := by
  intro item
  exact ae_of_all D.law fun outcome =>
    le_max_right (D.posteriorUtility item outcome) 0

/-- The aggregate utility score measure is finite under integrability. -/
theorem utilityScoreMeasure_finite
    (D : MeasureCostAwareData Applicant Outcome) :
    IsFiniteMeasure D.utilityScoreMeasure := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  unfold utilityScoreMeasure finiteValueWeightedScoreMeasureSum
    finiteWeightedMeasureSum
  constructor
  simp [measure_lt_top]

/-- The aggregate cost score measure is finite when the outcome law is finite. -/
theorem costScoreMeasure_finite
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law] :
    IsFiniteMeasure D.costScoreMeasure := by
  classical
  unfold costScoreMeasure finiteWeightedScoreMeasureSum finiteWeightedMeasureSum
  constructor
  rw [show
      ((∑ item : Applicant,
        ENNReal.ofReal (D.allocCost item) • D.law.map (D.score item)) :
          Measure ℝ) Set.univ =
        ∑ item : Applicant,
          (ENNReal.ofReal (D.allocCost item) •
            D.law.map (D.score item)) Set.univ by
    simpa using
      Measure.finset_sum_apply
        (Finset.univ : Finset Applicant)
        (fun item =>
          ENNReal.ofReal (D.allocCost item) • D.law.map (D.score item))
        (Set.univ : Set ℝ)]
  simp [ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)]

/--
Measure-level Lemma 2, utility half, specialized to the source score measure.
-/
theorem exists_utilityScoreMeasure_threshold_attainment
    (D : MeasureCostAwareData Applicant Outcome) {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total :
      target ≤ D.utilityScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ θ : RealThreshold,
      ∃ alpha : ℝ,
        0 ≤ alpha ∧ alpha ≤ 1 ∧
          θ.strictUpperTailMass D.utilityScoreMeasure +
              alpha *
                (θ.closedUpperTailMass D.utilityScoreMeasure -
                  θ.strictUpperTailMass D.utilityScoreMeasure) =
            target := by
  haveI : IsFiniteMeasure D.utilityScoreMeasure :=
    D.utilityScoreMeasure_finite
  exact exists_realThreshold_upperTailMass_interpolation_finite
    D.utilityScoreMeasure htarget_nonneg htarget_le_total

/--
Measure-level Lemma 2, cost half, specialized to the source score measure.
-/
theorem exists_costScoreMeasure_threshold_attainment
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total :
      target ≤ D.costScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ θ : RealThreshold,
      ∃ alpha : ℝ,
        0 ≤ alpha ∧ alpha ≤ 1 ∧
          θ.strictUpperTailMass D.costScoreMeasure +
              alpha *
                (θ.closedUpperTailMass D.costScoreMeasure -
                  θ.strictUpperTailMass D.costScoreMeasure) =
            target := by
  haveI : IsFiniteMeasure D.costScoreMeasure :=
    D.costScoreMeasure_finite
  exact exists_realThreshold_upperTailMass_interpolation_finite
    D.costScoreMeasure htarget_nonneg htarget_le_total

/--
Strict utility tail of the aggregate score measure equals the sum of
thresholded posterior-utility integrals.
-/
theorem upperTailMass_utilityScoreMeasure_eq_sum_integral_indicator
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (t : ℝ) :
    upperTailMass D.utilityScoreMeasure t =
      ∑ item : Applicant,
        ∫ outcome,
          ({outcome | t < D.score item outcome}.indicator
            (D.posteriorUtility item)) outcome ∂D.law := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  rw [utilityScoreMeasure,
    upperTailMass_finiteValueWeightedScoreMeasureSum]
  refine Finset.sum_congr rfl ?_
  intro item _
  exact
    (integral_indicator_value_strictUpperTail_eq_valueWeightedScoreMeasure_real
      D.law (D.score_measurable item)
      (D.posteriorUtility_integrable item)
      (hutility_nonneg item) t).symm

/--
Closed utility tail of the aggregate score measure equals the sum of
closed-threshold posterior-utility integrals.
-/
theorem closedUpperTailMass_utilityScoreMeasure_eq_sum_integral_indicator
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (t : ℝ) :
    D.utilityScoreMeasure.real (Set.Ici t) =
      ∑ item : Applicant,
        ∫ outcome,
          ({outcome | t ≤ D.score item outcome}.indicator
            (D.posteriorUtility item)) outcome ∂D.law := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  rw [utilityScoreMeasure,
    closedUpperTailMass_finiteValueWeightedScoreMeasureSum]
  refine Finset.sum_congr rfl ?_
  intro item _
  exact
    (integral_indicator_value_closedUpperTail_eq_valueWeightedScoreMeasure_real
      D.law (D.score_measurable item)
      (D.posteriorUtility_integrable item)
      (hutility_nonneg item) t).symm

/--
Strict cost tail of the aggregate score measure equals the sum of
thresholded allocation-cost integrals.
-/
theorem upperTailMass_costScoreMeasure_eq_sum_integral_indicator
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item) (t : ℝ) :
    upperTailMass D.costScoreMeasure t =
      ∑ item : Applicant,
        ∫ outcome,
          ({outcome | t < D.score item outcome}.indicator
            (fun _ : Outcome => D.allocCost item)) outcome ∂D.law := by
  classical
  rw [costScoreMeasure, upperTailMass_finiteWeightedScoreMeasureSum
    D.allocCost (fun _ : Applicant => D.law) D.score hcost_nonneg t]
  refine Finset.sum_congr rfl ?_
  intro item _
  simpa [upperTailMass] using
    (integral_indicator_const_strictUpperTail_eq_mul_map_real
      D.law (D.score_measurable item) (hcost_nonneg item) t).symm

/--
Closed cost tail of the aggregate score measure equals the sum of
closed-threshold allocation-cost integrals.
-/
theorem closedUpperTailMass_costScoreMeasure_eq_sum_integral_indicator
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item) (t : ℝ) :
    D.costScoreMeasure.real (Set.Ici t) =
      ∑ item : Applicant,
        ∫ outcome,
          ({outcome | t ≤ D.score item outcome}.indicator
            (fun _ : Outcome => D.allocCost item)) outcome ∂D.law := by
  classical
  rw [costScoreMeasure, closedUpperTailMass_finiteWeightedScoreMeasureSum
    D.allocCost (fun _ : Applicant => D.law) D.score hcost_nonneg t]
  refine Finset.sum_congr rfl ?_
  intro item _
  simpa using
    (integral_indicator_const_closedUpperTail_eq_mul_map_real
      D.law (D.score_measurable item) (hcost_nonneg item) t).symm

/--
Pointwise decomposition of the threshold policy's utility contribution into
strict-tail and boundary-tail indicators.
-/
theorem scoreThresholdPolicy_mul_posteriorUtility_eq_indicator_formula
    (D : MeasureCostAwareData Applicant Outcome) (t alpha : ℝ)
    (item : Applicant) (outcome : Outcome) :
    D.scoreThresholdPolicy t alpha item outcome *
        D.posteriorUtility item outcome =
      ({outcome | t < D.score item outcome}.indicator
          (D.posteriorUtility item)) outcome +
        alpha *
          (({outcome | t ≤ D.score item outcome}.indicator
              (D.posteriorUtility item)) outcome -
            ({outcome | t < D.score item outcome}.indicator
              (D.posteriorUtility item)) outcome) := by
  by_cases habove : t < D.score item outcome
  · have hclosed : t ≤ D.score item outcome := le_of_lt habove
    simp [scoreThresholdPolicy, habove, hclosed]
  · by_cases hbelow : D.score item outcome < t
    · have hnotclosed : ¬ t ≤ D.score item outcome := not_le.mpr hbelow
      simp [scoreThresholdPolicy, habove, hbelow, hnotclosed]
    · have hclosed : t ≤ D.score item outcome := le_of_not_gt hbelow
      simp [scoreThresholdPolicy, habove, hbelow, hclosed]

/--
Per-applicant utility of a finite threshold policy equals strict utility tail
plus boundary randomization times the boundary utility mass.
-/
theorem integral_scoreThresholdPolicy_mul_posteriorUtility_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (t alpha : ℝ)
    (item : Applicant) :
    (∫ outcome,
      D.scoreThresholdPolicy t alpha item outcome *
        D.posteriorUtility item outcome ∂D.law) =
      (valueWeightedScoreMeasure D.law (D.score item)
          (D.posteriorUtility item)).real (Set.Ioi t) +
        alpha *
          ((valueWeightedScoreMeasure D.law (D.score item)
              (D.posteriorUtility item)).real (Set.Ici t) -
            (valueWeightedScoreMeasure D.law (D.score item)
              (D.posteriorUtility item)).real (Set.Ioi t)) := by
  let strictSet : Set Outcome := {outcome | t < D.score item outcome}
  let closedSet : Set Outcome := {outcome | t ≤ D.score item outcome}
  have hstrict_meas : MeasurableSet strictSet :=
    D.score_measurable item measurableSet_Ioi
  have hclosed_meas : MeasurableSet closedSet :=
    D.score_measurable item measurableSet_Ici
  have hstrict_int :
      Integrable (strictSet.indicator (D.posteriorUtility item)) D.law :=
    (D.posteriorUtility_integrable item).indicator hstrict_meas
  have hclosed_int :
      Integrable (closedSet.indicator (D.posteriorUtility item)) D.law :=
    (D.posteriorUtility_integrable item).indicator hclosed_meas
  have hdiff_int :
      Integrable
        (fun outcome =>
          closedSet.indicator (D.posteriorUtility item) outcome -
            strictSet.indicator (D.posteriorUtility item) outcome) D.law :=
    hclosed_int.sub hstrict_int
  calc
    (∫ outcome,
      D.scoreThresholdPolicy t alpha item outcome *
        D.posteriorUtility item outcome ∂D.law)
        =
        ∫ outcome,
          strictSet.indicator (D.posteriorUtility item) outcome +
            alpha *
              (closedSet.indicator (D.posteriorUtility item) outcome -
                strictSet.indicator (D.posteriorUtility item) outcome) ∂D.law := by
      refine integral_congr_ae ?_
      exact ae_of_all D.law fun outcome => by
        dsimp [strictSet, closedSet]
        exact D.scoreThresholdPolicy_mul_posteriorUtility_eq_indicator_formula
          t alpha item outcome
    _ =
        (∫ outcome,
          strictSet.indicator (D.posteriorUtility item) outcome ∂D.law) +
          alpha *
            (∫ outcome,
              closedSet.indicator (D.posteriorUtility item) outcome -
                strictSet.indicator (D.posteriorUtility item) outcome ∂D.law) := by
      rw [integral_add hstrict_int (hdiff_int.const_mul alpha)]
      rw [integral_const_mul]
    _ =
        (∫ outcome,
          strictSet.indicator (D.posteriorUtility item) outcome ∂D.law) +
          alpha *
            ((∫ outcome,
              closedSet.indicator (D.posteriorUtility item) outcome ∂D.law) -
                ∫ outcome,
                  strictSet.indicator (D.posteriorUtility item) outcome ∂D.law) := by
      rw [integral_sub hclosed_int hstrict_int]
    _ =
        (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)).real (Set.Ioi t) +
          alpha *
            ((valueWeightedScoreMeasure D.law (D.score item)
                (D.posteriorUtility item)).real (Set.Ici t) -
              (valueWeightedScoreMeasure D.law (D.score item)
                (D.posteriorUtility item)).real (Set.Ioi t)) := by
      rw [integral_indicator_value_strictUpperTail_eq_valueWeightedScoreMeasure_real
        D.law (D.score_measurable item)
        (D.posteriorUtility_integrable item)
        (hutility_nonneg item) t]
      rw [integral_indicator_value_closedUpperTail_eq_valueWeightedScoreMeasure_real
        D.law (D.score_measurable item)
        (D.posteriorUtility_integrable item)
        (hutility_nonneg item) t]

/--
Pointwise decomposition of the threshold policy's cost contribution into
strict-tail and boundary-tail indicators.
-/
theorem allocCost_mul_scoreThresholdPolicy_eq_indicator_formula
    (D : MeasureCostAwareData Applicant Outcome) (t alpha : ℝ)
    (item : Applicant) (outcome : Outcome) :
    D.allocCost item * D.scoreThresholdPolicy t alpha item outcome =
      ({outcome | t < D.score item outcome}.indicator
          (fun _ : Outcome => D.allocCost item)) outcome +
        alpha *
          (({outcome | t ≤ D.score item outcome}.indicator
              (fun _ : Outcome => D.allocCost item)) outcome -
            ({outcome | t < D.score item outcome}.indicator
              (fun _ : Outcome => D.allocCost item)) outcome) := by
  by_cases habove : t < D.score item outcome
  · have hclosed : t ≤ D.score item outcome := le_of_lt habove
    simp [scoreThresholdPolicy, habove, hclosed]
  · by_cases hbelow : D.score item outcome < t
    · have hnotclosed : ¬ t ≤ D.score item outcome := not_le.mpr hbelow
      simp [scoreThresholdPolicy, habove, hbelow, hnotclosed]
    · have hclosed : t ≤ D.score item outcome := le_of_not_gt hbelow
      simp [scoreThresholdPolicy, habove, hbelow, hclosed]
      ring

/--
Per-applicant cost of a finite threshold policy equals strict cost tail plus
boundary randomization times the boundary cost mass.
-/
theorem integral_allocCost_mul_scoreThresholdPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (t alpha : ℝ) (item : Applicant) :
    (∫ outcome,
      D.allocCost item * D.scoreThresholdPolicy t alpha item outcome ∂D.law) =
      D.allocCost item * (D.law.map (D.score item)).real (Set.Ioi t) +
        alpha *
          (D.allocCost item * (D.law.map (D.score item)).real (Set.Ici t) -
            D.allocCost item * (D.law.map (D.score item)).real (Set.Ioi t)) := by
  let strictSet : Set Outcome := {outcome | t < D.score item outcome}
  let closedSet : Set Outcome := {outcome | t ≤ D.score item outcome}
  have hstrict_meas : MeasurableSet strictSet :=
    D.score_measurable item measurableSet_Ioi
  have hclosed_meas : MeasurableSet closedSet :=
    D.score_measurable item measurableSet_Ici
  have hconst_int :
      Integrable (fun _ : Outcome => D.allocCost item) D.law := by
    simpa using
      (MeasureTheory.integrable_const (μ := D.law)
        (c := D.allocCost item))
  have hstrict_int :
      Integrable
        (strictSet.indicator (fun _ : Outcome => D.allocCost item)) D.law :=
    hconst_int.indicator hstrict_meas
  have hclosed_int :
      Integrable
        (closedSet.indicator (fun _ : Outcome => D.allocCost item)) D.law :=
    hconst_int.indicator hclosed_meas
  have hdiff_int :
      Integrable
        (fun outcome =>
          closedSet.indicator (fun _ : Outcome => D.allocCost item) outcome -
            strictSet.indicator (fun _ : Outcome => D.allocCost item) outcome)
          D.law :=
    hclosed_int.sub hstrict_int
  calc
    (∫ outcome,
      D.allocCost item * D.scoreThresholdPolicy t alpha item outcome ∂D.law)
        =
        ∫ outcome,
          strictSet.indicator (fun _ : Outcome => D.allocCost item) outcome +
            alpha *
              (closedSet.indicator (fun _ : Outcome => D.allocCost item) outcome -
                strictSet.indicator (fun _ : Outcome => D.allocCost item)
                  outcome) ∂D.law := by
      refine integral_congr_ae ?_
      exact ae_of_all D.law fun outcome => by
        dsimp [strictSet, closedSet]
        exact D.allocCost_mul_scoreThresholdPolicy_eq_indicator_formula
          t alpha item outcome
    _ =
        (∫ outcome,
          strictSet.indicator (fun _ : Outcome => D.allocCost item)
            outcome ∂D.law) +
          alpha *
            (∫ outcome,
              closedSet.indicator (fun _ : Outcome => D.allocCost item)
                outcome -
                strictSet.indicator (fun _ : Outcome => D.allocCost item)
                  outcome ∂D.law) := by
      rw [integral_add hstrict_int (hdiff_int.const_mul alpha)]
      rw [integral_const_mul]
    _ =
        (∫ outcome,
          strictSet.indicator (fun _ : Outcome => D.allocCost item)
            outcome ∂D.law) +
          alpha *
            ((∫ outcome,
              closedSet.indicator (fun _ : Outcome => D.allocCost item)
                outcome ∂D.law) -
                ∫ outcome,
                  strictSet.indicator (fun _ : Outcome => D.allocCost item)
                    outcome ∂D.law) := by
      rw [integral_sub hclosed_int hstrict_int]
    _ =
        D.allocCost item * (D.law.map (D.score item)).real (Set.Ioi t) +
          alpha *
            (D.allocCost item * (D.law.map (D.score item)).real (Set.Ici t) -
              D.allocCost item * (D.law.map (D.score item)).real
                (Set.Ioi t)) := by
      rw [integral_indicator_const_strictUpperTail_eq_mul_map_real
        D.law (D.score_measurable item) (hcost_nonneg item) t]
      rw [integral_indicator_const_closedUpperTail_eq_mul_map_real
        D.law (D.score_measurable item) (hcost_nonneg item) t]

/--
The total expected posterior utility of a finite threshold policy is the
aggregate strict utility tail plus the randomized boundary utility mass.
-/
theorem expectedPosteriorUtility_scoreThresholdPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (t alpha : ℝ) :
    D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) =
      upperTailMass D.utilityScoreMeasure t +
        alpha *
          (D.utilityScoreMeasure.real (Set.Ici t) -
            upperTailMass D.utilityScoreMeasure t) := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  let strictMass : Applicant → ℝ := fun item =>
    (valueWeightedScoreMeasure D.law (D.score item)
      (D.posteriorUtility item)).real (Set.Ioi t)
  let closedMass : Applicant → ℝ := fun item =>
    (valueWeightedScoreMeasure D.law (D.score item)
      (D.posteriorUtility item)).real (Set.Ici t)
  have hterm_int :
      ∀ item : Applicant,
        Integrable
          (fun outcome =>
            D.scoreThresholdPolicy t alpha item outcome *
              D.posteriorUtility item outcome) D.law := by
    intro item
    let strictSet : Set Outcome := {outcome | t < D.score item outcome}
    let closedSet : Set Outcome := {outcome | t ≤ D.score item outcome}
    have hstrict_meas : MeasurableSet strictSet :=
      D.score_measurable item measurableSet_Ioi
    have hclosed_meas : MeasurableSet closedSet :=
      D.score_measurable item measurableSet_Ici
    have hstrict_int :
        Integrable (strictSet.indicator (D.posteriorUtility item)) D.law :=
      (D.posteriorUtility_integrable item).indicator hstrict_meas
    have hclosed_int :
        Integrable (closedSet.indicator (D.posteriorUtility item)) D.law :=
      (D.posteriorUtility_integrable item).indicator hclosed_meas
    have hdiff_int :
        Integrable
          (fun outcome =>
            closedSet.indicator (D.posteriorUtility item) outcome -
              strictSet.indicator (D.posteriorUtility item) outcome) D.law :=
      hclosed_int.sub hstrict_int
    have hright_int :
        Integrable
          (fun outcome =>
            strictSet.indicator (D.posteriorUtility item) outcome +
              alpha *
                (closedSet.indicator (D.posteriorUtility item) outcome -
                  strictSet.indicator (D.posteriorUtility item) outcome))
          D.law :=
      hstrict_int.add (hdiff_int.const_mul alpha)
    refine Integrable.congr hright_int ?_
    exact ae_of_all D.law fun outcome => by
      dsimp [strictSet, closedSet]
      symm
      exact D.scoreThresholdPolicy_mul_posteriorUtility_eq_indicator_formula
        t alpha item outcome
  have hstrict :
      (∑ item : Applicant, strictMass item) =
        upperTailMass D.utilityScoreMeasure t := by
    simpa [strictMass, utilityScoreMeasure, upperTailMass] using
      (upperTailMass_finiteValueWeightedScoreMeasureSum
        (fun _ : Applicant => D.law) D.score D.posteriorUtility t).symm
  have hclosed :
      (∑ item : Applicant, closedMass item) =
        D.utilityScoreMeasure.real (Set.Ici t) := by
    simpa [closedMass, utilityScoreMeasure] using
      (closedUpperTailMass_finiteValueWeightedScoreMeasureSum
        (fun _ : Applicant => D.law) D.score D.posteriorUtility t).symm
  calc
    D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha)
        =
        ∑ item : Applicant,
          ∫ outcome,
            D.scoreThresholdPolicy t alpha item outcome *
              D.posteriorUtility item outcome ∂D.law := by
      unfold expectedPosteriorUtility
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun item _ => hterm_int item)
    _ =
        ∑ item : Applicant,
          (strictMass item +
            alpha * (closedMass item - strictMass item)) := by
      refine Finset.sum_congr rfl ?_
      intro item _
      simpa [strictMass, closedMass] using
        D.integral_scoreThresholdPolicy_mul_posteriorUtility_eq
          hutility_nonneg t alpha item
    _ =
        (∑ item : Applicant, strictMass item) +
          alpha *
            ((∑ item : Applicant, closedMass item) -
              ∑ item : Applicant, strictMass item) := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
    _ =
        upperTailMass D.utilityScoreMeasure t +
          alpha *
            (D.utilityScoreMeasure.real (Set.Ici t) -
              upperTailMass D.utilityScoreMeasure t) := by
      rw [hstrict, hclosed]

/--
The total expected cost of a finite threshold policy is the aggregate strict
cost tail plus the randomized boundary cost mass.
-/
theorem expectedCost_scoreThresholdPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (t alpha : ℝ) :
    D.expectedCost (D.scoreThresholdPolicy t alpha) =
      upperTailMass D.costScoreMeasure t +
        alpha *
          (D.costScoreMeasure.real (Set.Ici t) -
            upperTailMass D.costScoreMeasure t) := by
  classical
  let strictMass : Applicant → ℝ := fun item =>
    D.allocCost item * (D.law.map (D.score item)).real (Set.Ioi t)
  let closedMass : Applicant → ℝ := fun item =>
    D.allocCost item * (D.law.map (D.score item)).real (Set.Ici t)
  have hterm_int :
      ∀ item : Applicant,
        Integrable
          (fun outcome =>
            D.allocCost item * D.scoreThresholdPolicy t alpha item outcome)
          D.law := by
    intro item
    let strictSet : Set Outcome := {outcome | t < D.score item outcome}
    let closedSet : Set Outcome := {outcome | t ≤ D.score item outcome}
    have hstrict_meas : MeasurableSet strictSet :=
      D.score_measurable item measurableSet_Ioi
    have hclosed_meas : MeasurableSet closedSet :=
      D.score_measurable item measurableSet_Ici
    have hconst_int :
        Integrable (fun _ : Outcome => D.allocCost item) D.law := by
      simpa using
        (MeasureTheory.integrable_const (μ := D.law)
          (c := D.allocCost item))
    have hstrict_int :
        Integrable
          (strictSet.indicator (fun _ : Outcome => D.allocCost item)) D.law :=
      hconst_int.indicator hstrict_meas
    have hclosed_int :
        Integrable
          (closedSet.indicator (fun _ : Outcome => D.allocCost item)) D.law :=
      hconst_int.indicator hclosed_meas
    have hdiff_int :
        Integrable
          (fun outcome =>
            closedSet.indicator (fun _ : Outcome => D.allocCost item) outcome -
              strictSet.indicator (fun _ : Outcome => D.allocCost item)
                outcome) D.law :=
      hclosed_int.sub hstrict_int
    have hright_int :
        Integrable
          (fun outcome =>
            strictSet.indicator (fun _ : Outcome => D.allocCost item) outcome +
              alpha *
                (closedSet.indicator (fun _ : Outcome => D.allocCost item)
                    outcome -
                  strictSet.indicator (fun _ : Outcome => D.allocCost item)
                    outcome)) D.law :=
      hstrict_int.add (hdiff_int.const_mul alpha)
    refine Integrable.congr hright_int ?_
    exact ae_of_all D.law fun outcome => by
      dsimp [strictSet, closedSet]
      symm
      exact D.allocCost_mul_scoreThresholdPolicy_eq_indicator_formula
        t alpha item outcome
  have hstrict :
      (∑ item : Applicant, strictMass item) =
        upperTailMass D.costScoreMeasure t := by
    simpa [strictMass, costScoreMeasure, upperTailMass] using
      (upperTailMass_finiteWeightedScoreMeasureSum
        D.allocCost (fun _ : Applicant => D.law) D.score hcost_nonneg t).symm
  have hclosed :
      (∑ item : Applicant, closedMass item) =
        D.costScoreMeasure.real (Set.Ici t) := by
    simpa [closedMass, costScoreMeasure] using
      (closedUpperTailMass_finiteWeightedScoreMeasureSum
        D.allocCost (fun _ : Applicant => D.law) D.score hcost_nonneg t).symm
  calc
    D.expectedCost (D.scoreThresholdPolicy t alpha)
        =
        ∑ item : Applicant,
          ∫ outcome,
            D.allocCost item *
              D.scoreThresholdPolicy t alpha item outcome ∂D.law := by
      unfold expectedCost
      exact MeasureTheory.integral_finset_sum Finset.univ
        (fun item _ => hterm_int item)
    _ =
        ∑ item : Applicant,
          (strictMass item +
            alpha * (closedMass item - strictMass item)) := by
      refine Finset.sum_congr rfl ?_
      intro item _
      simpa [strictMass, closedMass] using
        D.integral_allocCost_mul_scoreThresholdPolicy_eq hcost_nonneg t alpha
          item
    _ =
        (∑ item : Applicant, strictMass item) +
          alpha *
            ((∑ item : Applicant, closedMass item) -
              ∑ item : Applicant, strictMass item) := by
      rw [Finset.sum_add_distrib]
      rw [← Finset.mul_sum]
      rw [Finset.sum_sub_distrib]
    _ =
        upperTailMass D.costScoreMeasure t +
          alpha *
            (D.costScoreMeasure.real (Set.Ici t) -
              upperTailMass D.costScoreMeasure t) := by
      rw [hstrict, hclosed]

/-- A finite score-threshold policy is a bounded allocation policy. -/
theorem scoreThresholdPolicy_bounds
    (D : MeasureCostAwareData Applicant Outcome) (t alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    AllocationPolicyBounds (D.scoreThresholdPolicy t alpha) := by
  intro item outcome
  by_cases habove : t < D.score item outcome
  · simp [scoreThresholdPolicy, habove]
  · by_cases hbelow : D.score item outcome < t
    · simp [scoreThresholdPolicy, habove, hbelow]
    · simp [scoreThresholdPolicy, habove, hbelow, halpha_nonneg, halpha_le_one]

/-- A finite score-threshold policy is measurable. -/
theorem scoreThresholdPolicy_measurable
    (D : MeasureCostAwareData Applicant Outcome) (t alpha : ℝ) :
    AllocationPolicyMeasurable (D.scoreThresholdPolicy t alpha) := by
  intro item
  have habove : MeasurableSet {outcome : Outcome | t < D.score item outcome} :=
    D.score_measurable item measurableSet_Ioi
  have hbelow : MeasurableSet {outcome : Outcome | D.score item outcome < t} :=
    D.score_measurable item measurableSet_Iio
  exact Measurable.ite habove measurable_const
    (Measurable.ite hbelow measurable_const measurable_const)

/--
Pointwise exchange inequality for a finite score-threshold policy.  This is the
measure-space analogue of the algebraic core in Appendix Lemma 1.
-/
theorem scoreThresholdPolicy_delta_thresholdCost_le_delta_utility
    (D : MeasureCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ) (other : AllocationPolicy Applicant Outcome)
    (hother_bounds : AllocationPolicyBounds other)
    (item : Applicant) (outcome : Outcome) :
    (D.scoreThresholdPolicy t alpha item outcome - other item outcome) *
        (D.allocCost item * t) ≤
      (D.scoreThresholdPolicy t alpha item outcome - other item outcome) *
        D.posteriorUtility item outcome := by
  refine delta_mul_bound_le_delta_mul_value ?hpos ?hneg
  · intro hdelta_pos
    by_cases habove : t < D.score item outcome
    · have hlt :
          D.allocCost item * t < D.posteriorUtility item outcome := by
        have hlt' :
            t * D.allocCost item < D.posteriorUtility item outcome := by
          exact (lt_div_iff₀ (hcost_pos item)).mp (by
            simpa [score] using habove)
        linarith
      exact hlt.le
    · by_cases hbelow : D.score item outcome < t
      · have hthreshold_zero :
            D.scoreThresholdPolicy t alpha item outcome = 0 := by
          simp [scoreThresholdPolicy, habove, hbelow]
        have hother_nonneg : 0 ≤ other item outcome :=
          (hother_bounds item outcome).1
        rw [hthreshold_zero] at hdelta_pos
        linarith
      · have hscore_eq : D.score item outcome = t :=
          le_antisymm (le_of_not_gt habove) (le_of_not_gt hbelow)
        have heq :
            D.allocCost item * t =
              D.posteriorUtility item outcome := by
          have hscore_eq' :
              D.posteriorUtility item outcome / D.allocCost item = t := by
            simpa [score] using hscore_eq
          have hmul :=
            congrArg (fun x => x * D.allocCost item) hscore_eq'
          have hmul' :
              (D.posteriorUtility item outcome / D.allocCost item) *
                  D.allocCost item =
                t * D.allocCost item := by
            simpa using hmul
          rw [div_mul_cancel₀ _ (ne_of_gt (hcost_pos item))] at hmul'
          linarith
        exact le_of_eq heq
  · intro hdelta_neg
    by_cases habove : t < D.score item outcome
    · have hthreshold_one :
          D.scoreThresholdPolicy t alpha item outcome = 1 := by
        simp [scoreThresholdPolicy, habove]
      have hother_le_one : other item outcome ≤ 1 :=
        (hother_bounds item outcome).2
      rw [hthreshold_one] at hdelta_neg
      linarith
    · by_cases hbelow : D.score item outcome < t
      · have hlt :
            D.posteriorUtility item outcome < D.allocCost item * t := by
          have hlt' :
              D.posteriorUtility item outcome <
                t * D.allocCost item := by
            exact (div_lt_iff₀ (hcost_pos item)).mp (by
              simpa [score] using hbelow)
          linarith
        exact hlt.le
      · have hscore_eq : D.score item outcome = t :=
          le_antisymm (le_of_not_gt habove) (le_of_not_gt hbelow)
        have heq :
            D.posteriorUtility item outcome =
              D.allocCost item * t := by
          have hscore_eq' :
              D.posteriorUtility item outcome / D.allocCost item = t := by
            simpa [score] using hscore_eq
          have hmul :=
            congrArg (fun x => x * D.allocCost item) hscore_eq'
          have hmul' :
              (D.posteriorUtility item outcome / D.allocCost item) *
                  D.allocCost item =
                t * D.allocCost item := by
            simpa using hmul
          rw [div_mul_cancel₀ _ (ne_of_gt (hcost_pos item))] at hmul'
          linarith
        exact le_of_eq heq

/-- Difference in expected posterior utility as the integral of value deltas. -/
theorem expectedPosteriorUtility_sub_eq_integral_delta_value
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold_meas : AllocationPolicyMeasurable threshold)
    (hthreshold_bounds : AllocationPolicyBounds threshold)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other) :
    D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other =
      ∫ outcome,
        ∑ item : Applicant,
          (threshold item outcome - other item outcome) *
            D.posteriorUtility item outcome ∂D.law := by
  classical
  have hpolicy_value_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome =>
                  policy item outcome * D.posteriorUtility item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    exact (D.posteriorUtility_integrable item).bdd_mul
      (hpolicy_meas item).aestronglyMeasurable hbound
  have hthreshold_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            threshold item outcome * D.posteriorUtility item outcome)
        D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_value_int threshold hthreshold_meas hthreshold_bounds item)
  have hother_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            other item outcome * D.posteriorUtility item outcome)
        D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_value_int other hother_meas hother_bounds item)
  calc
    D.expectedPosteriorUtility threshold -
        D.expectedPosteriorUtility other =
        ∫ outcome,
          (∑ item : Applicant,
              threshold item outcome * D.posteriorUtility item outcome) -
            ∑ item : Applicant,
              other item outcome * D.posteriorUtility item outcome ∂D.law := by
      unfold expectedPosteriorUtility
      rw [← integral_sub hthreshold_sum_int hother_sum_int]
    _ =
        ∫ outcome,
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome ∂D.law := by
      refine integral_congr_ae ?_
      exact ae_of_all D.law fun outcome => by
        change
          (∑ item : Applicant,
              threshold item outcome * D.posteriorUtility item outcome) -
            (∑ item : Applicant,
              other item outcome * D.posteriorUtility item outcome) =
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro item _
        ring

/-- Difference in expected cost as the integral of cost deltas. -/
theorem expectedCost_sub_eq_integral_delta_cost
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (threshold other : AllocationPolicy Applicant Outcome)
    (hthreshold_meas : AllocationPolicyMeasurable threshold)
    (hthreshold_bounds : AllocationPolicyBounds threshold)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other) :
    D.expectedCost threshold - D.expectedCost other =
      ∫ outcome,
        ∑ item : Applicant,
          D.allocCost item * (threshold item outcome - other item outcome)
        ∂D.law := by
  classical
  have hpolicy_cost_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome => D.allocCost item * policy item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    have hpolicy_int :
        Integrable (fun outcome => policy item outcome) D.law := by
      have hone_int :
          Integrable (fun _ : Outcome => (1 : ℝ)) D.law := by
        simpa using
          (MeasureTheory.integrable_const (μ := D.law) (c := (1 : ℝ)))
      simpa [mul_one] using
        hone_int.bdd_mul (hpolicy_meas item).aestronglyMeasurable hbound
    exact hpolicy_int.const_mul (D.allocCost item)
  have hthreshold_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item * threshold item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_cost_int threshold hthreshold_meas hthreshold_bounds item)
  have hother_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item * other item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_cost_int other hother_meas hother_bounds item)
  calc
    D.expectedCost threshold - D.expectedCost other =
        ∫ outcome,
          (∑ item : Applicant,
              D.allocCost item * threshold item outcome) -
            ∑ item : Applicant,
              D.allocCost item * other item outcome ∂D.law := by
      unfold expectedCost
      rw [← integral_sub hthreshold_sum_int hother_sum_int]
    _ =
        ∫ outcome,
          ∑ item : Applicant,
            D.allocCost item * (threshold item outcome - other item outcome)
          ∂D.law := by
      refine integral_congr_ae ?_
      exact ae_of_all D.law fun outcome => by
        change
          (∑ item : Applicant,
              D.allocCost item * threshold item outcome) -
            (∑ item : Applicant,
              D.allocCost item * other item outcome) =
          ∑ item : Applicant,
            D.allocCost item * (threshold item outcome - other item outcome)
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro item _
        ring

/--
Appendix Lemma 1 key inequality for finite score-threshold policies in a
measure-space model.
-/
theorem scoreThresholdPolicy_expected_delta_key
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ) (other : AllocationPolicy Applicant Outcome)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other) :
    t * (D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other) ≤
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) -
        D.expectedPosteriorUtility other := by
  classical
  let threshold : AllocationPolicy Applicant Outcome :=
    D.scoreThresholdPolicy t alpha
  have hthreshold_meas : AllocationPolicyMeasurable threshold := by
    simpa [threshold] using D.scoreThresholdPolicy_measurable t alpha
  have hthreshold_bounds : AllocationPolicyBounds threshold := by
    simpa [threshold] using
      D.scoreThresholdPolicy_bounds t alpha halpha_nonneg halpha_le_one
  have hpolicy_cost_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome => D.allocCost item * policy item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    have hpolicy_int :
        Integrable (fun outcome => policy item outcome) D.law := by
      have hone_int :
          Integrable (fun _ : Outcome => (1 : ℝ)) D.law := by
        simpa using
          (MeasureTheory.integrable_const (μ := D.law) (c := (1 : ℝ)))
      simpa [mul_one] using
        hone_int.bdd_mul (hpolicy_meas item).aestronglyMeasurable hbound
    exact hpolicy_int.const_mul (D.allocCost item)
  have hpolicy_value_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome =>
                  policy item outcome * D.posteriorUtility item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    exact (D.posteriorUtility_integrable item).bdd_mul
      (hpolicy_meas item).aestronglyMeasurable hbound
  have hcost_delta_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item *
              (threshold item outcome - other item outcome)) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ => by
        have hthreshold_int :=
          hpolicy_cost_int threshold hthreshold_meas hthreshold_bounds item
        have hother_int :=
          hpolicy_cost_int other hother_meas hother_bounds item
        refine Integrable.congr (hthreshold_int.sub hother_int) ?_
        exact ae_of_all D.law fun outcome => by
          change
            D.allocCost item * threshold item outcome -
                D.allocCost item * other item outcome =
              D.allocCost item *
                (threshold item outcome - other item outcome)
          ring)
  have hvalue_delta_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ => by
        have hthreshold_int :=
          hpolicy_value_int threshold hthreshold_meas hthreshold_bounds item
        have hother_int :=
          hpolicy_value_int other hother_meas hother_bounds item
        refine Integrable.congr (hthreshold_int.sub hother_int) ?_
        exact ae_of_all D.law fun outcome => by
          change
            threshold item outcome * D.posteriorUtility item outcome -
                other item outcome * D.posteriorUtility item outcome =
              (threshold item outcome - other item outcome) *
                D.posteriorUtility item outcome
          ring)
  have hpoint :
      ∀ᵐ outcome ∂D.law,
        t *
            (∑ item : Applicant,
              D.allocCost item *
                (threshold item outcome - other item outcome)) ≤
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome := by
    exact ae_of_all D.law fun outcome => by
      calc
        t *
            (∑ item : Applicant,
              D.allocCost item *
                (threshold item outcome - other item outcome))
            =
            ∑ item : Applicant,
              (threshold item outcome - other item outcome) *
                (D.allocCost item * t) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro item _
          ring
        _ ≤
            ∑ item : Applicant,
              (threshold item outcome - other item outcome) *
                D.posteriorUtility item outcome := by
          refine Finset.sum_le_sum ?_
          intro item _
          simpa [threshold] using
            D.scoreThresholdPolicy_delta_thresholdCost_le_delta_utility
              hcost_pos t alpha other hother_bounds item outcome
  have hmono :
      ∫ outcome,
          t *
            (∑ item : Applicant,
              D.allocCost item *
                (threshold item outcome - other item outcome)) ∂D.law
        ≤
      ∫ outcome,
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome ∂D.law := by
    exact integral_mono_ae (hcost_delta_int.const_mul t)
      hvalue_delta_int hpoint
  calc
    t * (D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other)
        =
        t * (∫ outcome,
          ∑ item : Applicant,
            D.allocCost item *
              (threshold item outcome - other item outcome) ∂D.law) := by
      rw [D.expectedCost_sub_eq_integral_delta_cost
        (D.scoreThresholdPolicy t alpha) other
        (D.scoreThresholdPolicy_measurable t alpha)
        (D.scoreThresholdPolicy_bounds t alpha halpha_nonneg halpha_le_one)
        hother_meas hother_bounds]
    _ =
        ∫ outcome,
          t *
            (∑ item : Applicant,
              D.allocCost item *
                (threshold item outcome - other item outcome)) ∂D.law := by
      rw [integral_const_mul]
    _ ≤
        ∫ outcome,
          ∑ item : Applicant,
            (threshold item outcome - other item outcome) *
              D.posteriorUtility item outcome ∂D.law := hmono
    _ =
        D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) -
          D.expectedPosteriorUtility other := by
      rw [D.expectedPosteriorUtility_sub_eq_integral_delta_value
        (D.scoreThresholdPolicy t alpha) other
        (D.scoreThresholdPolicy_measurable t alpha)
        (D.scoreThresholdPolicy_bounds t alpha halpha_nonneg halpha_le_one)
        hother_meas hother_bounds]

/--
Appendix Lemma 1, Case 1: a finite score-threshold policy with the same
expected cost has weakly higher expected posterior utility.
-/
theorem scoreThresholdPolicy_expectedPosteriorUtility_ge_of_expectedCost_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ) (other : AllocationPolicy Applicant Outcome)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other)
    (hcost :
      D.expectedCost (D.scoreThresholdPolicy t alpha) =
        D.expectedCost other) :
    D.expectedPosteriorUtility other ≤
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) := by
  have hkey :=
    D.scoreThresholdPolicy_expected_delta_key hcost_pos t alpha other
      halpha_nonneg halpha_le_one hother_meas hother_bounds
  have hcost_zero :
      D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other = 0 := by
    linarith
  rw [hcost_zero, mul_zero] at hkey
  linarith

/--
Appendix Lemma 1, Case 2: a finite score-threshold policy with the same
expected utility and positive threshold has weakly lower expected cost.
-/
theorem scoreThresholdPolicy_expectedCost_le_of_expectedPosteriorUtility_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ) (other : AllocationPolicy Applicant Outcome)
    (ht : 0 < t)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other)
    (hutility :
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) =
        D.expectedPosteriorUtility other) :
    D.expectedCost (D.scoreThresholdPolicy t alpha) ≤ D.expectedCost other := by
  have hkey :=
    D.scoreThresholdPolicy_expected_delta_key hcost_pos t alpha other
      halpha_nonneg halpha_le_one hother_meas hother_bounds
  have hutility_zero :
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) -
          D.expectedPosteriorUtility other = 0 := by
    linarith
  rw [hutility_zero] at hkey
  have hcost_nonpos :
      D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other ≤ 0 := by
    have hmul :
        (D.expectedCost (D.scoreThresholdPolicy t alpha) -
            D.expectedCost other) * t ≤ 0 := by
      simpa [mul_comm] using hkey
    exact nonpos_of_mul_nonpos_left hmul ht
  linarith

/--
Endpoint-aware score-threshold policy.  The formal endpoints allocate to
everyone (`-∞`) or no one (`∞`); finite thresholds use the ordinary score rule.
-/
noncomputable def extendedScoreThresholdPolicy
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : RealThreshold) (alpha : ℝ) :
    AllocationPolicy Applicant Outcome :=
  match threshold with
  | RealThreshold.negInf => fun _ _ => 1
  | RealThreshold.finite t => D.scoreThresholdPolicy t alpha
  | RealThreshold.posInf => fun _ _ => 0

/-- An endpoint-aware score-threshold policy is a bounded allocation policy. -/
theorem extendedScoreThresholdPolicy_bounds
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : RealThreshold) (alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1) :
    AllocationPolicyBounds (D.extendedScoreThresholdPolicy threshold alpha) := by
  cases threshold with
  | negInf =>
      intro item outcome
      simp [extendedScoreThresholdPolicy]
  | finite t =>
      simpa [extendedScoreThresholdPolicy] using
        D.scoreThresholdPolicy_bounds t alpha halpha_nonneg halpha_le_one
  | posInf =>
      intro item outcome
      simp [extendedScoreThresholdPolicy]

/-- An endpoint-aware score-threshold policy is measurable. -/
theorem extendedScoreThresholdPolicy_measurable
    (D : MeasureCostAwareData Applicant Outcome)
    (threshold : RealThreshold) (alpha : ℝ) :
    AllocationPolicyMeasurable
      (D.extendedScoreThresholdPolicy threshold alpha) := by
  cases threshold with
  | negInf =>
      intro item
      simp [extendedScoreThresholdPolicy]
  | finite t =>
      simpa [extendedScoreThresholdPolicy] using
        D.scoreThresholdPolicy_measurable t alpha
  | posInf =>
      intro item
      simp [extendedScoreThresholdPolicy]

/--
Total utility mass of the aggregate score measure equals expected posterior
utility under the all-one allocation.
-/
theorem utilityScoreMeasure_real_univ_eq_expectedPosteriorUtility_all
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item) :
    D.utilityScoreMeasure.real (Set.univ : Set ℝ) =
      D.expectedPosteriorUtility (fun _ _ => 1) := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  let itemMass : Applicant → ℝ := fun item =>
    (valueWeightedScoreMeasure D.law (D.score item)
      (D.posteriorUtility item)).real (Set.univ : Set ℝ)
  have hmeasure :
      D.utilityScoreMeasure.real (Set.univ : Set ℝ) =
        ∑ item : Applicant, itemMass item := by
    simpa [utilityScoreMeasure, itemMass] using
      finiteValueWeightedScoreMeasureSum_real_univ
        (fun _ : Applicant => D.law) D.score D.posteriorUtility
  have hitem :
      ∀ item : Applicant,
        itemMass item =
          ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
    intro item
    simpa [itemMass] using
      valueWeightedScoreMeasure_real_univ_eq_integral
        D.law (D.score_measurable item)
        (D.posteriorUtility_integrable item)
        (hutility_nonneg item)
  have hexpected :
      D.expectedPosteriorUtility (fun _ _ => 1) =
        ∑ item : Applicant,
          ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
    calc
      D.expectedPosteriorUtility (fun _ _ => 1)
          =
          ∫ outcome,
            ∑ item : Applicant,
              D.posteriorUtility item outcome ∂D.law := by
        unfold expectedPosteriorUtility
        simp
      _ =
          ∑ item : Applicant,
            ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
        exact MeasureTheory.integral_finset_sum Finset.univ
          (fun item _ => D.posteriorUtility_integrable item)
  calc
    D.utilityScoreMeasure.real (Set.univ : Set ℝ)
        = ∑ item : Applicant, itemMass item := hmeasure
    _ =
        ∑ item : Applicant,
          ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
      refine Finset.sum_congr rfl ?_
      intro item _
      exact hitem item
    _ = D.expectedPosteriorUtility (fun _ _ => 1) := hexpected.symm

/--
The utility-weighted score measure has all of its mass above every
nonpositive threshold when utilities are nonnegative and costs are strictly
positive.
-/
theorem upperTailMass_utilityScoreMeasure_eq_univ_of_nonpos_threshold
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    {t : ℝ} (ht : t ≤ 0) :
    upperTailMass D.utilityScoreMeasure t =
      D.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
  classical
  letI :
      ∀ item : Applicant,
        IsFiniteMeasure
          (valueWeightedScoreMeasure D.law (D.score item)
            (D.posteriorUtility item)) := fun item =>
    isFiniteMeasure_valueWeightedScoreMeasure_of_hasFiniteIntegral
      D.law (D.score item) (D.posteriorUtility item)
      (D.posteriorUtility_integrable item).hasFiniteIntegral
  have htail :=
    D.upperTailMass_utilityScoreMeasure_eq_sum_integral_indicator
      hutility_nonneg t
  have hitem :
      ∀ item : Applicant,
        (∫ outcome,
          ({outcome | t < D.score item outcome}.indicator
            (D.posteriorUtility item)) outcome ∂D.law) =
        ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
    intro item
    refine integral_congr_ae ?_
    filter_upwards [hutility_nonneg item] with outcome hU_nonneg
    by_cases hstrict : t < D.score item outcome
    · have hmem :
          outcome ∈ {outcome | t < D.score item outcome} := hstrict
      rw [Set.indicator_of_mem hmem]
    · have hscore_nonneg : 0 ≤ D.score item outcome := by
        dsimp [score]
        exact div_nonneg hU_nonneg (hcost_pos item).le
      have hscore_le_t : D.score item outcome ≤ t := le_of_not_gt hstrict
      have hscore_zero : D.score item outcome = 0 := by
        linarith
      have hU_zero : D.posteriorUtility item outcome = 0 := by
        have hscore_zero' :
            D.posteriorUtility item outcome / D.allocCost item = 0 := by
          simpa [score] using hscore_zero
        have hmul :=
          congrArg (fun x => x * D.allocCost item) hscore_zero'
        have hmul' :
            (D.posteriorUtility item outcome / D.allocCost item) *
                D.allocCost item =
              0 * D.allocCost item := by
          simpa using hmul
        rw [div_mul_cancel₀ _ (ne_of_gt (hcost_pos item))] at hmul'
        simpa using hmul'
      have hnotmem :
          outcome ∉ {outcome | t < D.score item outcome} := hstrict
      rw [Set.indicator_of_notMem hnotmem]
      exact hU_zero.symm
  have hexpected :
      D.expectedPosteriorUtility (fun _ _ => 1) =
        ∑ item : Applicant,
          ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
    calc
      D.expectedPosteriorUtility (fun _ _ => 1)
          =
          ∫ outcome,
            ∑ item : Applicant,
              D.posteriorUtility item outcome ∂D.law := by
        unfold expectedPosteriorUtility
        simp
      _ =
          ∑ item : Applicant,
            ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
        exact MeasureTheory.integral_finset_sum Finset.univ
          (fun item _ => D.posteriorUtility_integrable item)
  calc
    upperTailMass D.utilityScoreMeasure t =
        ∑ item : Applicant,
          ∫ outcome,
            ({outcome | t < D.score item outcome}.indicator
              (D.posteriorUtility item)) outcome ∂D.law := htail
    _ =
        ∑ item : Applicant,
          ∫ outcome, D.posteriorUtility item outcome ∂D.law := by
      refine Finset.sum_congr rfl ?_
      intro item _
      exact hitem item
    _ = D.expectedPosteriorUtility (fun _ _ => 1) := hexpected.symm
    _ = D.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
      (D.utilityScoreMeasure_real_univ_eq_expectedPosteriorUtility_all
        hutility_nonneg).symm

/--
Strictly interior positive utility targets are attained by finite strictly
positive score thresholds.
-/
theorem exists_positive_scoreThresholdPolicy_expectedPosteriorUtility_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    {target : ℝ}
    (htarget_pos : 0 < target)
    (htarget_lt_total :
      target < D.utilityScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ t : ℝ,
      ∃ alpha : ℝ,
        0 < t ∧ 0 ≤ alpha ∧ alpha ≤ 1 ∧
          D.expectedPosteriorUtility
            (D.scoreThresholdPolicy t alpha) = target := by
  classical
  haveI : IsFiniteMeasure D.utilityScoreMeasure :=
    D.utilityScoreMeasure_finite
  rcases exists_upperTailMass_Ici_bracket_finite
      D.utilityScoreMeasure htarget_pos htarget_lt_total with
    ⟨t, hstrict, hclosed⟩
  have ht_pos : 0 < t := by
    by_contra hnot
    have ht_nonpos : t ≤ 0 := le_of_not_gt hnot
    have htail_total :=
      D.upperTailMass_utilityScoreMeasure_eq_univ_of_nonpos_threshold
        hutility_nonneg hcost_pos ht_nonpos
    have htotal_le_target :
        D.utilityScoreMeasure.real (Set.univ : Set ℝ) ≤ target := by
      simpa [htail_total] using hstrict
    exact not_lt_of_ge htotal_le_target htarget_lt_total
  have hlow_le_high :
      upperTailMass D.utilityScoreMeasure t ≤
        D.utilityScoreMeasure.real (Set.Ici t) :=
    hstrict.trans hclosed
  rcases exists_unit_interval_interpolation
      hlow_le_high hstrict hclosed with
    ⟨alpha, halpha_nonneg, halpha_le_one, halpha⟩
  refine ⟨t, alpha, ht_pos, halpha_nonneg, halpha_le_one, ?_⟩
  rw [D.expectedPosteriorUtility_scoreThresholdPolicy_eq hutility_nonneg]
  exact halpha

/--
Interior same-utility replacement: if a bounded measurable allocation has
strictly positive utility below the all-one utility mass, a positive finite
score-threshold policy achieves the same utility at weakly lower cost.
-/
theorem exists_sameUtilityScoreThresholdPolicy_of_policy_of_pos_lt_total
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (hutility_pos : 0 < D.expectedPosteriorUtility original)
    (hutility_lt_total :
      D.expectedPosteriorUtility original <
        D.utilityScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ t : ℝ,
      ∃ alpha : ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          0 < t ∧ 0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds replacement ∧
              AllocationPolicyMeasurable replacement ∧
                replacement = D.scoreThresholdPolicy t alpha ∧
                  D.expectedPosteriorUtility replacement =
                    D.expectedPosteriorUtility original ∧
                    D.expectedCost replacement ≤
                      D.expectedCost original := by
  rcases D.exists_positive_scoreThresholdPolicy_expectedPosteriorUtility_eq
      hutility_nonneg hcost_pos hutility_pos hutility_lt_total with
    ⟨t, alpha, ht_pos, halpha_nonneg, halpha_le_one, hutility⟩
  refine ⟨t, alpha, D.scoreThresholdPolicy t alpha, ht_pos,
    halpha_nonneg, halpha_le_one, ?_, ?_, rfl, hutility, ?_⟩
  · exact D.scoreThresholdPolicy_bounds
      t alpha halpha_nonneg halpha_le_one
  · exact D.scoreThresholdPolicy_measurable t alpha
  · exact
      D.scoreThresholdPolicy_expectedCost_le_of_expectedPosteriorUtility_eq
        hcost_pos t alpha original ht_pos halpha_nonneg halpha_le_one
        horiginal_meas horiginal_bounds hutility

/--
Zero-utility endpoint for Lemma 3: the all-zero endpoint threshold has the
same utility and weakly lower cost when the original allocation has zero
expected utility.
-/
theorem exists_sameUtilityZeroEndpointThresholdPolicy_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_bounds : AllocationPolicyBounds original)
    (hutility_zero : D.expectedPosteriorUtility original = 0) :
    ∃ replacement : AllocationPolicy Applicant Outcome,
      AllocationPolicyBounds replacement ∧
        AllocationPolicyMeasurable replacement ∧
          replacement = D.extendedScoreThresholdPolicy RealThreshold.posInf 0 ∧
            D.expectedPosteriorUtility replacement =
              D.expectedPosteriorUtility original ∧
              D.expectedCost replacement ≤ D.expectedCost original := by
  refine ⟨D.extendedScoreThresholdPolicy RealThreshold.posInf 0, ?_, ?_,
    rfl, ?_, ?_⟩
  · exact D.extendedScoreThresholdPolicy_bounds
      RealThreshold.posInf 0 (by norm_num) (by norm_num)
  · exact D.extendedScoreThresholdPolicy_measurable RealThreshold.posInf 0
  · simpa [extendedScoreThresholdPolicy, expectedPosteriorUtility] using
      hutility_zero.symm
  · have hcost_nonneg :
        0 ≤ D.expectedCost original := by
      unfold expectedCost
      exact integral_nonneg_of_ae
        (ae_of_all D.law fun outcome =>
          Finset.sum_nonneg fun item _ =>
            mul_nonneg (hcost_pos item).le
              (horiginal_bounds item outcome).1)
    simpa [extendedScoreThresholdPolicy, expectedCost] using hcost_nonneg

/--
The zero finite threshold with no boundary allocation attains the all-one
utility mass.
-/
theorem expectedPosteriorUtility_scoreThresholdPolicy_zero_zero_eq_univ
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    D.expectedPosteriorUtility (D.scoreThresholdPolicy 0 0) =
      D.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
  rw [D.expectedPosteriorUtility_scoreThresholdPolicy_eq hutility_nonneg]
  have htail :=
    D.upperTailMass_utilityScoreMeasure_eq_univ_of_nonpos_threshold
      hutility_nonneg hcost_pos (by norm_num : (0 : ℝ) ≤ 0)
  simp [htail]

/--
Total-utility endpoint for Lemma 3: if a bounded measurable allocation already
attains the all-one utility mass, then the finite threshold `t = 0`, `alpha = 0`
has weakly lower expected cost.
-/
theorem scoreThresholdPolicy_zero_zero_expectedCost_le_of_expectedPosteriorUtility_eq_univ
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (hutility_total :
      D.expectedPosteriorUtility original =
        D.utilityScoreMeasure.real (Set.univ : Set ℝ)) :
    D.expectedCost (D.scoreThresholdPolicy 0 0) ≤
      D.expectedCost original := by
  classical
  let allPolicy : AllocationPolicy Applicant Outcome := fun _ _ => 1
  have hall_meas : AllocationPolicyMeasurable allPolicy := by
    intro item
    exact measurable_const
  have hall_bounds : AllocationPolicyBounds allPolicy := by
    intro item outcome
    simp [allPolicy]
  have hpolicy_value_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome =>
                  policy item outcome * D.posteriorUtility item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    exact (D.posteriorUtility_integrable item).bdd_mul
      (hpolicy_meas item).aestronglyMeasurable hbound
  have hpolicy_cost_int :
      ∀ policy : AllocationPolicy Applicant Outcome,
        AllocationPolicyMeasurable policy →
          AllocationPolicyBounds policy →
            ∀ item : Applicant,
              Integrable
                (fun outcome => D.allocCost item * policy item outcome)
                D.law := by
    intro policy hpolicy_meas hpolicy_bounds item
    have hbound :
        ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
      ae_of_all D.law fun outcome => by
        exact abs_le.mpr
          ⟨by linarith [(hpolicy_bounds item outcome).1],
            (hpolicy_bounds item outcome).2⟩
    have hpolicy_int :
        Integrable (fun outcome => policy item outcome) D.law := by
      have hone_int :
          Integrable (fun _ : Outcome => (1 : ℝ)) D.law := by
        simpa using
          (MeasureTheory.integrable_const (μ := D.law) (c := (1 : ℝ)))
      simpa [mul_one] using
        hone_int.bdd_mul (hpolicy_meas item).aestronglyMeasurable hbound
    exact hpolicy_int.const_mul (D.allocCost item)
  have horig_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            original item outcome * D.posteriorUtility item outcome)
        D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_value_int original horiginal_meas horiginal_bounds item)
  have hall_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            allPolicy item outcome * D.posteriorUtility item outcome)
        D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_value_int allPolicy hall_meas hall_bounds item)
  have horig_le_all :
      (fun outcome =>
        ∑ item : Applicant,
          original item outcome * D.posteriorUtility item outcome)
        ≤ᵐ[D.law]
      (fun outcome =>
        ∑ item : Applicant,
          allPolicy item outcome * D.posteriorUtility item outcome) := by
    have hutility_nonneg_all :
        ∀ᵐ outcome ∂D.law,
          ∀ item : Applicant, 0 ≤ D.posteriorUtility item outcome :=
      Filter.eventually_all.2 fun item => hutility_nonneg item
    filter_upwards [hutility_nonneg_all] with outcome hutility_nonneg
    refine Finset.sum_le_sum ?_
    intro item _
    have hbounds := horiginal_bounds item outcome
    have hU := hutility_nonneg item
    simp [allPolicy]
    nlinarith
  have hintegral_eq :
      (∫ outcome,
        ∑ item : Applicant,
          original item outcome * D.posteriorUtility item outcome ∂D.law) =
      ∫ outcome,
        ∑ item : Applicant,
          allPolicy item outcome * D.posteriorUtility item outcome ∂D.law := by
    change D.expectedPosteriorUtility original =
      D.expectedPosteriorUtility allPolicy
    rw [hutility_total]
    exact D.utilityScoreMeasure_real_univ_eq_expectedPosteriorUtility_all
      hutility_nonneg
  have hsum_eq :
      (fun outcome =>
        ∑ item : Applicant,
          original item outcome * D.posteriorUtility item outcome)
        =ᵐ[D.law]
      (fun outcome =>
        ∑ item : Applicant,
          allPolicy item outcome * D.posteriorUtility item outcome) :=
    (integral_eq_iff_of_ae_le horig_sum_int hall_sum_int
      horig_le_all).1 hintegral_eq
  have hthreshold_le_original :
      ∀ᵐ outcome ∂D.law,
        ∀ item : Applicant,
          D.scoreThresholdPolicy 0 0 item outcome ≤
            original item outcome := by
    have hutility_nonneg_all :
        ∀ᵐ outcome ∂D.law,
          ∀ item : Applicant, 0 ≤ D.posteriorUtility item outcome :=
      Filter.eventually_all.2 fun item => hutility_nonneg item
    filter_upwards [hsum_eq, hutility_nonneg_all] with
      outcome hsum hutility_nonneg item
    by_cases habove : 0 < D.score item outcome
    · have hU_pos : 0 < D.posteriorUtility item outcome := by
        have hmul :=
          mul_lt_mul_of_pos_right habove (hcost_pos item)
        rw [zero_mul] at hmul
        have hmul' :
            (D.score item outcome) * D.allocCost item =
              D.posteriorUtility item outcome := by
          dsimp [score]
          rw [div_mul_cancel₀ _ (ne_of_gt (hcost_pos item))]
        rwa [hmul'] at hmul
      have hgap_sum_zero :
          ∑ item' : Applicant,
            (1 - original item' outcome) *
              D.posteriorUtility item' outcome = 0 := by
        have hsum' :
            (∑ item' : Applicant,
              original item' outcome *
                D.posteriorUtility item' outcome) =
            ∑ item' : Applicant,
              D.posteriorUtility item' outcome := by
          simpa [allPolicy] using hsum
        calc
          ∑ item' : Applicant,
            (1 - original item' outcome) *
              D.posteriorUtility item' outcome
              =
              (∑ item' : Applicant,
                D.posteriorUtility item' outcome) -
                ∑ item' : Applicant,
                  original item' outcome *
                    D.posteriorUtility item' outcome := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro item' _
            ring
          _ = 0 := by
            linarith
      have hterm_nonneg :
          0 ≤ (1 - original item outcome) *
            D.posteriorUtility item outcome := by
        exact mul_nonneg (sub_nonneg.mpr
          (horiginal_bounds item outcome).2) (hutility_nonneg item)
      have hterm_le_sum :
          (1 - original item outcome) *
              D.posteriorUtility item outcome ≤
            ∑ item' : Applicant,
              (1 - original item' outcome) *
                D.posteriorUtility item' outcome := by
        exact Finset.single_le_sum
          (fun item' _ =>
            mul_nonneg
              (sub_nonneg.mpr (horiginal_bounds item' outcome).2)
              (hutility_nonneg item'))
          (Finset.mem_univ item)
      have hterm_zero :
          (1 - original item outcome) *
            D.posteriorUtility item outcome = 0 := by
        exact le_antisymm (by
          simpa [hgap_sum_zero] using hterm_le_sum) hterm_nonneg
      have horig_one : original item outcome = 1 := by
        have hleft_zero :
            1 - original item outcome = 0 :=
          (mul_eq_zero.mp hterm_zero).resolve_right hU_pos.ne'
        linarith
      simp [scoreThresholdPolicy, habove, horig_one]
    · by_cases hbelow : D.score item outcome < 0
      · simp [scoreThresholdPolicy, habove, hbelow,
          (horiginal_bounds item outcome).1]
      · simp [scoreThresholdPolicy, habove, hbelow,
          (horiginal_bounds item outcome).1]
  have hthreshold_meas :
      AllocationPolicyMeasurable (D.scoreThresholdPolicy 0 0) :=
    D.scoreThresholdPolicy_measurable 0 0
  have hthreshold_bounds :
      AllocationPolicyBounds (D.scoreThresholdPolicy 0 0) :=
    D.scoreThresholdPolicy_bounds 0 0 (by norm_num) (by norm_num)
  have hthreshold_cost_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item *
              D.scoreThresholdPolicy 0 0 item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_cost_int (D.scoreThresholdPolicy 0 0)
          hthreshold_meas hthreshold_bounds item)
  have horiginal_cost_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item * original item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        hpolicy_cost_int original horiginal_meas horiginal_bounds item)
  unfold expectedCost
  exact integral_mono_ae hthreshold_cost_int horiginal_cost_int
    (hthreshold_le_original.mono fun outcome hle =>
      Finset.sum_le_sum fun item _ =>
        mul_le_mul_of_nonneg_left (hle item) (hcost_pos item).le)

/--
Total cost mass of the aggregate score measure equals expected cost under the
all-one allocation.
-/
theorem costScoreMeasure_real_univ_eq_expectedCost_all
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item) :
    D.costScoreMeasure.real (Set.univ : Set ℝ) =
      D.expectedCost (fun _ _ => 1) := by
  classical
  let itemMass : Applicant → ℝ := fun item =>
    D.allocCost item * (D.law.map (D.score item)).real (Set.univ : Set ℝ)
  have hmeasure :
      D.costScoreMeasure.real (Set.univ : Set ℝ) =
        ∑ item : Applicant, itemMass item := by
    simpa [costScoreMeasure, itemMass] using
      finiteWeightedScoreMeasureSum_real_univ
        D.allocCost (fun _ : Applicant => D.law) D.score hcost_nonneg
  have hitem :
      ∀ item : Applicant,
        itemMass item =
          ∫ outcome, D.allocCost item ∂D.law := by
    intro item
    calc
      itemMass item =
          D.allocCost item * D.law.real (Set.univ : Set Outcome) := by
        simp [itemMass,
          MeasureTheory.map_measureReal_apply
            (D.score_measurable item) MeasurableSet.univ]
      _ = ∫ outcome, D.allocCost item ∂D.law := by
        rw [MeasureTheory.integral_const]
        ring
  have hexpected :
      D.expectedCost (fun _ _ => 1) =
        ∑ item : Applicant,
          ∫ outcome, D.allocCost item ∂D.law := by
    have hterm_int :
        ∀ item : Applicant,
          Integrable (fun _ : Outcome => D.allocCost item) D.law := by
      intro item
      simpa using
        (MeasureTheory.integrable_const (μ := D.law)
          (c := D.allocCost item))
    calc
      D.expectedCost (fun _ _ => 1)
          =
          ∫ outcome,
            ∑ item : Applicant,
              D.allocCost item ∂D.law := by
        unfold expectedCost
        simp
      _ =
          ∑ item : Applicant,
            ∫ outcome, D.allocCost item ∂D.law := by
        exact MeasureTheory.integral_finset_sum Finset.univ
          (fun item _ => hterm_int item)
  calc
    D.costScoreMeasure.real (Set.univ : Set ℝ)
        = ∑ item : Applicant, itemMass item := hmeasure
    _ =
        ∑ item : Applicant,
          ∫ outcome, D.allocCost item ∂D.law := by
      refine Finset.sum_congr rfl ?_
      intro item _
      exact hitem item
    _ = D.expectedCost (fun _ _ => 1) := hexpected.symm

/-- A bounded measurable allocation has integrable utility contribution. -/
theorem policy_mul_posteriorUtility_integrable
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy)
    (item : Applicant) :
    Integrable
      (fun outcome =>
        policy item outcome * D.posteriorUtility item outcome) D.law := by
  have hbound :
      ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
    ae_of_all D.law fun outcome => by
      exact abs_le.mpr
        ⟨by linarith [(hpolicy_bounds item outcome).1],
          (hpolicy_bounds item outcome).2⟩
  exact (D.posteriorUtility_integrable item).bdd_mul
    (hpolicy_meas item).aestronglyMeasurable hbound

/-- A bounded measurable allocation has integrable cost contribution. -/
theorem allocCost_mul_policy_integrable
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy)
    (item : Applicant) :
    Integrable
      (fun outcome => D.allocCost item * policy item outcome) D.law := by
  have hbound :
      ∀ᵐ outcome ∂D.law, ‖policy item outcome‖ ≤ (1 : ℝ) :=
    ae_of_all D.law fun outcome => by
      exact abs_le.mpr
        ⟨by linarith [(hpolicy_bounds item outcome).1],
          (hpolicy_bounds item outcome).2⟩
  have hpolicy_int :
      Integrable (fun outcome => policy item outcome) D.law := by
    have hone_int :
        Integrable (fun _ : Outcome => (1 : ℝ)) D.law := by
      simpa using
        (MeasureTheory.integrable_const (μ := D.law) (c := (1 : ℝ)))
    simpa [mul_one] using
      hone_int.bdd_mul (hpolicy_meas item).aestronglyMeasurable hbound
  exact hpolicy_int.const_mul (D.allocCost item)

/-- Positive-part reduction preserves allocation-policy bounds. -/
theorem positivePartPolicy_bounds
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy : AllocationPolicyBounds policy) :
    AllocationPolicyBounds (D.positivePartPolicy policy) := by
  intro item outcome
  by_cases hpos : 0 < D.posteriorUtility item outcome
  · simpa [positivePartPolicy, hpos] using hpolicy item outcome
  · exact ⟨by simp [positivePartPolicy, hpos],
      by simp [positivePartPolicy, hpos]⟩

/-- Positive-part reduction preserves allocation-policy measurability. -/
theorem positivePartPolicy_measurable
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy : AllocationPolicyMeasurable policy) :
    AllocationPolicyMeasurable (D.positivePartPolicy policy) := by
  intro item
  let positiveSet : Set Outcome :=
    {outcome | 0 < D.posteriorUtility item outcome}
  have hpositiveSet : MeasurableSet positiveSet := by
    change MeasurableSet
      ((D.posteriorUtility item) ⁻¹' Set.Ioi (0 : ℝ))
    exact D.posteriorUtility_measurable item measurableSet_Ioi
  have hindicator :
      D.positivePartPolicy policy item =
        positiveSet.indicator (policy item) := by
    funext outcome
    by_cases hpos : 0 < D.posteriorUtility item outcome
    · simp [positivePartPolicy, positiveSet, hpos]
    · simp [positivePartPolicy, positiveSet, hpos]
  rw [hindicator]
  exact (hpolicy item).indicator hpositiveSet

/-- Positive-part reduction is pointwise no larger than the original policy. -/
theorem positivePartPolicy_le_policy
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy : AllocationPolicyBounds policy) :
    ∀ item outcome,
      D.positivePartPolicy policy item outcome ≤ policy item outcome := by
  intro item outcome
  by_cases hpos : 0 < D.posteriorUtility item outcome
  · simp [positivePartPolicy, hpos]
  · simpa [positivePartPolicy, hpos] using (hpolicy item outcome).1

/- On a nonzero positive-part atom, posterior utility is strictly positive. -/
theorem positivePartPolicy_pos_utility_of_ne_zero
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    {item : Applicant} {outcome : Outcome}
    (hne : D.positivePartPolicy policy item outcome ≠ 0) :
    0 < D.posteriorUtility item outcome := by
  by_contra hnot
  exact hne (by simp [positivePartPolicy, hnot])

/--
Removing nonpositive-utility outcomes cannot decrease expected posterior
utility for a bounded measurable allocation.
-/
theorem expectedPosteriorUtility_le_positivePartPolicy
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤
      D.expectedPosteriorUtility (D.positivePartPolicy policy) := by
  classical
  have hpositive_meas :
      AllocationPolicyMeasurable (D.positivePartPolicy policy) :=
    D.positivePartPolicy_measurable policy hpolicy_meas
  have hpositive_bounds :
      AllocationPolicyBounds (D.positivePartPolicy policy) :=
    D.positivePartPolicy_bounds policy hpolicy_bounds
  have hpolicy_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            policy item outcome * D.posteriorUtility item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.policy_mul_posteriorUtility_integrable
          policy hpolicy_meas hpolicy_bounds item)
  have hpositive_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.positivePartPolicy policy item outcome *
              D.posteriorUtility item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.policy_mul_posteriorUtility_integrable
          (D.positivePartPolicy policy) hpositive_meas
          hpositive_bounds item)
  unfold expectedPosteriorUtility
  exact integral_mono_ae hpolicy_sum_int hpositive_sum_int
    (ae_of_all D.law fun outcome =>
      Finset.sum_le_sum fun item _ => by
        by_cases hpos : 0 < D.posteriorUtility item outcome
        · simp [positivePartPolicy, hpos]
        · have hutility_nonpos :
              D.posteriorUtility item outcome ≤ 0 := le_of_not_gt hpos
          have hpolicy_nonneg : 0 ≤ policy item outcome :=
            (hpolicy_bounds item outcome).1
          have hterm_nonpos :
              policy item outcome * D.posteriorUtility item outcome ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hpolicy_nonneg hutility_nonpos
          simpa [positivePartPolicy, hpos] using hterm_nonpos)

/-- Positive-part reduction cannot increase expected allocation cost. -/
theorem expectedCost_positivePartPolicy_le
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    D.expectedCost (D.positivePartPolicy policy) ≤ D.expectedCost policy := by
  classical
  have hpositive_meas :
      AllocationPolicyMeasurable (D.positivePartPolicy policy) :=
    D.positivePartPolicy_measurable policy hpolicy_meas
  have hpositive_bounds :
      AllocationPolicyBounds (D.positivePartPolicy policy) :=
    D.positivePartPolicy_bounds policy hpolicy_bounds
  have hpositive_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item *
              D.positivePartPolicy policy item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.allocCost_mul_policy_integrable
          (D.positivePartPolicy policy) hpositive_meas
          hpositive_bounds item)
  have hpolicy_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item * policy item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.allocCost_mul_policy_integrable
          policy hpolicy_meas hpolicy_bounds item)
  unfold expectedCost
  exact integral_mono_ae hpositive_sum_int hpolicy_sum_int
    (ae_of_all D.law fun outcome =>
      Finset.sum_le_sum fun item _ =>
        mul_le_mul_of_nonneg_left
          (D.positivePartPolicy_le_policy policy hpolicy_bounds item outcome)
          (hcost_nonneg item))

/--
Measure-level signed positive-part reduction for the equality-target proof
chain.

Given a bounded measurable allocation whose expected posterior utility is a
nonnegative target, zeroing all nonpositive-utility outcomes preserves enough
utility for the target, does not increase cost, and leaves support only where
posterior utility is strictly positive.
-/
theorem measurePositivePartPolicy_cost_le
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (target : ℝ)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy)
    (htarget_nonneg : 0 ≤ target)
    (htarget_eq : D.expectedPosteriorUtility policy = target) :
    AllocationPolicyBounds (D.positivePartPolicy policy) ∧
      AllocationPolicyMeasurable (D.positivePartPolicy policy) ∧
      0 ≤ target ∧
      target ≤ D.expectedPosteriorUtility (D.positivePartPolicy policy) ∧
      D.expectedCost (D.positivePartPolicy policy) ≤ D.expectedCost policy ∧
      (∀ item outcome,
        D.positivePartPolicy policy item outcome ≠ 0 →
          0 < D.posteriorUtility item outcome) := by
  refine ⟨D.positivePartPolicy_bounds policy hpolicy_bounds,
    D.positivePartPolicy_measurable policy hpolicy_meas,
    htarget_nonneg, ?_, ?_, ?_⟩
  · calc
      target = D.expectedPosteriorUtility policy := htarget_eq.symm
      _ ≤ D.expectedPosteriorUtility (D.positivePartPolicy policy) :=
        D.expectedPosteriorUtility_le_positivePartPolicy
          policy hpolicy_meas hpolicy_bounds
  · exact D.expectedCost_positivePartPolicy_le
      policy (fun item => (hcost_pos item).le) hpolicy_meas hpolicy_bounds
  · intro item outcome hne
    exact D.positivePartPolicy_pos_utility_of_ne_zero policy hne

/-- Positive-part reduction is zero on nonpositive-utility outcomes. -/
theorem positivePartPolicy_eq_zero_of_nonpos
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    {item : Applicant} {outcome : Outcome}
    (hutility_nonpos : D.posteriorUtility item outcome ≤ 0) :
    D.positivePartPolicy policy item outcome = 0 := by
  have hnot_pos : ¬ 0 < D.posteriorUtility item outcome :=
    not_lt.mpr hutility_nonpos
  simp [positivePartPolicy, hnot_pos]

/--
On any policy supported only where signed posterior utility is positive, the
positive-posterior copy has the same expected posterior utility as the original
signed data.
-/
theorem positivePosteriorUtilityData_expectedPosteriorUtility_eq_of_zero_on_nonpos
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hzero :
      ∀ item outcome,
        D.posteriorUtility item outcome ≤ 0 → policy item outcome = 0) :
    (D.positivePosteriorUtilityData).expectedPosteriorUtility policy =
      D.expectedPosteriorUtility policy := by
  classical
  unfold expectedPosteriorUtility positivePosteriorUtilityData
  refine integral_congr_ae (ae_of_all D.law fun outcome => ?_)
  refine Finset.sum_congr rfl ?_
  intro item _
  by_cases hnonneg : 0 ≤ D.posteriorUtility item outcome
  · simp [max_eq_left hnonneg]
  · have hnonpos : D.posteriorUtility item outcome ≤ 0 :=
      le_of_not_ge hnonneg
    simp [max_eq_right hnonpos, hzero item outcome hnonpos]

/-- The positive-posterior copy leaves expected costs unchanged. -/
theorem positivePosteriorUtilityData_expectedCost_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) :
    (D.positivePosteriorUtilityData).expectedCost policy =
      D.expectedCost policy := by
  rfl

/--
Positive-part policies have the same expected posterior utility in the
positive-posterior copy and in the original signed data.
-/
theorem positivePosteriorUtilityData_expectedPosteriorUtility_positivePartPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome) :
    (D.positivePosteriorUtilityData).expectedPosteriorUtility
        (D.positivePartPolicy policy) =
      D.expectedPosteriorUtility (D.positivePartPolicy policy) := by
  exact
    D.positivePosteriorUtilityData_expectedPosteriorUtility_eq_of_zero_on_nonpos
      (D.positivePartPolicy policy)
      (fun item outcome hnonpos =>
        D.positivePartPolicy_eq_zero_of_nonpos policy hnonpos)

/--
For positive finite thresholds, the score-threshold policy for the
positive-posterior copy is definitionally the same allocation as the signed
score-threshold policy.
-/
theorem positivePosteriorUtilityData_scoreThresholdPolicy_eq_of_pos_threshold
    (D : MeasureCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    {t alpha : ℝ} (ht : 0 < t) :
    (D.positivePosteriorUtilityData).scoreThresholdPolicy t alpha =
      D.scoreThresholdPolicy t alpha := by
  funext item outcome
  by_cases hutility_pos : 0 < D.posteriorUtility item outcome
  · have hmax :
        max (D.posteriorUtility item outcome) 0 =
          D.posteriorUtility item outcome :=
      max_eq_left hutility_pos.le
    have hscore :
        (D.positivePosteriorUtilityData).score item outcome =
          D.score item outcome := by
      simp [score, positivePosteriorUtilityData, hmax]
    simp [scoreThresholdPolicy, hscore]
  · have hutility_nonpos : D.posteriorUtility item outcome ≤ 0 :=
      le_of_not_gt hutility_pos
    have hmax :
        max (D.posteriorUtility item outcome) 0 = 0 :=
      max_eq_right hutility_nonpos
    have hscore_nonpos : D.score item outcome ≤ 0 := by
      simpa [score] using
        div_nonpos_of_nonpos_of_nonneg hutility_nonpos
          (hcost_pos item).le
    have hpositive_score_zero :
        (D.positivePosteriorUtilityData).score item outcome = 0 := by
      simp [score, positivePosteriorUtilityData, hmax]
    have hpositive_not_above :
        ¬ t < (D.positivePosteriorUtilityData).score item outcome := by
      rw [hpositive_score_zero]
      exact not_lt.mpr ht.le
    have hpositive_below :
        (D.positivePosteriorUtilityData).score item outcome < t := by
      rw [hpositive_score_zero]
      exact ht
    have horiginal_not_above :
        ¬ t < D.score item outcome := by
      exact not_lt.mpr (hscore_nonpos.trans ht.le)
    have horiginal_below : D.score item outcome < t :=
      lt_of_le_of_lt hscore_nonpos ht
    simp [scoreThresholdPolicy, hpositive_not_above, hpositive_below,
      horiginal_not_above, horiginal_below]

/--
The zero-threshold, zero-boundary policy is unchanged by replacing signed
utilities with their positive part.
-/
theorem positivePosteriorUtilityData_scoreThresholdPolicy_zero_zero_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    (D.positivePosteriorUtilityData).scoreThresholdPolicy 0 0 =
      D.scoreThresholdPolicy 0 0 := by
  funext item outcome
  by_cases hutility_pos : 0 < D.posteriorUtility item outcome
  · have hmax :
        max (D.posteriorUtility item outcome) 0 =
          D.posteriorUtility item outcome :=
      max_eq_left hutility_pos.le
    have hscore :
        (D.positivePosteriorUtilityData).score item outcome =
          D.score item outcome := by
      simp [score, positivePosteriorUtilityData, hmax]
    simp [scoreThresholdPolicy, hscore]
  · have hutility_nonpos : D.posteriorUtility item outcome ≤ 0 :=
      le_of_not_gt hutility_pos
    have hmax :
        max (D.posteriorUtility item outcome) 0 = 0 :=
      max_eq_right hutility_nonpos
    have hscore_nonpos : D.score item outcome ≤ 0 := by
      simpa [score] using
        div_nonpos_of_nonpos_of_nonneg hutility_nonpos
          (hcost_pos item).le
    have hpositive_score_zero :
        (D.positivePosteriorUtilityData).score item outcome = 0 := by
      simp [score, positivePosteriorUtilityData, hmax]
    have hpositive_not_above :
        ¬ (0 : ℝ) < (D.positivePosteriorUtilityData).score item outcome := by
      rw [hpositive_score_zero]
      exact not_lt.mpr le_rfl
    have hpositive_not_below :
        ¬ (D.positivePosteriorUtilityData).score item outcome < (0 : ℝ) := by
      rw [hpositive_score_zero]
      exact not_lt.mpr le_rfl
    have horiginal_not_above :
        ¬ (0 : ℝ) < D.score item outcome :=
      not_lt.mpr hscore_nonpos
    by_cases horiginal_below : D.score item outcome < (0 : ℝ)
    · simp [scoreThresholdPolicy, hpositive_not_above,
        hpositive_not_below, horiginal_not_above, horiginal_below]
    · simp [scoreThresholdPolicy, hpositive_not_above,
        hpositive_not_below, horiginal_not_above, horiginal_below]

/--
For a positive threshold, the signed score-threshold policy allocates zero on
nonpositive-utility outcomes.
-/
theorem scoreThresholdPolicy_eq_zero_of_nonpos_of_pos_threshold
    (D : MeasureCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    {t alpha : ℝ} (ht : 0 < t)
    {item : Applicant} {outcome : Outcome}
    (hutility_nonpos : D.posteriorUtility item outcome ≤ 0) :
    D.scoreThresholdPolicy t alpha item outcome = 0 := by
  have hscore_nonpos : D.score item outcome ≤ 0 := by
    simpa [score] using
      div_nonpos_of_nonpos_of_nonneg hutility_nonpos
        (hcost_pos item).le
  have hnot_above : ¬ t < D.score item outcome :=
    not_lt.mpr (hscore_nonpos.trans ht.le)
  have hbelow : D.score item outcome < t :=
    lt_of_le_of_lt hscore_nonpos ht
  simp [scoreThresholdPolicy, hnot_above, hbelow]

/--
The zero-threshold, zero-boundary signed score-threshold policy allocates zero
on nonpositive-utility outcomes.
-/
theorem scoreThresholdPolicy_zero_zero_eq_zero_of_nonpos
    (D : MeasureCostAwareData Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    {item : Applicant} {outcome : Outcome}
    (hutility_nonpos : D.posteriorUtility item outcome ≤ 0) :
    D.scoreThresholdPolicy 0 0 item outcome = 0 := by
  have hscore_nonpos : D.score item outcome ≤ 0 := by
    simpa [score] using
      div_nonpos_of_nonpos_of_nonneg hutility_nonpos
        (hcost_pos item).le
  have hnot_above : ¬ (0 : ℝ) < D.score item outcome :=
    not_lt.mpr hscore_nonpos
  by_cases hbelow : D.score item outcome < (0 : ℝ)
  · simp [scoreThresholdPolicy, hnot_above, hbelow]
  · simp [scoreThresholdPolicy, hnot_above, hbelow]

/--
Positive-threshold score policies with weakly lower expected utility have
weakly lower expected cost.  This is the inequality form needed after
positive-part reduction, where the positive part may carry more utility than
the original nonnegative target.
-/
theorem scoreThresholdPolicy_expectedCost_le_of_expectedPosteriorUtility_le
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (t alpha : ℝ) (other : AllocationPolicy Applicant Outcome)
    (ht : 0 < t)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other)
    (hutility :
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) ≤
        D.expectedPosteriorUtility other) :
    D.expectedCost (D.scoreThresholdPolicy t alpha) ≤ D.expectedCost other := by
  have hkey :=
    D.scoreThresholdPolicy_expected_delta_key hcost_pos t alpha other
      halpha_nonneg halpha_le_one hother_meas hother_bounds
  have hutility_nonpos :
      D.expectedPosteriorUtility (D.scoreThresholdPolicy t alpha) -
          D.expectedPosteriorUtility other ≤ 0 := by
    linarith
  have hcost_mul_nonpos :
      (D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other) * t ≤ 0 := by
    simpa [mul_comm] using hkey.trans hutility_nonpos
  have hcost_nonpos :
      D.expectedCost (D.scoreThresholdPolicy t alpha) -
          D.expectedCost other ≤ 0 :=
    nonpos_of_mul_nonpos_left hcost_mul_nonpos ht
  linarith

/-- Expected posterior utility of a bounded measurable allocation is nonnegative. -/
theorem expectedPosteriorUtility_nonneg_of_measurable_bounds
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    0 ≤ D.expectedPosteriorUtility policy := by
  classical
  have hutility_nonneg_all :
      ∀ᵐ outcome ∂D.law,
        ∀ item : Applicant, 0 ≤ D.posteriorUtility item outcome :=
    Filter.eventually_all.2 fun item => hutility_nonneg item
  unfold expectedPosteriorUtility
  exact integral_nonneg_of_ae
    (hutility_nonneg_all.mono fun outcome hutility_nonneg =>
      Finset.sum_nonneg fun item _ =>
        mul_nonneg (hpolicy_bounds item outcome).1
          (hutility_nonneg item))

/--
Expected posterior utility of a bounded measurable allocation is at most the
all-one utility mass.
-/
theorem expectedPosteriorUtility_le_utilityScoreMeasure_univ_of_measurable_bounds
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    D.expectedPosteriorUtility policy ≤
      D.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
  classical
  have hpolicy_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            policy item outcome * D.posteriorUtility item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.policy_mul_posteriorUtility_integrable
          policy hpolicy_meas hpolicy_bounds item)
  have hall_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            (fun _ : Applicant => fun _ : Outcome => (1 : ℝ))
              item outcome * D.posteriorUtility item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ => by
        simpa using D.posteriorUtility_integrable item)
  have hutility_nonneg_all :
      ∀ᵐ outcome ∂D.law,
        ∀ item : Applicant, 0 ≤ D.posteriorUtility item outcome :=
    Filter.eventually_all.2 fun item => hutility_nonneg item
  rw [D.utilityScoreMeasure_real_univ_eq_expectedPosteriorUtility_all
    hutility_nonneg]
  unfold expectedPosteriorUtility
  exact integral_mono_ae hpolicy_sum_int hall_sum_int
    (hutility_nonneg_all.mono fun outcome hutility_nonneg =>
      Finset.sum_le_sum fun item _ => by
        have hbounds := hpolicy_bounds item outcome
        have hU := hutility_nonneg item
        nlinarith)

/-- Expected cost of a bounded allocation is nonnegative. -/
theorem expectedCost_nonneg_of_bounds
    (D : MeasureCostAwareData Applicant Outcome)
    (policy : AllocationPolicy Applicant Outcome)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    0 ≤ D.expectedCost policy := by
  classical
  unfold expectedCost
  exact integral_nonneg_of_ae
    (ae_of_all D.law fun outcome =>
      Finset.sum_nonneg fun item _ =>
        mul_nonneg (hcost_nonneg item)
          (hpolicy_bounds item outcome).1)

/--
Expected cost of a bounded measurable allocation is at most the all-one cost
mass.
-/
theorem expectedCost_le_costScoreMeasure_univ_of_measurable_bounds
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    D.expectedCost policy ≤ D.costScoreMeasure.real (Set.univ : Set ℝ) := by
  classical
  have hpolicy_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item * policy item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.allocCost_mul_policy_integrable
          policy hpolicy_meas hpolicy_bounds item)
  have hall_sum_int :
      Integrable
        (fun outcome =>
          ∑ item : Applicant,
            D.allocCost item *
              (fun _ : Applicant => fun _ : Outcome => (1 : ℝ))
                item outcome) D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        by
          simpa using
            (MeasureTheory.integrable_const (μ := D.law)
              (c := D.allocCost item)))
  rw [D.costScoreMeasure_real_univ_eq_expectedCost_all hcost_nonneg]
  unfold expectedCost
  exact integral_mono_ae hpolicy_sum_int hall_sum_int
    (ae_of_all D.law fun outcome =>
      Finset.sum_le_sum fun item _ => by
        have hbounds := hpolicy_bounds item outcome
        have hc := hcost_nonneg item
        nlinarith)

/--
Signed-utility same-utility threshold replacement for a nonnegative target.

This is the single-group measure analogue of the finite signed positive-part
route: first discard nonpositive-utility allocation mass, then run the
nonnegative threshold-attainment machinery on the positive-posterior copy and
translate the threshold policy back to the original signed data.
-/
theorem exists_sameUtilityExtendedScoreThresholdPolicy_of_policy_signed_nonnegative_target
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (htarget_nonneg : 0 ≤ D.expectedPosteriorUtility original) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds replacement ∧
              AllocationPolicyMeasurable replacement ∧
                replacement =
                  D.extendedScoreThresholdPolicy threshold alpha ∧
                  D.expectedPosteriorUtility replacement =
                    D.expectedPosteriorUtility original ∧
                    D.expectedCost replacement ≤
                      D.expectedCost original := by
  classical
  let Dpos : MeasureCostAwareData Applicant Outcome :=
    D.positivePosteriorUtilityData
  letI : IsFiniteMeasure Dpos.law := by
    dsimp [Dpos, positivePosteriorUtilityData]
    infer_instance
  let originalPos : AllocationPolicy Applicant Outcome :=
    D.positivePartPolicy original
  have hpos_nonneg :
      ∀ item, 0 ≤ᵐ[Dpos.law] Dpos.posteriorUtility item := by
    simpa [Dpos] using D.positivePosteriorUtilityData_nonneg
  have hpos_cost_pos : ∀ item, 0 < Dpos.allocCost item := by
    intro item
    simpa [Dpos] using hcost_pos item
  have hpos_original_meas : AllocationPolicyMeasurable originalPos := by
    simpa [originalPos] using
      D.positivePartPolicy_measurable original horiginal_meas
  have hpos_original_bounds : AllocationPolicyBounds originalPos := by
    simpa [originalPos] using
      D.positivePartPolicy_bounds original horiginal_bounds
  have htarget_le_originalPos_signed :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility originalPos := by
    simpa [originalPos] using
      D.expectedPosteriorUtility_le_positivePartPolicy
        original horiginal_meas horiginal_bounds
  have horiginalPos_utility_eq :
      Dpos.expectedPosteriorUtility originalPos =
        D.expectedPosteriorUtility originalPos := by
    simpa [Dpos, originalPos] using
      D.positivePosteriorUtilityData_expectedPosteriorUtility_positivePartPolicy_eq
        original
  have htarget_le_originalPos_pos :
      D.expectedPosteriorUtility original ≤
        Dpos.expectedPosteriorUtility originalPos := by
    rw [horiginalPos_utility_eq]
    exact htarget_le_originalPos_signed
  have horiginalPos_le_total :
      Dpos.expectedPosteriorUtility originalPos ≤
        Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
    exact
      Dpos.expectedPosteriorUtility_le_utilityScoreMeasure_univ_of_measurable_bounds
        hpos_nonneg originalPos hpos_original_meas hpos_original_bounds
  have htarget_le_total :
      D.expectedPosteriorUtility original ≤
        Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
    htarget_le_originalPos_pos.trans horiginalPos_le_total
  have hpospart_cost_le_original :
      D.expectedCost originalPos ≤ D.expectedCost original := by
    simpa [originalPos] using
      D.expectedCost_positivePartPolicy_le
        original (fun item => (hcost_pos item).le)
        horiginal_meas horiginal_bounds
  by_cases hzero : D.expectedPosteriorUtility original = 0
  · rcases D.exists_sameUtilityZeroEndpointThresholdPolicy_of_policy
        original hcost_pos horiginal_bounds hzero with
      ⟨replacement, hbounds, hmeas, hrepl, hutility, hcost⟩
    exact ⟨RealThreshold.posInf, 0, replacement,
      by norm_num, by norm_num, hbounds, hmeas, hrepl, hutility, hcost⟩
  · have htarget_pos : 0 < D.expectedPosteriorUtility original :=
      lt_of_le_of_ne htarget_nonneg (Ne.symm hzero)
    by_cases htotal :
        D.expectedPosteriorUtility original =
          Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ)
    · let replacement : AllocationPolicy Applicant Outcome :=
        D.scoreThresholdPolicy 0 0
      have hbounds : AllocationPolicyBounds replacement := by
        simpa [replacement] using
          D.scoreThresholdPolicy_bounds 0 0 (by norm_num) (by norm_num)
      have hmeas : AllocationPolicyMeasurable replacement := by
        simpa [replacement] using D.scoreThresholdPolicy_measurable 0 0
      have hsupport :
          ∀ item outcome,
            D.posteriorUtility item outcome ≤ 0 →
              replacement item outcome = 0 := by
        intro item outcome hnonpos
        simpa [replacement] using
          D.scoreThresholdPolicy_zero_zero_eq_zero_of_nonpos
            hcost_pos hnonpos
      have hpositive_policy_eq :
          Dpos.scoreThresholdPolicy 0 0 = replacement := by
        simpa [Dpos, replacement] using
          D.positivePosteriorUtilityData_scoreThresholdPolicy_zero_zero_eq
            hcost_pos
      have hpositive_utility :
          Dpos.expectedPosteriorUtility replacement =
            Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
        rw [← hpositive_policy_eq]
        exact
          Dpos.expectedPosteriorUtility_scoreThresholdPolicy_zero_zero_eq_univ
            hpos_nonneg hpos_cost_pos
      have hutility_bridge :
          Dpos.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility replacement := by
        simpa [Dpos] using
          D.positivePosteriorUtilityData_expectedPosteriorUtility_eq_of_zero_on_nonpos
            replacement hsupport
      have hutility :
          D.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility original := by
        calc
          D.expectedPosteriorUtility replacement =
              Dpos.expectedPosteriorUtility replacement := hutility_bridge.symm
          _ = Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
              hpositive_utility
          _ = D.expectedPosteriorUtility original := htotal.symm
      have horiginalPos_total :
          Dpos.expectedPosteriorUtility originalPos =
            Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
        refine le_antisymm horiginalPos_le_total ?_
        calc
          Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) =
              D.expectedPosteriorUtility original := htotal.symm
          _ ≤ Dpos.expectedPosteriorUtility originalPos :=
              htarget_le_originalPos_pos
      have hpositive_cost :
          Dpos.expectedCost (Dpos.scoreThresholdPolicy 0 0) ≤
            Dpos.expectedCost originalPos :=
        Dpos.scoreThresholdPolicy_zero_zero_expectedCost_le_of_expectedPosteriorUtility_eq_univ
          originalPos hpos_nonneg hpos_cost_pos hpos_original_meas
          hpos_original_bounds horiginalPos_total
      have hpositive_cost_replacement :
          Dpos.expectedCost replacement ≤ Dpos.expectedCost originalPos := by
        simpa [hpositive_policy_eq] using hpositive_cost
      have hcost_to_pospart :
          D.expectedCost replacement ≤ D.expectedCost originalPos := by
        simpa [Dpos, originalPos, positivePosteriorUtilityData,
          expectedCost] using hpositive_cost_replacement
      have hcost : D.expectedCost replacement ≤ D.expectedCost original :=
        hcost_to_pospart.trans hpospart_cost_le_original
      refine ⟨RealThreshold.finite 0, 0, replacement,
        by norm_num, by norm_num, hbounds, hmeas, ?_, hutility, hcost⟩
      simp [replacement, extendedScoreThresholdPolicy]
    · have htarget_lt_total :
          D.expectedPosteriorUtility original <
            Dpos.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
        lt_of_le_of_ne htarget_le_total htotal
      rcases
          Dpos.exists_positive_scoreThresholdPolicy_expectedPosteriorUtility_eq
            hpos_nonneg hpos_cost_pos htarget_pos htarget_lt_total with
        ⟨t, alpha, ht_pos, halpha_nonneg, halpha_le_one,
          hpositive_utility⟩
      let replacement : AllocationPolicy Applicant Outcome :=
        D.scoreThresholdPolicy t alpha
      have hbounds : AllocationPolicyBounds replacement := by
        simpa [replacement] using
          D.scoreThresholdPolicy_bounds t alpha halpha_nonneg halpha_le_one
      have hmeas : AllocationPolicyMeasurable replacement := by
        simpa [replacement] using D.scoreThresholdPolicy_measurable t alpha
      have hsupport :
          ∀ item outcome,
            D.posteriorUtility item outcome ≤ 0 →
              replacement item outcome = 0 := by
        intro item outcome hnonpos
        simpa [replacement] using
          D.scoreThresholdPolicy_eq_zero_of_nonpos_of_pos_threshold
            hcost_pos ht_pos hnonpos
      have hpositive_policy_eq :
          Dpos.scoreThresholdPolicy t alpha = replacement := by
        simpa [Dpos, replacement] using
          D.positivePosteriorUtilityData_scoreThresholdPolicy_eq_of_pos_threshold
            hcost_pos ht_pos
      have hpositive_utility_replacement :
          Dpos.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility original := by
        rw [← hpositive_policy_eq]
        exact hpositive_utility
      have hutility_bridge :
          Dpos.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility replacement := by
        simpa [Dpos] using
          D.positivePosteriorUtilityData_expectedPosteriorUtility_eq_of_zero_on_nonpos
            replacement hsupport
      have hutility :
          D.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility original := by
        calc
          D.expectedPosteriorUtility replacement =
              Dpos.expectedPosteriorUtility replacement := hutility_bridge.symm
          _ = D.expectedPosteriorUtility original :=
              hpositive_utility_replacement
      have hpositive_utility_le_originalPos :
          Dpos.expectedPosteriorUtility (Dpos.scoreThresholdPolicy t alpha) ≤
            Dpos.expectedPosteriorUtility originalPos := by
        calc
          Dpos.expectedPosteriorUtility (Dpos.scoreThresholdPolicy t alpha) =
              D.expectedPosteriorUtility original := hpositive_utility
          _ ≤ Dpos.expectedPosteriorUtility originalPos :=
              htarget_le_originalPos_pos
      have hpositive_cost :
          Dpos.expectedCost (Dpos.scoreThresholdPolicy t alpha) ≤
            Dpos.expectedCost originalPos :=
        Dpos.scoreThresholdPolicy_expectedCost_le_of_expectedPosteriorUtility_le
          hpos_cost_pos t alpha originalPos ht_pos halpha_nonneg
          halpha_le_one hpos_original_meas hpos_original_bounds
          hpositive_utility_le_originalPos
      have hpositive_cost_replacement :
          Dpos.expectedCost replacement ≤ Dpos.expectedCost originalPos := by
        simpa [hpositive_policy_eq] using hpositive_cost
      have hcost_to_pospart :
          D.expectedCost replacement ≤ D.expectedCost originalPos := by
        simpa [Dpos, originalPos, positivePosteriorUtilityData,
          expectedCost] using hpositive_cost_replacement
      have hcost : D.expectedCost replacement ≤ D.expectedCost original :=
        hcost_to_pospart.trans hpospart_cost_le_original
      refine ⟨RealThreshold.finite t, alpha, replacement,
        halpha_nonneg, halpha_le_one, hbounds, hmeas, ?_, hutility, hcost⟩
      simp [replacement, extendedScoreThresholdPolicy]

/--
A bounded allocation with zero expected cost has zero expected posterior
utility when every allocation cost is strictly positive.
-/
theorem expectedPosteriorUtility_eq_zero_of_expectedCost_eq_zero
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy)
    (hcost_zero : D.expectedCost policy = 0) :
    D.expectedPosteriorUtility policy = 0 := by
  classical
  let costSum : Outcome → ℝ := fun outcome =>
    ∑ item : Applicant, D.allocCost item * policy item outcome
  have hcost_sum_int : Integrable costSum D.law := by
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ =>
        D.allocCost_mul_policy_integrable
          policy hpolicy_meas hpolicy_bounds item)
  have hcost_sum_nonneg : 0 ≤ᵐ[D.law] costSum := by
    exact ae_of_all D.law fun outcome =>
      Finset.sum_nonneg fun item _ =>
        mul_nonneg (hcost_pos item).le
          (hpolicy_bounds item outcome).1
  have hcost_sum_integral_zero :
      ∫ outcome, costSum outcome ∂D.law = 0 := by
    simpa [expectedCost, costSum] using hcost_zero
  have hcost_sum_zero_ae : costSum =ᵐ[D.law] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      hcost_sum_nonneg hcost_sum_int).1 hcost_sum_integral_zero
  have hpolicy_zero :
      ∀ item : Applicant,
        (fun outcome => policy item outcome) =ᵐ[D.law] 0 := by
    intro item
    filter_upwards [hcost_sum_zero_ae] with outcome hsum
    have hterm_nonneg :
        0 ≤ D.allocCost item * policy item outcome :=
      mul_nonneg (hcost_pos item).le (hpolicy_bounds item outcome).1
    have hterm_le_sum :
        D.allocCost item * policy item outcome ≤ costSum outcome := by
      dsimp [costSum]
      exact Finset.single_le_sum
        (fun other _ =>
          mul_nonneg (hcost_pos other).le
            (hpolicy_bounds other outcome).1)
        (Finset.mem_univ item)
    have hterm_zero :
        D.allocCost item * policy item outcome = 0 := by
      exact le_antisymm (by simpa [hsum] using hterm_le_sum) hterm_nonneg
    exact (mul_eq_zero.mp hterm_zero).resolve_left
      (ne_of_gt (hcost_pos item))
  have hutility_zero_ae :
      (fun outcome =>
        ∑ item : Applicant,
          policy item outcome * D.posteriorUtility item outcome) =ᵐ[D.law]
        0 := by
    have hpolicy_zero_all :
        ∀ᵐ outcome ∂D.law,
          ∀ item : Applicant, policy item outcome = 0 :=
      Filter.eventually_all.2 hpolicy_zero
    filter_upwards [hpolicy_zero_all] with outcome hzero
    exact Finset.sum_eq_zero fun item _ => by
      simp [hzero item]
  unfold expectedPosteriorUtility
  exact integral_eq_zero_of_ae hutility_zero_ae

/--
A bounded measurable allocation with the same expected cost as the all-one
allocation agrees with it in expected posterior utility.  This endpoint fact
uses only positive allocation costs, so posterior utilities may have either
sign.
-/
theorem expectedPosteriorUtility_eq_all_of_expectedCost_eq_all
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy)
    (hcost_all :
      D.expectedCost (fun _ _ => 1) = D.expectedCost policy) :
    D.expectedPosteriorUtility policy =
      D.expectedPosteriorUtility (fun _ _ => 1) := by
  classical
  let complement : AllocationPolicy Applicant Outcome :=
    fun item outcome => 1 - policy item outcome
  have hcomplement_meas : AllocationPolicyMeasurable complement := by
    intro item
    exact measurable_const.sub (hpolicy_meas item)
  have hcomplement_bounds : AllocationPolicyBounds complement := by
    intro item outcome
    have hbounds := hpolicy_bounds item outcome
    constructor <;> dsimp [complement] <;> linarith
  have hcost_decomp :
      D.expectedCost (fun _ _ => 1) =
        D.expectedCost policy + D.expectedCost complement := by
    unfold expectedCost
    rw [← integral_add]
    · refine integral_congr_ae (ae_of_all D.law fun outcome => ?_)
      change (∑ item : Applicant, D.allocCost item * 1) =
        (∑ item : Applicant, D.allocCost item * policy item outcome) +
          ∑ item : Applicant, D.allocCost item * complement item outcome
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro item _
      dsimp [complement]
      ring
    · exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun item _ => D.allocCost_mul_policy_integrable
          policy hpolicy_meas hpolicy_bounds item)
    · exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun item _ => D.allocCost_mul_policy_integrable
          complement hcomplement_meas hcomplement_bounds item)
  have hcomplement_cost_zero : D.expectedCost complement = 0 := by
    linarith
  have hcomplement_utility_zero :
      D.expectedPosteriorUtility complement = 0 :=
    D.expectedPosteriorUtility_eq_zero_of_expectedCost_eq_zero
      complement hcost_pos hcomplement_meas hcomplement_bounds
      hcomplement_cost_zero
  have hutility_decomp :
      D.expectedPosteriorUtility (fun _ _ => 1) =
        D.expectedPosteriorUtility policy +
          D.expectedPosteriorUtility complement := by
    unfold expectedPosteriorUtility
    rw [← integral_add]
    · refine integral_congr_ae (ae_of_all D.law fun outcome => ?_)
      change (∑ item : Applicant, 1 * D.posteriorUtility item outcome) =
        (∑ item : Applicant,
          policy item outcome * D.posteriorUtility item outcome) +
          ∑ item : Applicant,
            complement item outcome * D.posteriorUtility item outcome
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro item _
      dsimp [complement]
      ring
    · exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun item _ => D.policy_mul_posteriorUtility_integrable
          policy hpolicy_meas hpolicy_bounds item)
    · exact MeasureTheory.integrable_finset_sum Finset.univ
        (fun item _ => D.policy_mul_posteriorUtility_integrable
          complement hcomplement_meas hcomplement_bounds item)
  linarith

/--
Appendix Lemma 1, Case 1, for endpoint-aware score thresholds: if an
endpoint-aware threshold policy has the same expected cost as another bounded
measurable allocation, then it has weakly higher expected posterior utility.
-/
theorem extendedScoreThresholdPolicy_expectedPosteriorUtility_ge_of_expectedCost_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (threshold : RealThreshold) (alpha : ℝ)
    (halpha_nonneg : 0 ≤ alpha) (halpha_le_one : alpha ≤ 1)
    (other : AllocationPolicy Applicant Outcome)
    (hother_meas : AllocationPolicyMeasurable other)
    (hother_bounds : AllocationPolicyBounds other)
    (hcost :
      D.expectedCost (D.extendedScoreThresholdPolicy threshold alpha) =
        D.expectedCost other) :
    D.expectedPosteriorUtility other ≤
      D.expectedPosteriorUtility
        (D.extendedScoreThresholdPolicy threshold alpha) := by
  cases threshold with
  | finite t =>
      simpa [extendedScoreThresholdPolicy] using
        D.scoreThresholdPolicy_expectedPosteriorUtility_ge_of_expectedCost_eq
          hcost_pos t alpha other halpha_nonneg halpha_le_one
          hother_meas hother_bounds (by
            simpa [extendedScoreThresholdPolicy] using hcost)
  | negInf =>
      have hcost_all :
          D.expectedCost (fun _ _ => 1) = D.expectedCost other := by
        simpa [extendedScoreThresholdPolicy] using hcost
      have hutility_all :=
        D.expectedPosteriorUtility_eq_all_of_expectedCost_eq_all
          other hcost_pos hother_meas hother_bounds hcost_all
      simpa [extendedScoreThresholdPolicy, hutility_all]
  | posInf =>
      have hcost_zero : D.expectedCost other = 0 := by
        have hzero :
            (0 : ℝ) = D.expectedCost other := by
          simpa [extendedScoreThresholdPolicy, expectedCost] using hcost
        exact hzero.symm
      have hutility_zero :
          D.expectedPosteriorUtility other = 0 :=
        D.expectedPosteriorUtility_eq_zero_of_expectedCost_eq_zero
          other hcost_pos hother_meas hother_bounds hcost_zero
      rw [hutility_zero]
      simp [extendedScoreThresholdPolicy, expectedPosteriorUtility]

/--
Endpoint-aware expected utility formula for score-threshold policies.
-/
theorem expectedPosteriorUtility_extendedScoreThresholdPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (threshold : RealThreshold) (alpha : ℝ) :
    D.expectedPosteriorUtility
        (D.extendedScoreThresholdPolicy threshold alpha) =
      threshold.strictUpperTailMass D.utilityScoreMeasure +
        alpha *
          (threshold.closedUpperTailMass D.utilityScoreMeasure -
            threshold.strictUpperTailMass D.utilityScoreMeasure) := by
  cases threshold with
  | negInf =>
      have htotal :=
        D.utilityScoreMeasure_real_univ_eq_expectedPosteriorUtility_all
          hutility_nonneg
      simp [extendedScoreThresholdPolicy, RealThreshold.strictUpperTailMass,
        RealThreshold.closedUpperTailMass, htotal.symm]
  | finite t =>
      simpa [extendedScoreThresholdPolicy, RealThreshold.strictUpperTailMass,
        RealThreshold.closedUpperTailMass] using
        D.expectedPosteriorUtility_scoreThresholdPolicy_eq
          hutility_nonneg t alpha
  | posInf =>
      simp [extendedScoreThresholdPolicy, expectedPosteriorUtility,
        RealThreshold.strictUpperTailMass, RealThreshold.closedUpperTailMass]

/--
Endpoint-aware expected cost formula for score-threshold policies.
-/
theorem expectedCost_extendedScoreThresholdPolicy_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (threshold : RealThreshold) (alpha : ℝ) :
    D.expectedCost (D.extendedScoreThresholdPolicy threshold alpha) =
      threshold.strictUpperTailMass D.costScoreMeasure +
        alpha *
          (threshold.closedUpperTailMass D.costScoreMeasure -
            threshold.strictUpperTailMass D.costScoreMeasure) := by
  cases threshold with
  | negInf =>
      have htotal :=
        D.costScoreMeasure_real_univ_eq_expectedCost_all hcost_nonneg
      simp [extendedScoreThresholdPolicy, RealThreshold.strictUpperTailMass,
        RealThreshold.closedUpperTailMass, htotal.symm]
  | finite t =>
      simpa [extendedScoreThresholdPolicy, RealThreshold.strictUpperTailMass,
        RealThreshold.closedUpperTailMass] using
        D.expectedCost_scoreThresholdPolicy_eq hcost_nonneg t alpha
  | posInf =>
      simp [extendedScoreThresholdPolicy, expectedCost,
        RealThreshold.strictUpperTailMass, RealThreshold.closedUpperTailMass]

/--
Measure-level Lemma 2, utility version: every target utility between zero and
the total utility mass is exactly achieved by an endpoint-aware score-threshold
policy.
-/
theorem exists_extendedScoreThresholdPolicy_expectedPosteriorUtility_eq
    (D : MeasureCostAwareData Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total :
      target ≤ D.utilityScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ policy : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds policy ∧
              policy = D.extendedScoreThresholdPolicy threshold alpha ∧
                D.expectedPosteriorUtility policy = target := by
  rcases D.exists_utilityScoreMeasure_threshold_attainment
      htarget_nonneg htarget_le_total with
    ⟨threshold, alpha, halpha_nonneg, halpha_le_one, hmass⟩
  refine ⟨threshold, alpha,
    D.extendedScoreThresholdPolicy threshold alpha,
    halpha_nonneg, halpha_le_one, ?_, rfl, ?_⟩
  · exact
      D.extendedScoreThresholdPolicy_bounds threshold alpha
        halpha_nonneg halpha_le_one
  · rw [D.expectedPosteriorUtility_extendedScoreThresholdPolicy_eq
      hutility_nonneg]
    exact hmass

/--
Measure-level Lemma 2, cost version: every target cost between zero and the
total cost mass is exactly achieved by an endpoint-aware score-threshold policy.
-/
theorem exists_extendedScoreThresholdPolicy_expectedCost_eq
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    {target : ℝ}
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total :
      target ≤ D.costScoreMeasure.real (Set.univ : Set ℝ)) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ policy : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds policy ∧
              policy = D.extendedScoreThresholdPolicy threshold alpha ∧
                D.expectedCost policy = target := by
  rcases D.exists_costScoreMeasure_threshold_attainment
      htarget_nonneg htarget_le_total with
    ⟨threshold, alpha, halpha_nonneg, halpha_le_one, hmass⟩
  refine ⟨threshold, alpha,
    D.extendedScoreThresholdPolicy threshold alpha,
    halpha_nonneg, halpha_le_one, ?_, rfl, ?_⟩
  · exact
      D.extendedScoreThresholdPolicy_bounds threshold alpha
        halpha_nonneg halpha_le_one
  · rw [D.expectedCost_extendedScoreThresholdPolicy_eq hcost_nonneg]
    exact hmass

/--
Measure-level Lemma 2, utility version, applied to an original bounded
measurable allocation policy.
-/
theorem exists_extendedScoreThresholdPolicy_expectedPosteriorUtility_eq_of_policy
    (D : MeasureCostAwareData Applicant Outcome)
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ policy : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds policy ∧
              policy = D.extendedScoreThresholdPolicy threshold alpha ∧
                D.expectedPosteriorUtility policy =
                  D.expectedPosteriorUtility original := by
  exact D.exists_extendedScoreThresholdPolicy_expectedPosteriorUtility_eq
    hutility_nonneg
    (D.expectedPosteriorUtility_nonneg_of_measurable_bounds
      hutility_nonneg original horiginal_bounds)
    (D.expectedPosteriorUtility_le_utilityScoreMeasure_univ_of_measurable_bounds
      hutility_nonneg original horiginal_meas horiginal_bounds)

/--
Measure-level Lemma 2, cost version, applied to an original bounded measurable
allocation policy.
-/
theorem exists_extendedScoreThresholdPolicy_expectedCost_eq_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_nonneg : ∀ item, 0 ≤ D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ policy : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds policy ∧
              policy = D.extendedScoreThresholdPolicy threshold alpha ∧
                D.expectedCost policy = D.expectedCost original := by
  exact D.exists_extendedScoreThresholdPolicy_expectedCost_eq hcost_nonneg
    (D.expectedCost_nonneg_of_bounds
      original hcost_nonneg horiginal_bounds)
    (D.expectedCost_le_costScoreMeasure_univ_of_measurable_bounds
      original hcost_nonneg horiginal_meas horiginal_bounds)

/--
Measure-level Lemma 2 plus Lemma 1, Case 1: every bounded measurable
allocation has a same-cost endpoint-aware score-threshold replacement with
weakly higher expected posterior utility.
-/
theorem exists_sameCostExtendedScoreThresholdPolicy_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds replacement ∧
              AllocationPolicyMeasurable replacement ∧
                replacement =
                  D.extendedScoreThresholdPolicy threshold alpha ∧
                  D.expectedCost replacement =
                    D.expectedCost original ∧
                    D.expectedPosteriorUtility original ≤
                      D.expectedPosteriorUtility replacement := by
  rcases D.exists_extendedScoreThresholdPolicy_expectedCost_eq_of_policy
      original (fun item => (hcost_pos item).le)
      horiginal_meas horiginal_bounds with
    ⟨threshold, alpha, replacement, halpha_nonneg, halpha_le_one,
      hreplacement_bounds, hreplacement_eq, hcost⟩
  subst replacement
  refine ⟨threshold, alpha, D.extendedScoreThresholdPolicy threshold alpha,
    halpha_nonneg, halpha_le_one, ?_, ?_, rfl, hcost, ?_⟩
  · exact D.extendedScoreThresholdPolicy_bounds
      threshold alpha halpha_nonneg halpha_le_one
  · exact D.extendedScoreThresholdPolicy_measurable threshold alpha
  · exact
      D.extendedScoreThresholdPolicy_expectedPosteriorUtility_ge_of_expectedCost_eq
        hcost_pos threshold alpha halpha_nonneg halpha_le_one
        original horiginal_meas horiginal_bounds hcost

/--
Certificate form of the measure-level same-cost threshold replacement.
-/
structure SameCostExtendedScoreThresholdReplacement
    (D : MeasureCostAwareData Applicant Outcome)
    (original : AllocationPolicy Applicant Outcome) where
  threshold : RealThreshold
  alpha : ℝ
  replacement : AllocationPolicy Applicant Outcome
  alpha_nonneg : 0 ≤ alpha
  alpha_le_one : alpha ≤ 1
  replacement_bounds : AllocationPolicyBounds replacement
  replacement_measurable : AllocationPolicyMeasurable replacement
  replacement_eq :
    replacement = D.extendedScoreThresholdPolicy threshold alpha
  same_cost :
    D.expectedCost replacement = D.expectedCost original
  utility_ge :
    D.expectedPosteriorUtility original ≤
      D.expectedPosteriorUtility replacement

/-- Certificate version of `exists_sameCostExtendedScoreThresholdPolicy_of_policy`. -/
theorem exists_sameCostExtendedScoreThresholdReplacement_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    Nonempty (D.SameCostExtendedScoreThresholdReplacement original) := by
  rcases D.exists_sameCostExtendedScoreThresholdPolicy_of_policy
      original hcost_pos horiginal_meas horiginal_bounds with
    ⟨threshold, alpha, replacement, halpha_nonneg, halpha_le_one,
      hreplacement_bounds, hreplacement_measurable, hreplacement_eq,
      hcost, hutility⟩
  exact ⟨{
    threshold := threshold
    alpha := alpha
    replacement := replacement
    alpha_nonneg := halpha_nonneg
    alpha_le_one := halpha_le_one
    replacement_bounds := hreplacement_bounds
    replacement_measurable := hreplacement_measurable
    replacement_eq := hreplacement_eq
    same_cost := hcost
    utility_ge := hutility }⟩

/--
Measure-level Lemma 2 plus Lemma 1, Case 2: every bounded measurable
allocation has a same-utility endpoint-aware score-threshold replacement with
weakly lower expected cost.
-/
theorem exists_sameUtilityExtendedScoreThresholdPolicy_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : RealThreshold,
      ∃ alpha : ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          0 ≤ alpha ∧ alpha ≤ 1 ∧
            AllocationPolicyBounds replacement ∧
              AllocationPolicyMeasurable replacement ∧
                replacement =
                  D.extendedScoreThresholdPolicy threshold alpha ∧
                  D.expectedPosteriorUtility replacement =
                    D.expectedPosteriorUtility original ∧
                    D.expectedCost replacement ≤
                      D.expectedCost original := by
  by_cases hzero : D.expectedPosteriorUtility original = 0
  · rcases D.exists_sameUtilityZeroEndpointThresholdPolicy_of_policy
        original hcost_pos horiginal_bounds hzero with
      ⟨replacement, hbounds, hmeas, hrepl, hutility, hcost⟩
    refine ⟨RealThreshold.posInf, 0, replacement, by norm_num, by norm_num,
      hbounds, hmeas, hrepl, hutility, hcost⟩
  · have hutility_nonneg_total :
        0 ≤ D.expectedPosteriorUtility original :=
      D.expectedPosteriorUtility_nonneg_of_measurable_bounds
        hutility_nonneg original horiginal_bounds
    have hutility_pos : 0 < D.expectedPosteriorUtility original :=
      lt_of_le_of_ne hutility_nonneg_total (Ne.symm hzero)
    have hutility_le_total :
        D.expectedPosteriorUtility original ≤
          D.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
      D.expectedPosteriorUtility_le_utilityScoreMeasure_univ_of_measurable_bounds
        hutility_nonneg original horiginal_meas horiginal_bounds
    by_cases htotal :
        D.expectedPosteriorUtility original =
          D.utilityScoreMeasure.real (Set.univ : Set ℝ)
    · let replacement : AllocationPolicy Applicant Outcome :=
        D.scoreThresholdPolicy 0 0
      have hbounds : AllocationPolicyBounds replacement := by
        simpa [replacement] using
          D.scoreThresholdPolicy_bounds 0 0 (by norm_num) (by norm_num)
      have hmeas : AllocationPolicyMeasurable replacement := by
        simpa [replacement] using D.scoreThresholdPolicy_measurable 0 0
      have hutility :
          D.expectedPosteriorUtility replacement =
            D.expectedPosteriorUtility original := by
        calc
          D.expectedPosteriorUtility replacement =
              D.utilityScoreMeasure.real (Set.univ : Set ℝ) := by
            simpa [replacement] using
              D.expectedPosteriorUtility_scoreThresholdPolicy_zero_zero_eq_univ
                hutility_nonneg hcost_pos
          _ = D.expectedPosteriorUtility original := htotal.symm
      have hcost :
          D.expectedCost replacement ≤ D.expectedCost original := by
        simpa [replacement] using
          D.scoreThresholdPolicy_zero_zero_expectedCost_le_of_expectedPosteriorUtility_eq_univ
            original hutility_nonneg hcost_pos horiginal_meas horiginal_bounds
            htotal
      refine ⟨RealThreshold.finite 0, 0, replacement,
        by norm_num, by norm_num, hbounds, hmeas, ?_, hutility, hcost⟩
      simp [replacement, extendedScoreThresholdPolicy]
    · have hlt_total :
          D.expectedPosteriorUtility original <
            D.utilityScoreMeasure.real (Set.univ : Set ℝ) :=
        lt_of_le_of_ne hutility_le_total htotal
      rcases D.exists_sameUtilityScoreThresholdPolicy_of_policy_of_pos_lt_total
          original hutility_nonneg hcost_pos horiginal_meas horiginal_bounds
          hutility_pos hlt_total with
        ⟨t, alpha, replacement, ht_pos, halpha_nonneg, halpha_le_one,
          hbounds, hmeas, hrepl, hutility, hcost⟩
      refine ⟨RealThreshold.finite t, alpha, replacement,
        halpha_nonneg, halpha_le_one, hbounds, hmeas, ?_, hutility, hcost⟩
      simpa [extendedScoreThresholdPolicy] using hrepl

/-- Certificate form of the measure-level same-utility threshold replacement. -/
structure SameUtilityExtendedScoreThresholdReplacement
    (D : MeasureCostAwareData Applicant Outcome)
    (original : AllocationPolicy Applicant Outcome) where
  threshold : RealThreshold
  alpha : ℝ
  replacement : AllocationPolicy Applicant Outcome
  alpha_nonneg : 0 ≤ alpha
  alpha_le_one : alpha ≤ 1
  replacement_bounds : AllocationPolicyBounds replacement
  replacement_measurable : AllocationPolicyMeasurable replacement
  replacement_eq :
    replacement = D.extendedScoreThresholdPolicy threshold alpha
  same_utility :
    D.expectedPosteriorUtility replacement =
      D.expectedPosteriorUtility original
  cost_le :
    D.expectedCost replacement ≤ D.expectedCost original

/-- Certificate version of `exists_sameUtilityExtendedScoreThresholdPolicy_of_policy`. -/
theorem exists_sameUtilityExtendedScoreThresholdReplacement_of_policy
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    Nonempty (D.SameUtilityExtendedScoreThresholdReplacement original) := by
  rcases D.exists_sameUtilityExtendedScoreThresholdPolicy_of_policy
      original hutility_nonneg hcost_pos horiginal_meas horiginal_bounds with
    ⟨threshold, alpha, replacement, halpha_nonneg, halpha_le_one,
      hbounds, hmeas, hrepl, hutility, hcost⟩
  exact ⟨{
    threshold := threshold
    alpha := alpha
    replacement := replacement
    alpha_nonneg := halpha_nonneg
    alpha_le_one := halpha_le_one
    replacement_bounds := hbounds
    replacement_measurable := hmeas
    replacement_eq := hrepl
    same_utility := hutility
    cost_le := hcost }⟩

/--
Certificate version of the signed nonnegative-target same-utility threshold
replacement.
-/
theorem exists_sameUtilityExtendedScoreThresholdReplacement_of_policy_signed_nonnegative_target
    (D : MeasureCostAwareData Applicant Outcome) [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (htarget_nonneg : 0 ≤ D.expectedPosteriorUtility original) :
    Nonempty (D.SameUtilityExtendedScoreThresholdReplacement original) := by
  rcases
      D.exists_sameUtilityExtendedScoreThresholdPolicy_of_policy_signed_nonnegative_target
        original hcost_pos horiginal_meas horiginal_bounds
        htarget_nonneg with
    ⟨threshold, alpha, replacement, halpha_nonneg, halpha_le_one,
      hbounds, hmeas, hrepl, hutility, hcost⟩
  exact ⟨{
    threshold := threshold
    alpha := alpha
    replacement := replacement
    alpha_nonneg := halpha_nonneg
    alpha_le_one := halpha_le_one
    replacement_bounds := hbounds
    replacement_measurable := hmeas
    replacement_eq := hrepl
    same_utility := hutility
    cost_le := hcost }⟩

end MeasureCostAwareData

/--
Measure-space grouped allocation data for the source-general threshold
replacement theorem.
-/
structure MeasureGroupAllocationData
    (Applicant Outcome Group : Type*) [MeasurableSpace Outcome] extends
    MeasureCostAwareData Applicant Outcome where
  group : Applicant → Group

namespace MeasureGroupAllocationData

variable {Applicant Outcome Group : Type*}
variable [Fintype Applicant] [MeasurableSpace Outcome]

/-- Allocation policies in the measure-space grouped model. -/
abbrev AllocationPolicy (Applicant Outcome : Type*) :=
  MeasureCostAwareData.AllocationPolicy Applicant Outcome

/-- Allocation bounds in the measure-space grouped model. -/
abbrev AllocationPolicyBounds
    {Applicant Outcome : Type*}
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  MeasureCostAwareData.AllocationPolicyBounds policy

/-- Allocation measurability in the measure-space grouped model. -/
abbrev AllocationPolicyMeasurable
    {Applicant Outcome : Type*} [MeasurableSpace Outcome]
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  MeasureCostAwareData.AllocationPolicyMeasurable policy

/-- Expected posterior utility in the measure-space grouped model. -/
noncomputable def expectedPosteriorUtility
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  D.toMeasureCostAwareData.expectedPosteriorUtility policy

/-- Expected allocation cost in the measure-space grouped model. -/
noncomputable def expectedCost
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  D.toMeasureCostAwareData.expectedCost policy

/-- Expected posterior utility contributed by one group. -/
noncomputable def expectedGroupPosteriorUtility [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  ∫ outcome,
    ∑ item : Applicant,
      if D.group item = g then
        policy item outcome * D.posteriorUtility item outcome
      else
        0 ∂D.law

/-- Expected allocation cost contributed by one group. -/
noncomputable def expectedGroupCost [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome) : ℝ :=
  ∫ outcome,
    ∑ item : Applicant,
      if D.group item = g then
        D.allocCost item * policy item outcome
      else
        0 ∂D.law

/-- Cost-aware measure data obtained by restricting to one group. -/
noncomputable def groupMeasureCostAwareData [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group) :
    MeasureCostAwareData {item : Applicant // D.group item = g} Outcome where
  law := D.law
  posteriorUtility item outcome := D.posteriorUtility item.1 outcome
  posteriorUtility_measurable item := D.posteriorUtility_measurable item.1
  posteriorUtility_integrable item := D.posteriorUtility_integrable item.1
  allocCost item := D.allocCost item.1

/-- Restrict an allocation policy to one group. -/
noncomputable def restrictPolicy [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome) :
    MeasureCostAwareData.AllocationPolicy
      {item : Applicant // D.group item = g} Outcome :=
  fun item outcome => policy item.1 outcome

/-- Allocation bounds restrict to every group. -/
theorem restrictPolicy_bounds [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy : AllocationPolicyBounds policy) :
    MeasureCostAwareData.AllocationPolicyBounds
      (D.restrictPolicy g policy) := by
  intro item outcome
  exact hpolicy item.1 outcome

/-- Allocation measurability restricts to every group. -/
theorem restrictPolicy_measurable [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy : AllocationPolicyMeasurable policy) :
    MeasureCostAwareData.AllocationPolicyMeasurable
      (D.restrictPolicy g policy) := by
  intro item
  exact hpolicy item.1

/-- A group cost integral is the expected cost of the restricted subproblem. -/
theorem expectedGroupCost_eq_restrictedExpectedCost [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome) :
    D.expectedGroupCost g policy =
      (D.groupMeasureCostAwareData g).expectedCost
        (D.restrictPolicy g policy) := by
  classical
  unfold expectedGroupCost MeasureCostAwareData.expectedCost
    groupMeasureCostAwareData restrictPolicy
  refine integral_congr_ae ?_
  exact ae_of_all D.law fun outcome => by
    calc
      (∑ item : Applicant,
        (if D.group item = g then
          D.allocCost item * policy item outcome
        else
          0))
          =
          ∑ item ∈
            ((Finset.univ : Finset Applicant).filter
              fun item : Applicant => D.group item = g),
            D.allocCost item * policy item outcome := by
        rw [Finset.sum_filter]
      _ =
          ∑ item : {item : Applicant // D.group item = g},
            D.allocCost item.1 * policy item.1 outcome := by
        exact
          Finset.sum_subtype
            ((Finset.univ : Finset Applicant).filter
              fun item : Applicant => D.group item = g)
            (by intro item; simp)
            (fun item : Applicant =>
              D.allocCost item * policy item outcome)

/--
A group posterior-utility integral is the expected posterior utility of the
restricted subproblem.
-/
theorem expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group) (g : Group)
    (policy : AllocationPolicy Applicant Outcome) :
    D.expectedGroupPosteriorUtility g policy =
      (D.groupMeasureCostAwareData g).expectedPosteriorUtility
        (D.restrictPolicy g policy) := by
  classical
  unfold expectedGroupPosteriorUtility
    MeasureCostAwareData.expectedPosteriorUtility
    groupMeasureCostAwareData restrictPolicy
  refine integral_congr_ae ?_
  exact ae_of_all D.law fun outcome => by
    calc
      (∑ item : Applicant,
        (if D.group item = g then
          policy item outcome * D.posteriorUtility item outcome
        else
          0))
          =
          ∑ item ∈
            ((Finset.univ : Finset Applicant).filter
              fun item : Applicant => D.group item = g),
            policy item outcome * D.posteriorUtility item outcome := by
        rw [Finset.sum_filter]
      _ =
          ∑ item : {item : Applicant // D.group item = g},
            policy item.1 outcome * D.posteriorUtility item.1 outcome := by
        exact
          Finset.sum_subtype
            ((Finset.univ : Finset Applicant).filter
              fun item : Applicant => D.group item = g)
            (by intro item; simp)
            (fun item : Applicant =>
              policy item outcome * D.posteriorUtility item outcome)

/-- The groupwise endpoint-aware score-threshold policy from threshold data. -/
noncomputable def groupwiseExtendedScoreThresholdPolicy
    [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (threshold : Group → RealThreshold) (alpha : Group → ℝ) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome =>
    (D.groupMeasureCostAwareData (D.group item)).extendedScoreThresholdPolicy
      (threshold (D.group item)) (alpha (D.group item)) ⟨item, rfl⟩ outcome

/--
Recombine one same-cost measure-threshold replacement per group into a full
allocation policy.
-/
noncomputable def groupwiseSameCostExtendedScoreThresholdPolicy
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original))) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome => (R (D.group item)).replacement ⟨item, rfl⟩ outcome

/-- Restricting the recombined policy recovers that group's replacement. -/
theorem restrict_groupwiseSameCostExtendedScoreThresholdPolicy
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.restrictPolicy g
        (D.groupwiseSameCostExtendedScoreThresholdPolicy original R) =
      (R g).replacement := by
  funext item outcome
  rcases item with ⟨item, hitem⟩
  cases hitem
  rfl

/-- The recombined same-cost replacement preserves each group's cost. -/
theorem groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupCost_eq
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupCost g
        (D.groupwiseSameCostExtendedScoreThresholdPolicy original R) =
      D.expectedGroupCost g original := by
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g
    (D.groupwiseSameCostExtendedScoreThresholdPolicy original R)]
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g original]
  rw [D.restrict_groupwiseSameCostExtendedScoreThresholdPolicy original R g]
  exact (R g).same_cost

/--
The recombined same-cost replacement weakly improves each group's expected
posterior utility.
-/
theorem groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupUtility_ge
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupPosteriorUtility g original ≤
      D.expectedGroupPosteriorUtility g
        (D.groupwiseSameCostExtendedScoreThresholdPolicy original R) := by
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g original]
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g (D.groupwiseSameCostExtendedScoreThresholdPolicy original R)]
  rw [D.restrict_groupwiseSameCostExtendedScoreThresholdPolicy original R g]
  exact (R g).utility_ge

/--
Measure-level groupwise same-cost replacement existence: applying the
single-group measure Lemma 2 + Lemma 1 bridge separately to each group yields a
recombined policy with identical group costs and weakly higher group utilities.
-/
theorem exists_groupwiseSameCostExtendedScoreThresholdPolicy
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ replacement : AllocationPolicy Applicant Outcome,
      AllocationPolicyBounds replacement ∧
        AllocationPolicyMeasurable replacement ∧
          (∀ g, D.expectedGroupCost g replacement =
            D.expectedGroupCost g original) ∧
            (∀ g,
              D.expectedGroupPosteriorUtility g original ≤
                D.expectedGroupPosteriorUtility g replacement) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)) := fun g => by
    letI : IsFiniteMeasure (D.groupMeasureCostAwareData g).law := by
      dsimp [groupMeasureCostAwareData]
      infer_instance
    exact Classical.choice
      ((D.groupMeasureCostAwareData g).exists_sameCostExtendedScoreThresholdReplacement_of_policy
        (D.restrictPolicy g original)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_measurable g original horiginal_meas)
        (D.restrictPolicy_bounds g original horiginal_bounds))
  let replacement : AllocationPolicy Applicant Outcome :=
    D.groupwiseSameCostExtendedScoreThresholdPolicy original R
  refine ⟨replacement, ?_, ?_, ?_, ?_⟩
  · intro item outcome
    exact (R (D.group item)).replacement_bounds ⟨item, rfl⟩ outcome
  · intro item
    exact (R (D.group item)).replacement_measurable ⟨item, rfl⟩
  · intro g
    exact
      D.groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupCost_eq
        original R g
  · intro g
    exact
      D.groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupUtility_ge
        original R g

/--
Measure-level groupwise same-cost replacement with explicit threshold
witnesses.
-/
theorem exists_groupwiseSameCostExtendedScoreThresholdPolicy_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              AllocationPolicyBounds replacement ∧
                AllocationPolicyMeasurable replacement ∧
                  (∀ g, D.expectedGroupCost g replacement =
                    D.expectedGroupCost g original) ∧
                    (∀ g,
                      D.expectedGroupPosteriorUtility g original ≤
                        D.expectedGroupPosteriorUtility g replacement) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameCostExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)) := fun g => by
    letI : IsFiniteMeasure (D.groupMeasureCostAwareData g).law := by
      dsimp [groupMeasureCostAwareData]
      infer_instance
    exact Classical.choice
      ((D.groupMeasureCostAwareData g).exists_sameCostExtendedScoreThresholdReplacement_of_policy
        (D.restrictPolicy g original)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_measurable g original horiginal_meas)
        (D.restrictPolicy_bounds g original horiginal_bounds))
  let threshold : Group → RealThreshold := fun g => (R g).threshold
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant Outcome :=
    D.groupwiseSameCostExtendedScoreThresholdPolicy original R
  refine ⟨threshold, alpha, replacement, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact ⟨(R g).alpha_nonneg, (R g).alpha_le_one⟩
  · funext item outcome
    change (R (D.group item)).replacement ⟨item, rfl⟩ outcome =
      ((D.groupMeasureCostAwareData (D.group item)).extendedScoreThresholdPolicy
        (R (D.group item)).threshold (R (D.group item)).alpha)
          ⟨item, rfl⟩ outcome
    rw [(R (D.group item)).replacement_eq]
  · intro item outcome
    exact (R (D.group item)).replacement_bounds ⟨item, rfl⟩ outcome
  · intro item
    exact (R (D.group item)).replacement_measurable ⟨item, rfl⟩
  · intro g
    exact
      D.groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupCost_eq
        original R g
  · intro g
    exact
      D.groupwiseSameCostExtendedScoreThresholdPolicy_expectedGroupUtility_ge
        original R g

/--
Recombine one same-utility measure-threshold replacement per group into a full
allocation policy.
-/
noncomputable def groupwiseSameUtilityExtendedScoreThresholdPolicy
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original))) :
    AllocationPolicy Applicant Outcome :=
  fun item outcome => (R (D.group item)).replacement ⟨item, rfl⟩ outcome

/-- Restricting the recombined same-utility policy recovers that group. -/
theorem restrict_groupwiseSameUtilityExtendedScoreThresholdPolicy
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.restrictPolicy g
        (D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R) =
      (R g).replacement := by
  funext item outcome
  rcases item with ⟨item, hitem⟩
  cases hitem
  rfl

/-- The recombined same-utility replacement preserves each group's utility. -/
theorem groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupUtility_eq
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupPosteriorUtility g
        (D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R) =
      D.expectedGroupPosteriorUtility g original := by
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g (D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R)]
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g original]
  rw [D.restrict_groupwiseSameUtilityExtendedScoreThresholdPolicy original R g]
  exact (R g).same_utility

/-- The recombined same-utility replacement weakly lowers each group's cost. -/
theorem groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupCost_le
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (original : AllocationPolicy Applicant Outcome)
    (R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupCost g
        (D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R) ≤
      D.expectedGroupCost g original := by
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g
    (D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R)]
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g original]
  rw [D.restrict_groupwiseSameUtilityExtendedScoreThresholdPolicy original R g]
  exact (R g).cost_le

/--
Measure-level groupwise same-utility replacement existence, used for the
equality-diversity variant.
-/
theorem exists_groupwiseSameUtilityExtendedScoreThresholdPolicy
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ replacement : AllocationPolicy Applicant Outcome,
      AllocationPolicyBounds replacement ∧
        AllocationPolicyMeasurable replacement ∧
          (∀ g,
            D.expectedGroupPosteriorUtility g replacement =
              D.expectedGroupPosteriorUtility g original) ∧
            (∀ g,
              D.expectedGroupCost g replacement ≤
                D.expectedGroupCost g original) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)) := fun g => by
    letI : IsFiniteMeasure (D.groupMeasureCostAwareData g).law := by
      dsimp [groupMeasureCostAwareData]
      infer_instance
    exact Classical.choice
      ((D.groupMeasureCostAwareData g).exists_sameUtilityExtendedScoreThresholdReplacement_of_policy
        (D.restrictPolicy g original)
        (fun item => hutility_nonneg item.1)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_measurable g original horiginal_meas)
        (D.restrictPolicy_bounds g original horiginal_bounds))
  let replacement : AllocationPolicy Applicant Outcome :=
    D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R
  refine ⟨replacement, ?_, ?_, ?_, ?_⟩
  · intro item outcome
    exact (R (D.group item)).replacement_bounds ⟨item, rfl⟩ outcome
  · intro item
    exact (R (D.group item)).replacement_measurable ⟨item, rfl⟩
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupUtility_eq
        original R g
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupCost_le
        original R g

/--
Measure-level groupwise same-utility replacement with explicit threshold
witnesses, used for the equality-diversity variant.
-/
theorem exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              AllocationPolicyBounds replacement ∧
                AllocationPolicyMeasurable replacement ∧
                  (∀ g,
                    D.expectedGroupPosteriorUtility g replacement =
                      D.expectedGroupPosteriorUtility g original) ∧
                    (∀ g,
                      D.expectedGroupCost g replacement ≤
                        D.expectedGroupCost g original) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)) := fun g => by
    letI : IsFiniteMeasure (D.groupMeasureCostAwareData g).law := by
      dsimp [groupMeasureCostAwareData]
      infer_instance
    exact Classical.choice
      ((D.groupMeasureCostAwareData g).exists_sameUtilityExtendedScoreThresholdReplacement_of_policy
        (D.restrictPolicy g original)
        (fun item => hutility_nonneg item.1)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_measurable g original horiginal_meas)
        (D.restrictPolicy_bounds g original horiginal_bounds))
  let threshold : Group → RealThreshold := fun g => (R g).threshold
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant Outcome :=
    D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R
  refine ⟨threshold, alpha, replacement, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact ⟨(R g).alpha_nonneg, (R g).alpha_le_one⟩
  · funext item outcome
    change (R (D.group item)).replacement ⟨item, rfl⟩ outcome =
      ((D.groupMeasureCostAwareData (D.group item)).extendedScoreThresholdPolicy
        (R (D.group item)).threshold (R (D.group item)).alpha)
          ⟨item, rfl⟩ outcome
    rw [(R (D.group item)).replacement_eq]
  · intro item outcome
    exact (R (D.group item)).replacement_bounds ⟨item, rfl⟩ outcome
  · intro item
    exact (R (D.group item)).replacement_measurable ⟨item, rfl⟩
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupUtility_eq
        original R g
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupCost_le
        original R g

/--
Measure-level groupwise same-utility replacement with explicit threshold
witnesses for signed utilities and nonnegative group targets.
-/
theorem exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness_signed_nonnegative_targets
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (original : AllocationPolicy Applicant Outcome)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (htarget_nonneg :
      ∀ g : Group, 0 ≤ D.expectedGroupPosteriorUtility g original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              AllocationPolicyBounds replacement ∧
                AllocationPolicyMeasurable replacement ∧
                  (∀ g,
                    D.expectedGroupPosteriorUtility g replacement =
                      D.expectedGroupPosteriorUtility g original) ∧
                    (∀ g,
                      D.expectedGroupCost g replacement ≤
                        D.expectedGroupCost g original) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupMeasureCostAwareData g).SameUtilityExtendedScoreThresholdReplacement
          (D.restrictPolicy g original)) := fun g => by
    letI : IsFiniteMeasure (D.groupMeasureCostAwareData g).law := by
      dsimp [groupMeasureCostAwareData]
      infer_instance
    exact Classical.choice
      ((D.groupMeasureCostAwareData g).exists_sameUtilityExtendedScoreThresholdReplacement_of_policy_signed_nonnegative_target
        (D.restrictPolicy g original)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_measurable g original horiginal_meas)
        (D.restrictPolicy_bounds g original horiginal_bounds)
        (by
          rw [← D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
            g original]
          exact htarget_nonneg g))
  let threshold : Group → RealThreshold := fun g => (R g).threshold
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant Outcome :=
    D.groupwiseSameUtilityExtendedScoreThresholdPolicy original R
  refine ⟨threshold, alpha, replacement, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact ⟨(R g).alpha_nonneg, (R g).alpha_le_one⟩
  · funext item outcome
    change (R (D.group item)).replacement ⟨item, rfl⟩ outcome =
      ((D.groupMeasureCostAwareData (D.group item)).extendedScoreThresholdPolicy
        (R (D.group item)).threshold (R (D.group item)).alpha)
          ⟨item, rfl⟩ outcome
    rw [(R (D.group item)).replacement_eq]
  · intro item outcome
    exact (R (D.group item)).replacement_bounds ⟨item, rfl⟩ outcome
  · intro item
    exact (R (D.group item)).replacement_measurable ⟨item, rfl⟩
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupUtility_eq
        original R g
  · intro g
    exact
      D.groupwiseSameUtilityExtendedScoreThresholdPolicy_expectedGroupCost_le
        original R g

/-- Feasibility for the source allocation constraints: budget and diversity. -/
def Feasible [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.expectedCost policy ≤ budget ∧
    ∀ g, diversityTarget g ≤ D.expectedGroupPosteriorUtility g policy

/-- Optimality for the measure-space grouped allocation subproblem. -/
def Optimal [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.Feasible budget diversityTarget policy ∧
    ∀ other,
      D.Feasible budget diversityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Feasibility for equality diversity constraints. -/
def EqualityFeasible [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.expectedCost policy ≤ budget ∧
    ∀ g, D.expectedGroupPosteriorUtility g policy = equalityTarget g

/-- Optimality for the equality diversity variant. -/
def EqualityOptimal [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.EqualityFeasible budget equalityTarget policy ∧
    ∀ other,
      D.EqualityFeasible budget equalityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/--
Source allocation feasibility, including the paper's allocation-policy domain:
every allocation is a measurable probability in `[0,1]`.
-/
def SourceFeasible [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  AllocationPolicyBounds policy ∧
    AllocationPolicyMeasurable policy ∧
      D.expectedCost policy ≤ budget ∧
        ∀ g, diversityTarget g ≤ D.expectedGroupPosteriorUtility g policy

/-- Optimality over the source allocation-policy domain. -/
def SourceOptimal [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.SourceFeasible budget diversityTarget policy ∧
    ∀ other,
      D.SourceFeasible budget diversityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Source equality-diversity feasibility over admissible allocations. -/
def SourceEqualityFeasible [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  AllocationPolicyBounds policy ∧
    AllocationPolicyMeasurable policy ∧
      D.expectedCost policy ≤ budget ∧
        ∀ g, D.expectedGroupPosteriorUtility g policy = equalityTarget g

/-- Equality-diversity optimality over the source allocation-policy domain. -/
def SourceEqualityOptimal [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant Outcome) : Prop :=
  D.SourceEqualityFeasible budget equalityTarget policy ∧
    ∀ other,
      D.SourceEqualityFeasible budget equalityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Total expected utility is the sum of group expected utilities. -/
theorem sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
    [Fintype Group] [DecidableEq Group]
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    ∑ g : Group, D.expectedGroupPosteriorUtility g policy =
      D.expectedPosteriorUtility policy := by
  classical
  unfold expectedGroupPosteriorUtility expectedPosteriorUtility
    MeasureCostAwareData.expectedPosteriorUtility
  rw [← MeasureTheory.integral_finset_sum (Finset.univ : Finset Group)]
  · refine integral_congr_ae ?_
    exact ae_of_all D.law fun outcome => by
      calc
        ∑ g : Group,
            ∑ item : Applicant,
              (if D.group item = g then
                policy item outcome * D.posteriorUtility item outcome
              else
                0)
            =
            ∑ item : Applicant,
              ∑ g : Group,
                (if D.group item = g then
                  policy item outcome * D.posteriorUtility item outcome
                else
                  0) := by
          rw [Finset.sum_comm]
        _ =
            ∑ item : Applicant,
              policy item outcome * D.posteriorUtility item outcome := by
          refine Finset.sum_congr rfl ?_
          intro item _
          simp
  · intro g _
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ => by
        by_cases hg : D.group item = g
        · simpa [hg] using
            D.toMeasureCostAwareData.policy_mul_posteriorUtility_integrable
              policy hpolicy_meas hpolicy_bounds item
        · simp [hg])

/-- Total expected cost is the sum of group expected costs. -/
theorem sum_expectedGroupCost_eq_expectedCost
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (policy : AllocationPolicy Applicant Outcome)
    (hpolicy_meas : AllocationPolicyMeasurable policy)
    (hpolicy_bounds : AllocationPolicyBounds policy) :
    ∑ g : Group, D.expectedGroupCost g policy = D.expectedCost policy := by
  classical
  unfold expectedGroupCost expectedCost MeasureCostAwareData.expectedCost
  rw [← MeasureTheory.integral_finset_sum (Finset.univ : Finset Group)]
  · refine integral_congr_ae ?_
    exact ae_of_all D.law fun outcome => by
      calc
        ∑ g : Group,
            ∑ item : Applicant,
              (if D.group item = g then
                D.allocCost item * policy item outcome
              else
                0)
            =
            ∑ item : Applicant,
              ∑ g : Group,
                (if D.group item = g then
                  D.allocCost item * policy item outcome
                else
                  0) := by
          rw [Finset.sum_comm]
        _ =
            ∑ item : Applicant,
              D.allocCost item * policy item outcome := by
          refine Finset.sum_congr rfl ?_
          intro item _
          simp
  · intro g _
    exact MeasureTheory.integrable_finset_sum Finset.univ
      (fun item _ => by
        by_cases hg : D.group item = g
        · simpa [hg] using
            D.toMeasureCostAwareData.allocCost_mul_policy_integrable
              policy hpolicy_meas hpolicy_bounds item
        · simp [hg])

/--
Groupwise equal-cost, weakly utility-improving replacement preserves optimality
over the paper's admissible allocation policies.
-/
theorem sourceOptimal_of_groupwise_replacement_improves_constraints
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant Outcome)
    (horiginal : D.SourceOptimal budget diversityTarget original)
    (hreplacement_bounds : AllocationPolicyBounds replacement)
    (hreplacement_meas : AllocationPolicyMeasurable replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement) :
    D.SourceOptimal budget diversityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement = D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupCost_eq_expectedCost
        original horiginal.1.2.1 horiginal.1.1]
    exact Finset.sum_congr rfl (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original horiginal.1.2.1 horiginal.1.1,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement hreplacement_meas hreplacement_bounds]
    exact Finset.sum_le_sum (fun g _ => hgroup g)
  constructor
  · exact ⟨hreplacement_bounds, hreplacement_meas,
      hcost_total.le.trans horiginal.1.2.2.1,
      fun g => (horiginal.1.2.2.2 g).trans (hgroup g)⟩
  · intro other hother
    exact (horiginal.2 other hother).trans hutility_total

/--
Groupwise same-utility, weakly lower-cost replacement preserves equality
optimality over the paper's admissible allocation policies.
-/
theorem sourceEqualityOptimal_of_groupwise_sameUtility_replacement
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant Outcome)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hreplacement_bounds : AllocationPolicyBounds replacement)
    (hreplacement_meas : AllocationPolicyMeasurable replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) :
    D.SourceEqualityOptimal budget equalityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement ≤ D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupCost_eq_expectedCost
        original horiginal.1.2.1 horiginal.1.1]
    exact Finset.sum_le_sum (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility replacement =
        D.expectedPosteriorUtility original := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original horiginal.1.2.1 horiginal.1.1]
    exact Finset.sum_congr rfl (fun g _ => hgroup g)
  constructor
  · exact ⟨hreplacement_bounds, hreplacement_meas,
      hcost_total.trans horiginal.1.2.2.1,
      fun g => (hgroup g).trans (horiginal.1.2.2.2 g)⟩
  · intro other hother
    exact (horiginal.2 other hother).trans_eq hutility_total.symm

/-- Assembly step for measure-space groupwise replacement facts. -/
theorem optimal_of_groupwise_replacement_improves_constraints
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant Outcome)
    (horiginal : D.Optimal budget diversityTarget original)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (hreplacement_meas : AllocationPolicyMeasurable replacement)
    (hreplacement_bounds : AllocationPolicyBounds replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement) :
    D.Optimal budget diversityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement = D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupCost_eq_expectedCost
        original horiginal_meas horiginal_bounds]
    exact Finset.sum_congr rfl (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original horiginal_meas horiginal_bounds,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement hreplacement_meas hreplacement_bounds]
    exact Finset.sum_le_sum (fun g _ => hgroup g)
  constructor
  · constructor
    · exact hcost_total.le.trans horiginal.1.1
    · intro g
      exact (horiginal.1.2 g).trans (hgroup g)
  · intro other hother
    exact (horiginal.2 other hother).trans hutility_total

/--
Equality-diversity assembly from per-group same-utility replacement facts.
-/
theorem equalityOptimal_of_groupwise_sameUtility_replacement
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant Outcome)
    (horiginal : D.EqualityOptimal budget equalityTarget original)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original)
    (hreplacement_meas : AllocationPolicyMeasurable replacement)
    (hreplacement_bounds : AllocationPolicyBounds replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) :
    D.EqualityOptimal budget equalityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement ≤ D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupCost_eq_expectedCost
        original horiginal_meas horiginal_bounds]
    exact Finset.sum_le_sum (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility replacement =
        D.expectedPosteriorUtility original := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement hreplacement_meas hreplacement_bounds,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original horiginal_meas horiginal_bounds]
    exact Finset.sum_congr rfl (fun g _ => hgroup g)
  constructor
  · constructor
    · exact hcost_total.trans horiginal.1.1
    · intro g
      rw [hgroup g]
      exact horiginal.1.2 g
  · intro other hother
    exact (horiginal.2 other hother).trans_eq hutility_total.symm

/--
Measure-level source-general Theorem 1 allocation step: an optimal allocation
can be replaced by a groupwise endpoint-aware score-threshold allocation.
-/
theorem exists_optimal_groupwise_threshold_replacement
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.Optimal budget diversityTarget original)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ replacement : AllocationPolicy Applicant Outcome,
      D.Optimal budget diversityTarget replacement := by
  rcases D.exists_groupwiseSameCostExtendedScoreThresholdPolicy
      original hcost_pos horiginal_meas horiginal_bounds with
    ⟨replacement, hreplacement_bounds, hreplacement_meas, hcost, hgroup⟩
  exact ⟨replacement,
    D.optimal_of_groupwise_replacement_improves_constraints
      budget diversityTarget original replacement horiginal
      horiginal_meas horiginal_bounds hreplacement_meas hreplacement_bounds
      hcost hgroup⟩

/--
Measure-level source-general Theorem 1 allocation step with explicit
group-threshold witnesses.
-/
theorem exists_optimal_groupwise_threshold_replacement_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.Optimal budget diversityTarget original)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              D.Optimal budget diversityTarget replacement := by
  rcases D.exists_groupwiseSameCostExtendedScoreThresholdPolicy_with_witness
      original hcost_pos horiginal_meas horiginal_bounds with
    ⟨threshold, alpha, replacement, halpha, hreplacement_eq,
      hreplacement_bounds, hreplacement_meas, hcost, hgroup⟩
  refine ⟨threshold, alpha, replacement, halpha, hreplacement_eq, ?_⟩
  exact
    D.optimal_of_groupwise_replacement_improves_constraints
      budget diversityTarget original replacement horiginal
      horiginal_meas horiginal_bounds hreplacement_meas hreplacement_bounds
      hcost hgroup

/--
Measure-level source-general Lemma 3 allocation step: under equality diversity
constraints, an optimal allocation can be replaced by a groupwise
endpoint-aware score-threshold allocation.
-/
theorem exists_equalityOptimal_groupwise_threshold_replacement
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.EqualityOptimal budget equalityTarget original)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ replacement : AllocationPolicy Applicant Outcome,
      D.EqualityOptimal budget equalityTarget replacement := by
  rcases D.exists_groupwiseSameUtilityExtendedScoreThresholdPolicy
      original hutility_nonneg hcost_pos horiginal_meas horiginal_bounds with
    ⟨replacement, hreplacement_bounds, hreplacement_meas, hgroup, hcost⟩
  exact ⟨replacement,
    D.equalityOptimal_of_groupwise_sameUtility_replacement
      budget equalityTarget original replacement horiginal
      horiginal_meas horiginal_bounds hreplacement_meas hreplacement_bounds
      hcost hgroup⟩

/--
Measure-level source-general Lemma 3 allocation step with explicit
group-threshold witnesses.
-/
theorem exists_equalityOptimal_groupwise_threshold_replacement_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.EqualityOptimal budget equalityTarget original)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal_meas : AllocationPolicyMeasurable original)
    (horiginal_bounds : AllocationPolicyBounds original) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              D.EqualityOptimal budget equalityTarget replacement := by
  rcases D.exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness
      original hutility_nonneg hcost_pos horiginal_meas horiginal_bounds with
    ⟨threshold, alpha, replacement, halpha, hreplacement_eq,
      hreplacement_bounds, hreplacement_meas, hgroup, hcost⟩
  refine ⟨threshold, alpha, replacement, halpha, hreplacement_eq, ?_⟩
  exact
    D.equalityOptimal_of_groupwise_sameUtility_replacement
      budget equalityTarget original replacement horiginal
      horiginal_meas horiginal_bounds hreplacement_meas hreplacement_bounds
      hcost hgroup

/--
Source-faithful Theorem 1 allocation step.  Admissibility is internal to the
optimality predicate, and posterior utilities may be signed.
-/
theorem exists_sourceOptimal_groupwise_threshold_replacement_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.SourceOptimal budget diversityTarget original)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              D.SourceOptimal budget diversityTarget replacement := by
  rcases D.exists_groupwiseSameCostExtendedScoreThresholdPolicy_with_witness
      original hcost_pos horiginal.1.2.1 horiginal.1.1 with
    ⟨threshold, alpha, replacement, halpha, hreplacement_eq,
      hreplacement_bounds, hreplacement_meas, hcost, hgroup⟩
  refine ⟨threshold, alpha, replacement, halpha, hreplacement_eq, ?_⟩
  exact D.sourceOptimal_of_groupwise_replacement_improves_constraints
    budget diversityTarget original replacement horiginal
    hreplacement_bounds hreplacement_meas hcost hgroup

/--
Legacy nonnegative-posterior equality-diversity replacement.  The signed
source-facing endpoint below should be used when the paper only assumes
nonnegative equality targets.
-/
theorem exists_sourceEqualityOptimal_groupwise_threshold_replacement_with_witness
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hutility_nonneg : ∀ item, 0 ≤ᵐ[D.law] D.posteriorUtility item)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              D.SourceEqualityOptimal budget equalityTarget replacement := by
  rcases D.exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness
      original hutility_nonneg hcost_pos horiginal.1.2.1 horiginal.1.1 with
    ⟨threshold, alpha, replacement, halpha, hreplacement_eq,
      hreplacement_bounds, hreplacement_meas, hgroup, hcost⟩
  refine ⟨threshold, alpha, replacement, halpha, hreplacement_eq, ?_⟩
  exact D.sourceEqualityOptimal_of_groupwise_sameUtility_replacement
    budget equalityTarget original replacement horiginal
    hreplacement_bounds hreplacement_meas hcost hgroup

/--
Source-faithful equality-diversity replacement for signed utilities with
nonnegative equality targets.
-/
theorem exists_sourceEqualityOptimal_groupwise_threshold_replacement_with_witness_signed_nonnegative_targets
    (D : MeasureGroupAllocationData Applicant Outcome Group)
    [Fintype Group] [DecidableEq Group] [IsFiniteMeasure D.law]
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant Outcome)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold : Group → RealThreshold,
      ∃ alpha : Group → ℝ,
        ∃ replacement : AllocationPolicy Applicant Outcome,
          (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
            replacement =
              D.groupwiseExtendedScoreThresholdPolicy threshold alpha ∧
              D.SourceEqualityOptimal budget equalityTarget replacement := by
  have htarget_nonneg :
      ∀ g : Group, 0 ≤ D.expectedGroupPosteriorUtility g original := by
    intro g
    rw [horiginal.1.2.2.2 g]
    exact hequalityTarget_nonneg g
  rcases
      D.exists_groupwiseSameUtilityExtendedScoreThresholdPolicy_with_witness_signed_nonnegative_targets
        original hcost_pos horiginal.1.2.1 horiginal.1.1
        htarget_nonneg with
    ⟨threshold, alpha, replacement, halpha, hreplacement_eq,
      hreplacement_bounds, hreplacement_meas, hgroup, hcost⟩
  refine ⟨threshold, alpha, replacement, halpha, hreplacement_eq, ?_⟩
  exact D.sourceEqualityOptimal_of_groupwise_sameUtility_replacement
    budget equalityTarget original replacement horiginal
    hreplacement_bounds hreplacement_meas hcost hgroup

end MeasureGroupAllocationData

/--
Finite-state grouped allocation data for the main threshold-replacement
theorem.  This extends the single-group cost-aware data with a group label for
each applicant.
-/
structure GroupAllocationData (Applicant State Group : Type*) extends
    CostAwareThresholdData Applicant State where
  group : Applicant → Group

namespace GroupAllocationData

variable {Applicant State Group : Type*} [Fintype Applicant] [Fintype State]

/-- Allocation policies in the grouped model. -/
abbrev AllocationPolicy (Applicant State : Type*) :=
  CostAwareThresholdData.AllocationPolicy Applicant State

/-- Expected posterior utility in the grouped model. -/
noncomputable def expectedPosteriorUtility
    (D : GroupAllocationData Applicant State Group)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  D.toCostAwareThresholdData.expectedPosteriorUtility policy

/-- Expected cost in the grouped model. -/
noncomputable def expectedCost
    (D : GroupAllocationData Applicant State Group)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  D.toCostAwareThresholdData.expectedCost policy

/-- Expected posterior utility contributed by one group. -/
noncomputable def expectedGroupPosteriorUtility [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.group item = g then
          policy item state * D.posteriorUtility item state
        else
          0

/-- Expected allocation cost contributed by one group. -/
noncomputable def expectedGroupCost [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State) : ℝ :=
  ∑ state : State,
    D.weight state *
      ∑ item : Applicant,
        if D.group item = g then
          D.allocCost item * policy item state
        else
          0

/-- Cost-aware single-group data obtained by restricting to one group. -/
noncomputable def groupCostAwareData [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group) :
    CostAwareThresholdData {item : Applicant // D.group item = g} State where
  weight := D.weight
  posteriorUtility item state := D.posteriorUtility item.1 state
  allocCost item := D.allocCost item.1

/-- Restrict an allocation policy to a single group. -/
noncomputable def restrictPolicy [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State) :
    CostAwareThresholdData.AllocationPolicy
      {item : Applicant // D.group item = g} State :=
  fun item state => policy item.1 state

/-- Allocation bounds restrict to every group. -/
theorem restrictPolicy_bounds [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State)
    (hpolicy : CostAwareThresholdData.AllocationPolicyBounds policy) :
    CostAwareThresholdData.AllocationPolicyBounds
      (D.restrictPolicy g policy) := by
  intro item state
  exact hpolicy item.1 state

/-- A group cost sum is the expected cost of the restricted subproblem. -/
theorem expectedGroupCost_eq_restrictedExpectedCost [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State) :
    D.expectedGroupCost g policy =
      (D.groupCostAwareData g).expectedCost
        (D.restrictPolicy g policy) := by
  classical
  simp only [expectedGroupCost, CostAwareThresholdData.expectedCost,
    groupCostAwareData, restrictPolicy]
  refine Finset.sum_congr rfl ?_
  intro state _
  congr 1
  calc
    (∑ item : Applicant,
      (if D.group item = g then D.allocCost item * policy item state else 0))
        =
        ∑ item ∈ (Finset.univ.filter fun item : Applicant => D.group item = g),
          D.allocCost item * policy item state := by
      rw [Finset.sum_filter]
    _ =
        ∑ item : {item : Applicant // D.group item = g},
          D.allocCost item.1 * policy item.1 state := by
      exact
        Finset.sum_subtype
          ((Finset.univ : Finset Applicant).filter
            fun item : Applicant => D.group item = g)
          (by intro item; simp)
          (fun item : Applicant => D.allocCost item * policy item state)

/--
A group posterior-utility sum is the expected posterior utility of the
restricted subproblem.
-/
theorem expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group) (g : Group)
    (policy : AllocationPolicy Applicant State) :
    D.expectedGroupPosteriorUtility g policy =
      (D.groupCostAwareData g).expectedPosteriorUtility
        (D.restrictPolicy g policy) := by
  classical
  simp only [expectedGroupPosteriorUtility,
    CostAwareThresholdData.expectedPosteriorUtility, groupCostAwareData,
    restrictPolicy]
  refine Finset.sum_congr rfl ?_
  intro state _
  congr 1
  calc
    (∑ item : Applicant,
      (if D.group item = g then
        policy item state * D.posteriorUtility item state
      else
        0))
        =
        ∑ item ∈ (Finset.univ.filter fun item : Applicant => D.group item = g),
          policy item state * D.posteriorUtility item state := by
      rw [Finset.sum_filter]
    _ =
        ∑ item : {item : Applicant // D.group item = g},
          policy item.1 state * D.posteriorUtility item.1 state := by
      exact
        Finset.sum_subtype
          ((Finset.univ : Finset Applicant).filter
            fun item : Applicant => D.group item = g)
          (by intro item; simp)
          (fun item : Applicant => policy item state * D.posteriorUtility item state)

/--
Recombine one same-cost single-group threshold replacement per group into a
full allocation policy.
-/
noncomputable def groupwiseSameCostThresholdReplacementPolicy
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original))) :
    AllocationPolicy Applicant State :=
  fun item state => (R (D.group item)).threshold ⟨item, rfl⟩ state

/-- Restricting the recombined policy to a group recovers that group's policy. -/
theorem restrict_groupwiseSameCostThresholdReplacementPolicy
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.restrictPolicy g
        (D.groupwiseSameCostThresholdReplacementPolicy original R) =
      (R g).threshold := by
  funext item state
  rcases item with ⟨item, hitem⟩
  cases hitem
  rfl

/-- The recombined same-cost groupwise replacement preserves each group cost. -/
theorem groupwiseSameCostThresholdReplacementPolicy_expectedGroupCost_eq
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupCost g
        (D.groupwiseSameCostThresholdReplacementPolicy original R) =
      D.expectedGroupCost g original := by
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g
    (D.groupwiseSameCostThresholdReplacementPolicy original R)]
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g original]
  rw [D.restrict_groupwiseSameCostThresholdReplacementPolicy original R g]
  exact (R g).same_cost

/--
The recombined same-cost groupwise replacement weakly improves every group's
expected posterior utility.
-/
theorem groupwiseSameCostThresholdReplacementPolicy_expectedGroupUtility_ge
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original)))
    (hweight : ∀ state, 0 ≤ D.weight state)
    (horiginal : CostAwareThresholdData.AllocationPolicyBounds original)
    (g : Group) :
    D.expectedGroupPosteriorUtility g original ≤
      D.expectedGroupPosteriorUtility g
        (D.groupwiseSameCostThresholdReplacementPolicy original R) := by
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g original]
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g (D.groupwiseSameCostThresholdReplacementPolicy original R)]
  rw [D.restrict_groupwiseSameCostThresholdReplacementPolicy original R g]
  exact
    (D.groupCostAwareData g).sameCostThresholdReplacement_expectedPosteriorUtility_ge
      (D.restrictPolicy g original) (R g) hweight
      (D.restrictPolicy_bounds g original horiginal)

/--
Finite-support groupwise replacement existence: applying the finite Lemma 2
cost-attainment theorem separately to each group yields a recombined policy
with identical group costs and weakly higher group utilities.
-/
theorem exists_groupwiseSameCostThresholdReplacementPolicy_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : CostAwareThresholdData.AllocationPolicyBounds original)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).costAtomMass)) :
    ∃ replacement : AllocationPolicy Applicant State,
      (∀ g, D.expectedGroupCost g replacement =
        D.expectedGroupCost g original) ∧
        (∀ g,
          D.expectedGroupPosteriorUtility g original ≤
            D.expectedGroupPosteriorUtility g replacement) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameCostThresholdReplacement_of_finite_positive_costs
        (D.restrictPolicy g original)
        hweight
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_bounds g original horiginal)
        (htotal_pos g))
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameCostThresholdReplacementPolicy original R
  refine ⟨replacement, ?_, ?_⟩
  · intro g
    exact D.groupwiseSameCostThresholdReplacementPolicy_expectedGroupCost_eq
      original R g
  · intro g
    exact D.groupwiseSameCostThresholdReplacementPolicy_expectedGroupUtility_ge
      original R hweight horiginal g

/--
Recombine one same-utility single-group threshold replacement per group into a
full allocation policy.
-/
noncomputable def groupwiseSameUtilityThresholdReplacementPolicy
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original))) :
    AllocationPolicy Applicant State :=
  fun item state => (R (D.group item)).threshold ⟨item, rfl⟩ state

/-- Restricting the recombined same-utility policy recovers the group policy. -/
theorem restrict_groupwiseSameUtilityThresholdReplacementPolicy
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.restrictPolicy g
        (D.groupwiseSameUtilityThresholdReplacementPolicy original R) =
      (R g).threshold := by
  funext item state
  rcases item with ⟨item, hitem⟩
  cases hitem
  rfl

/-- The recombined same-utility groupwise replacement preserves group utility. -/
theorem groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupUtility_eq
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)))
    (g : Group) :
    D.expectedGroupPosteriorUtility g
        (D.groupwiseSameUtilityThresholdReplacementPolicy original R) =
      D.expectedGroupPosteriorUtility g original := by
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g (D.groupwiseSameUtilityThresholdReplacementPolicy original R)]
  rw [D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
    g original]
  rw [D.restrict_groupwiseSameUtilityThresholdReplacementPolicy original R g]
  exact (R g).same_utility

/--
The recombined same-utility groupwise replacement weakly lowers every group's
expected cost.
-/
theorem groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupCost_le
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)))
    (hweight : ∀ state, 0 ≤ D.weight state)
    (horiginal : CostAwareThresholdData.AllocationPolicyBounds original)
    (g : Group) :
    D.expectedGroupCost g
        (D.groupwiseSameUtilityThresholdReplacementPolicy original R) ≤
      D.expectedGroupCost g original := by
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g
    (D.groupwiseSameUtilityThresholdReplacementPolicy original R)]
  rw [D.expectedGroupCost_eq_restrictedExpectedCost g original]
  rw [D.restrict_groupwiseSameUtilityThresholdReplacementPolicy original R g]
  exact
    (D.groupCostAwareData g).sameUtilityThresholdReplacement_expectedCost_le
      (D.restrictPolicy g original) (R g) hweight
      (D.restrictPolicy_bounds g original horiginal)

/--
Finite-support groupwise same-utility replacement existence, used for the
equality-diversity variant.
-/
theorem exists_groupwiseSameUtilityThresholdReplacementPolicy_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : CostAwareThresholdData.AllocationPolicyBounds original)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).utilityAtomMass)) :
    ∃ replacement : AllocationPolicy Applicant State,
      (∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) ∧
        (∀ g,
          D.expectedGroupCost g replacement ≤
            D.expectedGroupCost g original) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameUtilityThresholdReplacement_of_finite_positive_costs
        (D.restrictPolicy g original)
        hweight
        (fun item state => hutility_nonneg item.1 state)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_bounds g original horiginal)
        (htotal_pos g))
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameUtilityThresholdReplacementPolicy original R
  refine ⟨replacement, ?_, ?_⟩
  · intro g
    exact D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupUtility_eq
      original R g
  · intro g
    exact D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupCost_le
      original R hweight horiginal g

/--
Finite-support groupwise same-utility replacement for signed utilities and
nonnegative original group utilities.
-/
theorem exists_groupwiseSameUtilityThresholdReplacementPolicy_of_finite_signed_nonnegative_targets
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (original : AllocationPolicy Applicant State)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (horiginal : CostAwareThresholdData.AllocationPolicyBounds original)
    (htarget_nonneg :
      ∀ g : Group, 0 ≤ D.expectedGroupPosteriorUtility g original) :
    ∃ replacement : AllocationPolicy Applicant State,
      (∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) ∧
        (∀ g,
          D.expectedGroupCost g replacement ≤
            D.expectedGroupCost g original) := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameUtilityThresholdReplacement_of_finite_signed_nonnegative_target
          (D.restrictPolicy g original)
          hweight
          (fun item => hcost_pos item.1)
          (D.restrictPolicy_bounds g original horiginal)
          (by
            rw [← D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
              g original]
            exact htarget_nonneg g))
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameUtilityThresholdReplacementPolicy original R
  refine ⟨replacement, ?_, ?_⟩
  · intro g
    exact D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupUtility_eq
      original R g
  · intro g
    exact D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupCost_le
      original R hweight horiginal g

/-- Group-restricted utilities sum to total expected posterior utility. -/
theorem sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (policy : AllocationPolicy Applicant State) :
    (∑ g : Group, D.expectedGroupPosteriorUtility g policy) =
      D.expectedPosteriorUtility policy := by
  classical
  simp only [expectedGroupPosteriorUtility, expectedPosteriorUtility,
    CostAwareThresholdData.expectedPosteriorUtility]
  calc
    (∑ g : Group,
      ∑ state : State,
        D.weight state *
          ∑ item : Applicant,
            (if D.group item = g then
              policy item state * D.posteriorUtility item state
            else
              0))
        =
        ∑ state : State,
          ∑ g : Group,
            D.weight state *
              ∑ item : Applicant,
                (if D.group item = g then
                  policy item state * D.posteriorUtility item state
                else
                  0) := by
      rw [Finset.sum_comm]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ g : Group,
              ∑ item : Applicant,
                (if D.group item = g then
                  policy item state * D.posteriorUtility item state
                else
                  0) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      rw [← Finset.mul_sum]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ item : Applicant,
              ∑ g : Group,
                (if D.group item = g then
                  policy item state * D.posteriorUtility item state
                else
                  0) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      congr 1
      rw [Finset.sum_comm]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ item : Applicant,
              policy item state * D.posteriorUtility item state := by
      refine Finset.sum_congr rfl ?_
      intro state _
      congr 1
      refine Finset.sum_congr rfl ?_
      intro item _
      simp

/-- Group-restricted costs sum to total expected cost. -/
theorem sum_expectedGroupCost_eq_expectedCost
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (policy : AllocationPolicy Applicant State) :
    (∑ g : Group, D.expectedGroupCost g policy) =
      D.expectedCost policy := by
  classical
  simp only [expectedGroupCost, expectedCost, CostAwareThresholdData.expectedCost]
  calc
    (∑ g : Group,
      ∑ state : State,
        D.weight state *
          ∑ item : Applicant,
            (if D.group item = g then
              D.allocCost item * policy item state
            else
              0))
        =
        ∑ state : State,
          ∑ g : Group,
            D.weight state *
              ∑ item : Applicant,
                (if D.group item = g then
                  D.allocCost item * policy item state
                else
                  0) := by
      rw [Finset.sum_comm]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ g : Group,
              ∑ item : Applicant,
                (if D.group item = g then
                  D.allocCost item * policy item state
                else
                  0) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      rw [← Finset.mul_sum]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ item : Applicant,
              ∑ g : Group,
                (if D.group item = g then
                  D.allocCost item * policy item state
                else
                  0) := by
      refine Finset.sum_congr rfl ?_
      intro state _
      congr 1
      rw [Finset.sum_comm]
    _ =
        ∑ state : State,
          D.weight state *
            ∑ item : Applicant,
              D.allocCost item * policy item state := by
      refine Finset.sum_congr rfl ?_
      intro state _
      congr 1
      refine Finset.sum_congr rfl ?_
      intro item _
      simp

/-- Feasibility for the source optimization constraints: budget and diversity. -/
def Feasible [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.expectedCost policy ≤ budget ∧
    ∀ g, diversityTarget g ≤ D.expectedGroupPosteriorUtility g policy

/-- Optimality for the grouped allocation subproblem. -/
def Optimal [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.Feasible budget diversityTarget policy ∧
    ∀ other,
      D.Feasible budget diversityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Feasibility for equality diversity constraints. -/
def EqualityFeasible [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.expectedCost policy ≤ budget ∧
    ∀ g, D.expectedGroupPosteriorUtility g policy = equalityTarget g

/-- Optimality for the equality diversity variant. -/
def EqualityOptimal [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.EqualityFeasible budget equalityTarget policy ∧
    ∀ other,
      D.EqualityFeasible budget equalityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Finite source feasibility, including allocation-probability bounds. -/
def SourceFeasible [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  CostAwareThresholdData.AllocationPolicyBounds policy ∧
    D.expectedCost policy ≤ budget ∧
      ∀ g, diversityTarget g ≤ D.expectedGroupPosteriorUtility g policy

/-- Finite optimality restricted to source allocation policies. -/
def SourceOptimal [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.SourceFeasible budget diversityTarget policy ∧
    ∀ other,
      D.SourceFeasible budget diversityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- Finite source equality feasibility over bounded allocation policies. -/
def SourceEqualityFeasible [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  CostAwareThresholdData.AllocationPolicyBounds policy ∧
    D.expectedCost policy ≤ budget ∧
      ∀ g, D.expectedGroupPosteriorUtility g policy = equalityTarget g

/-- Finite equality optimality restricted to source allocation policies. -/
def SourceEqualityOptimal [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  D.SourceEqualityFeasible budget equalityTarget policy ∧
    ∀ other,
      D.SourceEqualityFeasible budget equalityTarget other →
        D.expectedPosteriorUtility other ≤ D.expectedPosteriorUtility policy

/-- A finite policy is cost-aware thresholded separately within each group. -/
def IsGroupwiseSingleCostAwareThresholdPolicy [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (threshold alpha : Group → ℝ)
    (policy : AllocationPolicy Applicant State) : Prop :=
  ∀ g,
    (D.groupCostAwareData g).IsSingleCostAwareThresholdPolicy
      (threshold g) (alpha g) (D.restrictPolicy g policy)

/-- Source-domain finite assembly for the inequality-diversity problem. -/
theorem sourceOptimal_of_groupwise_replacement_improves_constraints
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant State)
    (horiginal : D.SourceOptimal budget diversityTarget original)
    (hreplacement_bounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement) :
    D.SourceOptimal budget diversityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement = D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost replacement,
      ← D.sum_expectedGroupCost_eq_expectedCost original]
    exact Finset.sum_congr rfl (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement]
    exact Finset.sum_le_sum (fun g _ => hgroup g)
  constructor
  · exact ⟨hreplacement_bounds,
      hcost_total.le.trans horiginal.1.2.1,
      fun g => (horiginal.1.2.2 g).trans (hgroup g)⟩
  · intro other hother
    exact (horiginal.2 other hother).trans hutility_total

/-- Source-domain finite assembly for equality diversity constraints. -/
theorem sourceEqualityOptimal_of_groupwise_sameUtility_replacement
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant State)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hreplacement_bounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) :
    D.SourceEqualityOptimal budget equalityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement ≤ D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost replacement,
      ← D.sum_expectedGroupCost_eq_expectedCost original]
    exact Finset.sum_le_sum (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility replacement =
        D.expectedPosteriorUtility original := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original]
    exact Finset.sum_congr rfl (fun g _ => hgroup g)
  constructor
  · exact ⟨hreplacement_bounds,
      hcost_total.trans horiginal.1.2.1,
      fun g => (hgroup g).trans (horiginal.1.2.2 g)⟩
  · intro other hother
    exact (horiginal.2 other hother).trans_eq hutility_total.symm

/--
Main-theorem assembly step.

If an optimal allocation is replaced by another allocation with weakly lower
expected cost, weakly higher utility for every constrained group, and weakly
higher total expected utility, then the replacement is also optimal.
-/
theorem optimal_of_replacement_improves_constraints
    [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant State)
    (horiginal : D.Optimal budget diversityTarget original)
    (hcost :
      D.expectedCost replacement ≤ D.expectedCost original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement)
    (hutility :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement) :
    D.Optimal budget diversityTarget replacement := by
  constructor
  · constructor
    · exact hcost.trans horiginal.1.1
    · intro g
      exact (horiginal.1.2 g).trans (hgroup g)
  · intro other hother
    exact (horiginal.2 other hother).trans hutility

/--
Main-theorem assembly from per-group replacement facts.

This is the source-shaped version used after applying the threshold-replacement
lemma separately to every group.
-/
theorem optimal_of_groupwise_replacement_improves_constraints
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant State)
    (horiginal : D.Optimal budget diversityTarget original)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement) :
    D.Optimal budget diversityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement = D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost replacement,
      ← D.sum_expectedGroupCost_eq_expectedCost original]
    exact Finset.sum_congr rfl (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility original ≤
        D.expectedPosteriorUtility replacement := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility original,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility replacement]
    exact Finset.sum_le_sum (fun g _ => hgroup g)
  exact D.optimal_of_replacement_improves_constraints
    budget diversityTarget original replacement horiginal
    hcost_total.le hgroup hutility_total

/--
Finite-support version of the main threshold-replacement theorem.

Under positive allocation costs and positive cost mass in every group, an
optimal allocation can be replaced by a groupwise cost-aware threshold
allocation that is also optimal.
-/
theorem exists_optimal_groupwise_threshold_replacement_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant State)
    (horiginal : D.Optimal budget diversityTarget original)
    (horiginal_bounds :
      CostAwareThresholdData.AllocationPolicyBounds original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).costAtomMass)) :
    ∃ replacement : AllocationPolicy Applicant State,
      D.Optimal budget diversityTarget replacement := by
  rcases D.exists_groupwiseSameCostThresholdReplacementPolicy_of_finite_positive_costs
      original hweight hcost_pos horiginal_bounds htotal_pos with
    ⟨replacement, hcost, hgroup⟩
  exact ⟨replacement,
    D.optimal_of_groupwise_replacement_improves_constraints
      budget diversityTarget original replacement horiginal hcost hgroup⟩

/--
Equality-diversity assembly from per-group same-utility replacement facts.
-/
theorem equalityOptimal_of_groupwise_sameUtility_replacement
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original replacement : AllocationPolicy Applicant State)
    (horiginal : D.EqualityOptimal budget equalityTarget original)
    (hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original)
    (hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original) :
    D.EqualityOptimal budget equalityTarget replacement := by
  have hcost_total :
      D.expectedCost replacement ≤ D.expectedCost original := by
    rw [← D.sum_expectedGroupCost_eq_expectedCost replacement,
      ← D.sum_expectedGroupCost_eq_expectedCost original]
    exact Finset.sum_le_sum (fun g _ => hcost g)
  have hutility_total :
      D.expectedPosteriorUtility replacement =
        D.expectedPosteriorUtility original := by
    rw [← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        replacement,
      ← D.sum_expectedGroupPosteriorUtility_eq_expectedPosteriorUtility
        original]
    exact Finset.sum_congr rfl (fun g _ => hgroup g)
  constructor
  · constructor
    · exact hcost_total.trans horiginal.1.1
    · intro g
      rw [hgroup g]
      exact horiginal.1.2 g
  · intro other hother
    exact (horiginal.2 other hother).trans_eq hutility_total.symm

/--
Finite-support version of Lemma 3: under equality diversity constraints, a
groupwise cost-aware threshold replacement with the same group utilities and
weakly lower group costs is also optimal.
-/
theorem exists_equalityOptimal_groupwise_threshold_replacement_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant State)
    (horiginal : D.EqualityOptimal budget equalityTarget original)
    (horiginal_bounds :
      CostAwareThresholdData.AllocationPolicyBounds original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).utilityAtomMass)) :
    ∃ replacement : AllocationPolicy Applicant State,
      D.EqualityOptimal budget equalityTarget replacement := by
  rcases D.exists_groupwiseSameUtilityThresholdReplacementPolicy_of_finite_positive_costs
      original hweight hutility_nonneg hcost_pos horiginal_bounds
      htotal_pos with
    ⟨replacement, hgroup, hcost⟩
  exact ⟨replacement,
    D.equalityOptimal_of_groupwise_sameUtility_replacement
      budget equalityTarget original replacement horiginal hcost hgroup⟩

/--
Finite source-domain Theorem 1 with the threshold witnesses retained in the
conclusion rather than erased behind bare existence of an optimal policy.
-/
theorem exists_sourceOptimal_groupwise_threshold_replacement_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (diversityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant State)
    (horiginal : D.SourceOptimal budget diversityTarget original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).costAtomMass)) :
    ∃ threshold alpha : Group → ℝ,
      ∃ replacement : AllocationPolicy Applicant State,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          D.IsGroupwiseSingleCostAwareThresholdPolicy
            threshold alpha replacement ∧
            D.SourceOptimal budget diversityTarget replacement := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameCostThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameCostThresholdReplacement_of_finite_positive_costs
        (D.restrictPolicy g original) hweight
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_bounds g original horiginal.1.1)
        (htotal_pos g))
  let threshold : Group → ℝ := fun g => (R g).t
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameCostThresholdReplacementPolicy original R
  have hbounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement := by
    intro item state
    exact (D.groupCostAwareData (D.group item)).singleCostAwareThresholdPolicy_bounds
      (threshold (D.group item)) (alpha (D.group item))
      (R (D.group item)).threshold (R (D.group item)).threshold_policy
      ⟨item, rfl⟩ state
  have hthreshold :
      D.IsGroupwiseSingleCostAwareThresholdPolicy
        threshold alpha replacement := by
    intro g
    rw [D.restrict_groupwiseSameCostThresholdReplacementPolicy original R g]
    exact (R g).threshold_policy
  have hcost :
      ∀ g,
        D.expectedGroupCost g replacement =
          D.expectedGroupCost g original := fun g =>
    D.groupwiseSameCostThresholdReplacementPolicy_expectedGroupCost_eq
      original R g
  have hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g original ≤
          D.expectedGroupPosteriorUtility g replacement := fun g =>
    D.groupwiseSameCostThresholdReplacementPolicy_expectedGroupUtility_ge
      original R hweight horiginal.1.1 g
  refine ⟨threshold, alpha, replacement, ?_, hthreshold, ?_⟩
  · intro g
    exact ⟨(R g).threshold_policy.1, (R g).threshold_policy.2.1⟩
  · exact D.sourceOptimal_of_groupwise_replacement_improves_constraints
      budget diversityTarget original replacement horiginal hbounds hcost hgroup

/-- Finite source-domain equality variant with explicit threshold witnesses. -/
theorem exists_sourceEqualityOptimal_groupwise_threshold_replacement_of_finite_positive_costs
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant State)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hutility_nonneg : ∀ item state, 0 ≤ D.posteriorUtility item state)
    (hcost_pos : ∀ item, 0 < D.allocCost item)
    (htotal_pos :
      ∀ g : Group,
        0 < finiteAtomTotalMass ((D.groupCostAwareData g).utilityAtomMass)) :
    ∃ threshold alpha : Group → ℝ,
      ∃ replacement : AllocationPolicy Applicant State,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          D.IsGroupwiseSingleCostAwareThresholdPolicy
            threshold alpha replacement ∧
            D.SourceEqualityOptimal budget equalityTarget replacement := by
  classical
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameUtilityThresholdReplacement_of_finite_positive_costs
        (D.restrictPolicy g original) hweight
        (fun item state => hutility_nonneg item.1 state)
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_bounds g original horiginal.1.1)
        (htotal_pos g))
  let threshold : Group → ℝ := fun g => (R g).t
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameUtilityThresholdReplacementPolicy original R
  have hbounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement := by
    intro item state
    exact (D.groupCostAwareData (D.group item)).singleCostAwareThresholdPolicy_bounds
      (threshold (D.group item)) (alpha (D.group item))
      (R (D.group item)).threshold (R (D.group item)).threshold_policy
      ⟨item, rfl⟩ state
  have hthreshold :
      D.IsGroupwiseSingleCostAwareThresholdPolicy
        threshold alpha replacement := by
    intro g
    rw [D.restrict_groupwiseSameUtilityThresholdReplacementPolicy original R g]
    exact (R g).threshold_policy
  have hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original := fun g =>
    D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupUtility_eq
      original R g
  have hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original := fun g =>
    D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupCost_le
      original R hweight horiginal.1.1 g
  refine ⟨threshold, alpha, replacement, ?_, hthreshold, ?_⟩
  · intro g
    exact ⟨(R g).threshold_policy.1, (R g).threshold_policy.2.1⟩
  · exact D.sourceEqualityOptimal_of_groupwise_sameUtility_replacement
      budget equalityTarget original replacement horiginal hbounds hcost hgroup

/--
Finite source-domain equality variant with explicit threshold witnesses for
signed posterior utilities.  The only utility-side sign premise is the source
level nonnegativity of the equality targets.
-/
theorem exists_sourceEqualityOptimal_groupwise_threshold_replacement_of_finite_signed_nonnegative_targets
    [Fintype Group] [DecidableEq Group]
    (D : GroupAllocationData Applicant State Group)
    (budget : ℝ) (equalityTarget : Group → ℝ)
    (original : AllocationPolicy Applicant State)
    (horiginal : D.SourceEqualityOptimal budget equalityTarget original)
    (hweight : ∀ state, 0 ≤ D.weight state)
    (hequalityTarget_nonneg : ∀ g : Group, 0 ≤ equalityTarget g)
    (hcost_pos : ∀ item, 0 < D.allocCost item) :
    ∃ threshold alpha : Group → ℝ,
      ∃ replacement : AllocationPolicy Applicant State,
        (∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1) ∧
          D.IsGroupwiseSingleCostAwareThresholdPolicy
            threshold alpha replacement ∧
            D.SourceEqualityOptimal budget equalityTarget replacement := by
  classical
  have htarget_nonneg :
      ∀ g : Group, 0 ≤ D.expectedGroupPosteriorUtility g original := by
    intro g
    rw [horiginal.1.2.2 g]
    exact hequalityTarget_nonneg g
  let R :
      ∀ g : Group,
        ((D.groupCostAwareData g).SameUtilityThresholdReplacement
          (D.restrictPolicy g original)) := fun g =>
    Classical.choice
      ((D.groupCostAwareData g).exists_sameUtilityThresholdReplacement_of_finite_signed_nonnegative_target
        (D.restrictPolicy g original)
        hweight
        (fun item => hcost_pos item.1)
        (D.restrictPolicy_bounds g original horiginal.1.1)
        (by
          rw [← D.expectedGroupPosteriorUtility_eq_restrictedExpectedPosteriorUtility
            g original]
          exact htarget_nonneg g))
  let threshold : Group → ℝ := fun g => (R g).t
  let alpha : Group → ℝ := fun g => (R g).alpha
  let replacement : AllocationPolicy Applicant State :=
    D.groupwiseSameUtilityThresholdReplacementPolicy original R
  have hbounds :
      CostAwareThresholdData.AllocationPolicyBounds replacement := by
    intro item state
    exact (D.groupCostAwareData (D.group item)).singleCostAwareThresholdPolicy_bounds
      (threshold (D.group item)) (alpha (D.group item))
      (R (D.group item)).threshold (R (D.group item)).threshold_policy
      ⟨item, rfl⟩ state
  have hthreshold :
      D.IsGroupwiseSingleCostAwareThresholdPolicy
        threshold alpha replacement := by
    intro g
    rw [D.restrict_groupwiseSameUtilityThresholdReplacementPolicy original R g]
    exact (R g).threshold_policy
  have hgroup :
      ∀ g,
        D.expectedGroupPosteriorUtility g replacement =
          D.expectedGroupPosteriorUtility g original := fun g =>
    D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupUtility_eq
      original R g
  have hcost :
      ∀ g,
        D.expectedGroupCost g replacement ≤
          D.expectedGroupCost g original := fun g =>
    D.groupwiseSameUtilityThresholdReplacementPolicy_expectedGroupCost_le
      original R hweight horiginal.1.1 g
  refine ⟨threshold, alpha, replacement, ?_, hthreshold, ?_⟩
  · intro g
    exact ⟨(R g).threshold_policy.1, (R g).threshold_policy.2.1⟩
  · exact D.sourceEqualityOptimal_of_groupwise_sameUtility_replacement
      budget equalityTarget original replacement horiginal hbounds hcost hgroup

end GroupAllocationData

/--
Source data for one fixed threshold policy.

For applicant `i`, the paper defines
`q_i = Pr(D_i > t_{g_i})`, `e_i = E[U_i | D_i > t_{g_i}]`, and
`o_i = 1_{mu_i > t_{g_i}} + alpha_{g_i} 1_{mu_i = t_{g_i}}`.
Those probability/expectation quantities are treated here as already computed
constants for the fixed threshold policy.
-/
structure FixedThresholdData (Applicant Group : Type*) where
  group : Applicant → Group
  q : Applicant → ℝ
  e : Applicant → ℝ
  o : Applicant → ℝ
  mu : Applicant → ℝ
  screenCost : ℝ
  allocCost : ℝ
  budget : ℝ
  diversityTarget : Group → ℝ

namespace FixedThresholdData

variable {Applicant Group : Type*} [Fintype Applicant]

/-- Equation (obj): expected utility for a fixed threshold policy. -/
noncomputable def utility (D : FixedThresholdData Applicant Group)
    (p : Applicant → ℝ) : ℝ :=
  ∑ i : Applicant,
    (D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i))

/-- Constant term of the affine objective in the screening probabilities. -/
noncomputable def baseUtility (D : FixedThresholdData Applicant Group) : ℝ :=
  ∑ i : Applicant, D.o i * D.mu i

/-- Linear coefficient of applicant `i` in the fixed-threshold utility. -/
noncomputable def utilityCoeff (D : FixedThresholdData Applicant Group)
    (i : Applicant) : ℝ :=
  D.q i * D.e i - D.o i * D.mu i

/-- Equation (obj) is affine in the screening probabilities. -/
theorem utility_eq_base_add
    (D : FixedThresholdData Applicant Group) (p : Applicant → ℝ) :
    D.utility p = D.baseUtility + ∑ i : Applicant, D.utilityCoeff i * p i := by
  classical
  simp only [utility, baseUtility, utilityCoeff]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- Equation (constr1): expected budget use for a fixed threshold policy. -/
noncomputable def budgetUse (D : FixedThresholdData Applicant Group)
    (p : Applicant → ℝ) : ℝ :=
  ∑ i : Applicant,
    (D.screenCost * p i + D.allocCost * D.q i * p i +
      D.allocCost * D.o i * (1 - p i))

/-- Constant term of the affine budget expression. -/
noncomputable def baseBudgetUse (D : FixedThresholdData Applicant Group) : ℝ :=
  ∑ i : Applicant, D.allocCost * D.o i

/-- Linear coefficient of applicant `i` in the fixed-threshold budget use. -/
noncomputable def budgetCoeff (D : FixedThresholdData Applicant Group)
    (i : Applicant) : ℝ :=
  D.screenCost + D.allocCost * D.q i - D.allocCost * D.o i

/-- Equation (constr1) is affine in the screening probabilities. -/
theorem budgetUse_eq_base_add
    (D : FixedThresholdData Applicant Group) (p : Applicant → ℝ) :
    D.budgetUse p =
      D.baseBudgetUse + ∑ i : Applicant, D.budgetCoeff i * p i := by
  classical
  simp only [budgetUse, baseBudgetUse, budgetCoeff]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- Equation (constr2): expected group utility for a fixed threshold policy. -/
noncomputable def groupUtility [DecidableEq Group]
    (D : FixedThresholdData Applicant Group) (g : Group)
    (p : Applicant → ℝ) : ℝ :=
  ∑ i : Applicant,
    if D.group i = g then
      D.q i * D.e i * p i + D.o i * D.mu i * (1 - p i)
    else
      0

/-- Constant term of the affine group-utility expression. -/
noncomputable def baseGroupUtility [DecidableEq Group]
    (D : FixedThresholdData Applicant Group) (g : Group) : ℝ :=
  ∑ i : Applicant, if D.group i = g then D.o i * D.mu i else 0

/-- Linear coefficient of applicant `i` in group `g`'s utility expression. -/
noncomputable def groupUtilityCoeff [DecidableEq Group]
    (D : FixedThresholdData Applicant Group) (g : Group)
    (i : Applicant) : ℝ :=
  if D.group i = g then D.utilityCoeff i else 0

/-- Equation (constr2) is affine in the screening probabilities. -/
theorem groupUtility_eq_base_add [DecidableEq Group]
    (D : FixedThresholdData Applicant Group) (g : Group)
    (p : Applicant → ℝ) :
    D.groupUtility g p =
      D.baseGroupUtility g +
        ∑ i : Applicant, D.groupUtilityCoeff g i * p i := by
  classical
  simp only [groupUtility, baseGroupUtility, groupUtilityCoeff]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : D.group i = g
  · simp [h, utilityCoeff]
    ring
  · simp [h]

end FixedThresholdData

/--
Source-facing data for the fixed-threshold LP.  The inherited record is the
algebraic layer; these fields state the threshold and coefficient contract
printed immediately before Eqs. (obj), (constr1), and (constr2).
-/
structure FixedThresholdLPSourceData (Applicant Group : Type*) extends
    FixedThresholdData Applicant Group where
  threshold : Group → ℝ
  alpha : Group → ℝ
  alpha_bounds : ∀ g, 0 ≤ alpha g ∧ alpha g ≤ 1
  /-- Probability space for the paper's post-screening utility estimate `D_i`. -/
  Outcome : Type*
  outcomeMeasurable : MeasurableSpace Outcome
  law : @Measure Outcome outcomeMeasurable
  law_is_probability : @IsProbabilityMeasure Outcome outcomeMeasurable law
  postScreeningUtility : Applicant → Outcome → ℝ
  actualUtility : Applicant → Outcome → ℝ
  postScreeningUtility_measurable : ∀ i, Measurable (postScreeningUtility i)
  postScreeningUtility_integrable : ∀ i, Integrable (postScreeningUtility i) law
  actualUtility_measurable : ∀ i, Measurable (actualUtility i)
  actualUtility_integrable : ∀ i, Integrable (actualUtility i) law
  /-- `D_i` is the posterior expected utility: it preserves the mean of `U_i`
  on every event determined by the observed posterior value. -/
  posterior_mean_on_score_events : ∀ i (s : Set ℝ), MeasurableSet s →
    ∫ outcome,
      ({outcome | postScreeningUtility i outcome ∈ s}.indicator
        (actualUtility i)) outcome ∂law =
      ∫ outcome,
        ({outcome | postScreeningUtility i outcome ∈ s}.indicator
          (postScreeningUtility i)) outcome ∂law
  /-- `q_i = Pr(D_i > t_{g_i})`. -/
  q_semantics : ∀ i,
    toFixedThresholdData.q i =
      @MeasureTheory.integral Outcome ℝ _ _ outcomeMeasurable law
        (fun outcome => if threshold (toFixedThresholdData.group i) <
          postScreeningUtility i outcome then 1 else 0)
  /-- `q_i e_i` is the utility mass above the fixed threshold. -/
  screened_utility_mass_semantics : ∀ i,
    toFixedThresholdData.q i * toFixedThresholdData.e i =
      @MeasureTheory.integral Outcome ℝ _ _ outcomeMeasurable law
        (fun outcome => if threshold (toFixedThresholdData.group i) <
          postScreeningUtility i outcome then actualUtility i outcome else 0)
  /-- When the screening event has positive probability, `e_i` is its
  conditional expected utility.  The product equation above fixes the only
  LP-relevant quantity when the event has probability zero. -/
  e_conditional_semantics : ∀ i, 0 < toFixedThresholdData.q i →
    toFixedThresholdData.e i =
      (toFixedThresholdData.q i)⁻¹ *
        @MeasureTheory.integral Outcome ℝ _ _ outcomeMeasurable law
          (fun outcome => if threshold (toFixedThresholdData.group i) <
            postScreeningUtility i outcome then actualUtility i outcome else 0)
  /-- `mu_i = E[U_i]`, the pre-screening expected utility. -/
  mu_semantics : ∀ i,
    toFixedThresholdData.mu i =
      @MeasureTheory.integral Outcome ℝ _ _ outcomeMeasurable law
        (actualUtility i)
  o_formula : ∀ i,
    toFixedThresholdData.o i =
      if threshold (toFixedThresholdData.group i) < toFixedThresholdData.mu i then 1
      else if toFixedThresholdData.mu i = threshold (toFixedThresholdData.group i) then
        alpha (toFixedThresholdData.group i)
      else 0

namespace FixedThresholdLPSourceData

variable {Applicant Group : Type*} [Fintype Applicant]

/-- The source screening variables are probabilities. -/
def screeningProbabilityBounds
    (D : FixedThresholdLPSourceData Applicant Group)
    (p : Applicant → ℝ) : Prop :=
  ∀ i, 0 ≤ p i ∧ p i ≤ 1

/-- The unscreened-allocation coefficient is a probability under the source rule. -/
theorem o_bounds
    (D : FixedThresholdLPSourceData Applicant Group) (i : Applicant) :
    0 ≤ D.toFixedThresholdData.o i ∧ D.toFixedThresholdData.o i ≤ 1 := by
  rcases D.alpha_bounds (D.toFixedThresholdData.group i) with ⟨halpha_nonneg, halpha_le_one⟩
  rw [D.o_formula i]
  by_cases hgt : D.threshold (D.toFixedThresholdData.group i) < D.toFixedThresholdData.mu i
  · simp [hgt]
  · by_cases heq : D.toFixedThresholdData.mu i = D.threshold (D.toFixedThresholdData.group i)
    · simp [hgt, heq, halpha_nonneg, halpha_le_one]
    · simp [hgt, heq]

end FixedThresholdLPSourceData

/-- Constraint rows for the fixed-threshold screening LP. -/
inductive FixedThresholdConstraint (Applicant Group : Type*) where
  | budget : FixedThresholdConstraint Applicant Group
  | diversity : Group → FixedThresholdConstraint Applicant Group
  | probabilityUpper : Applicant → FixedThresholdConstraint Applicant Group
deriving DecidableEq, Fintype

namespace FixedThresholdData

variable {Applicant Group : Type*}
  [Fintype Applicant] [Fintype Group] [DecidableEq Applicant]
  [DecidableEq Group]

/--
The finite standard-form LP for the fixed-threshold screening problem.

The objective maximizes the nonconstant part of Eq. (obj).  The dropped
constant `baseUtility` is restored by `fixedThresholdLP_objective_eq_utility`.
-/
noncomputable def fixedThresholdLP
    (D : FixedThresholdData Applicant Group) :
    StandardMaxLP Applicant (FixedThresholdConstraint Applicant Group) where
  A constraint i :=
    match constraint with
    | .budget => D.budgetCoeff i
    | .diversity g => -D.groupUtilityCoeff g i
    | .probabilityUpper j => if i = j then 1 else 0
  b constraint :=
    match constraint with
    | .budget => D.budget - D.baseBudgetUse
    | .diversity g => D.baseGroupUtility g - D.diversityTarget g
    | .probabilityUpper _ => 1
  c i := D.utilityCoeff i

/-- The LP objective is exactly the fixed-threshold utility up to its constant. -/
theorem fixedThresholdLP_objective_eq_utility_sub_base
    (D : FixedThresholdData Applicant Group) (p : Applicant → ℝ) :
    (D.fixedThresholdLP).primalObjective p = D.utility p - D.baseUtility := by
  classical
  rw [fixedThresholdLP, StandardMaxLP.primalObjective]
  have h := D.utility_eq_base_add p
  linarith

/-- The LP budget row is the source budget inequality after moving constants. -/
theorem fixedThresholdLP_budget_row_iff
    (D : FixedThresholdData Applicant Group) (p : Applicant → ℝ) :
    (∑ i : Applicant,
        D.fixedThresholdLP.A (.budget : FixedThresholdConstraint Applicant Group) i *
          p i) ≤
        D.fixedThresholdLP.b (.budget : FixedThresholdConstraint Applicant Group) ↔
      D.budgetUse p ≤ D.budget := by
  classical
  rw [fixedThresholdLP]
  have h := D.budgetUse_eq_base_add p
  constructor <;> intro hrow <;> linarith

/-- The LP diversity row is the source lower-bound inequality. -/
theorem fixedThresholdLP_diversity_row_iff
    (D : FixedThresholdData Applicant Group) (g : Group)
    (p : Applicant → ℝ) :
    (∑ i : Applicant,
        D.fixedThresholdLP.A (.diversity g : FixedThresholdConstraint Applicant Group) i *
          p i) ≤
        D.fixedThresholdLP.b (.diversity g : FixedThresholdConstraint Applicant Group) ↔
      D.diversityTarget g ≤ D.groupUtility g p := by
  classical
  rw [fixedThresholdLP]
  have hgroup := D.groupUtility_eq_base_add g p
  have hneg :
      (∑ i : Applicant, -D.groupUtilityCoeff g i * p i) =
        -∑ i : Applicant, D.groupUtilityCoeff g i * p i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  rw [hneg]
  constructor <;> intro hrow <;> linarith

/-- The LP upper-probability row says `p_i ≤ 1`. -/
theorem fixedThresholdLP_probabilityUpper_row_iff
    (D : FixedThresholdData Applicant Group) (p : Applicant → ℝ)
    (i : Applicant) :
    (∑ j : Applicant,
        D.fixedThresholdLP.A
            (.probabilityUpper i : FixedThresholdConstraint Applicant Group) j *
          p j) ≤
        D.fixedThresholdLP.b
          (.probabilityUpper i : FixedThresholdConstraint Applicant Group) ↔
      p i ≤ 1 := by
  classical
  rw [fixedThresholdLP]
  simp

end FixedThresholdData

/--
Data for the appendix optimized two-group procedure.

`ScreenApplicant` is the group whose members may be screened; `DirectApplicant`
is the group whose post-screening distribution is a point mass and whose
allocation probabilities are LP variables directly.
-/
structure OptimizedTwoGroupData (ScreenApplicant DirectApplicant : Type*) where
  q : ScreenApplicant → ℝ
  e : ScreenApplicant → ℝ
  o : ScreenApplicant → ℝ
  muScreen : ScreenApplicant → ℝ
  muDirect : DirectApplicant → ℝ
  screenCost : ℝ
  allocCost : ℝ
  budget : ℝ
  lambdaScreen : ℝ
  lambdaDirect : ℝ

/--
Source-facing data for the appendix's optimized two-group LP.  Its inherited
record contains the displayed algebra; this wrapper records the fixed
threshold, coefficient contract, and probability-vector domain from the
source construction.
-/
structure OptimizedTwoGroupLPSourceData
    (ScreenApplicant DirectApplicant : Type*) extends
    OptimizedTwoGroupData ScreenApplicant DirectApplicant where
  threshold : ℝ
  alpha : ℝ
  alpha_bounds : 0 ≤ alpha ∧ alpha ≤ 1
  /-- Probability space for the optimized screened group's utility estimates. -/
  ScreenOutcome : Type*
  screenOutcomeMeasurable : MeasurableSpace ScreenOutcome
  screenLaw : @Measure ScreenOutcome screenOutcomeMeasurable
  screenLaw_is_probability :
    @IsProbabilityMeasure ScreenOutcome screenOutcomeMeasurable screenLaw
  screenPostUtility : ScreenApplicant → ScreenOutcome → ℝ
  screenActualUtility : ScreenApplicant → ScreenOutcome → ℝ
  screenPostUtility_measurable : ∀ i, Measurable (screenPostUtility i)
  screenPostUtility_integrable : ∀ i, Integrable (screenPostUtility i) screenLaw
  screenActualUtility_measurable : ∀ i, Measurable (screenActualUtility i)
  screenActualUtility_integrable : ∀ i, Integrable (screenActualUtility i) screenLaw
  /-- The screened score `D_i` is the conditional expected utility of `U_i`. -/
  screen_posterior_mean_on_score_events : ∀ i (s : Set ℝ), MeasurableSet s →
    ∫ outcome,
      ({outcome | screenPostUtility i outcome ∈ s}.indicator
        (screenActualUtility i)) outcome ∂screenLaw =
      ∫ outcome,
        ({outcome | screenPostUtility i outcome ∈ s}.indicator
          (screenPostUtility i)) outcome ∂screenLaw
  /-- `q_i = Pr(D_i > t)` for the screened group. -/
  q_semantics : ∀ i,
    toOptimizedTwoGroupData.q i =
      @MeasureTheory.integral ScreenOutcome ℝ _ _ screenOutcomeMeasurable screenLaw
        (fun outcome => if threshold < screenPostUtility i outcome then 1 else 0)
  /-- `q_i e_i` is the screened utility mass above the optimized threshold. -/
  screened_utility_mass_semantics : ∀ i,
    toOptimizedTwoGroupData.q i * toOptimizedTwoGroupData.e i =
      @MeasureTheory.integral ScreenOutcome ℝ _ _ screenOutcomeMeasurable screenLaw
        (fun outcome => if threshold < screenPostUtility i outcome then
          screenActualUtility i outcome else 0)
  /-- Conditional-mean reading of `e_i` away from the zero-probability case. -/
  e_conditional_semantics : ∀ i, 0 < toOptimizedTwoGroupData.q i →
    toOptimizedTwoGroupData.e i =
      (toOptimizedTwoGroupData.q i)⁻¹ *
        @MeasureTheory.integral ScreenOutcome ℝ _ _ screenOutcomeMeasurable screenLaw
          (fun outcome => if threshold < screenPostUtility i outcome then
            screenActualUtility i outcome else 0)
  /-- `mu_i` is the screened group's pre-screening expected utility. -/
  muScreen_semantics : ∀ i,
    toOptimizedTwoGroupData.muScreen i =
      @MeasureTheory.integral ScreenOutcome ℝ _ _ screenOutcomeMeasurable screenLaw
        (screenActualUtility i)
  /-- Probability model for the direct group, for which screening adds no
  information. -/
  DirectOutcome : Type*
  directOutcomeMeasurable : MeasurableSpace DirectOutcome
  directLaw : DirectApplicant → @Measure DirectOutcome directOutcomeMeasurable
  directLaw_is_probability : ∀ i,
    @IsProbabilityMeasure DirectOutcome directOutcomeMeasurable (directLaw i)
  directPostScreeningUtility : DirectApplicant → DirectOutcome → ℝ
  directActualUtility : DirectApplicant → DirectOutcome → ℝ
  directPostScreeningUtility_measurable : ∀ i,
    Measurable (directPostScreeningUtility i)
  directPostScreeningUtility_integrable : ∀ i,
    Integrable (directPostScreeningUtility i) (directLaw i)
  directActualUtility_measurable : ∀ i, Measurable (directActualUtility i)
  directActualUtility_integrable : ∀ i,
    Integrable (directActualUtility i) (directLaw i)
  /-- The source's direct-group `D_i` is a point mass at the prior mean. -/
  direct_post_screening_is_constant : ∀ i outcome,
    directPostScreeningUtility i outcome = toOptimizedTwoGroupData.muDirect i
  direct_posterior_mean_on_score_events : ∀ i (s : Set ℝ), MeasurableSet s →
    ∫ outcome,
      ({outcome | directPostScreeningUtility i outcome ∈ s}.indicator
        (directActualUtility i)) outcome ∂(directLaw i) =
      ∫ outcome,
        ({outcome | directPostScreeningUtility i outcome ∈ s}.indicator
          (directPostScreeningUtility i)) outcome ∂(directLaw i)
  /-- The direct coefficient is the prior expected realized utility. -/
  muDirect_semantics : ∀ i,
    toOptimizedTwoGroupData.muDirect i =
      @MeasureTheory.integral DirectOutcome ℝ _ _ directOutcomeMeasurable (directLaw i)
        (directActualUtility i)
  o_formula : ∀ i,
    toOptimizedTwoGroupData.o i =
      if threshold < toOptimizedTwoGroupData.muScreen i then 1
      else if toOptimizedTwoGroupData.muScreen i = threshold then alpha else 0

namespace OptimizedTwoGroupLPSourceData

variable {ScreenApplicant DirectApplicant : Type*}

/-- Both appendix LP decision blocks are probability vectors. -/
def probabilityBounds
    (D : OptimizedTwoGroupLPSourceData ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : Prop :=
  (∀ i : ScreenApplicant, 0 ≤ p i ∧ p i ≤ 1) ∧
    ∀ i : DirectApplicant, 0 ≤ a i ∧ a i ≤ 1

/-- The upper-bound display in Eq. (lp5) follows from the full source domain. -/
theorem probabilityBounds_implies_upper
    (D : OptimizedTwoGroupLPSourceData ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ)
    (h : D.probabilityBounds p a) :
    (∀ i : ScreenApplicant, p i ≤ 1) ∧ ∀ i : DirectApplicant, a i ≤ 1 := by
  exact ⟨fun i => (h.1 i).2, fun i => (h.2 i).2⟩

end OptimizedTwoGroupLPSourceData

namespace OptimizedTwoGroupData

variable {ScreenApplicant DirectApplicant : Type*}
  [Fintype ScreenApplicant] [Fintype DirectApplicant]

/-- Equation (lp1): optimized two-group objective. -/
noncomputable def utility
  (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
  (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : ℝ :=
  (∑ i : ScreenApplicant,
    (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))) +
  (∑ i : DirectApplicant, D.muDirect i * a i)

/-- Constant term in the screened-group part of Eq. (lp1). -/
noncomputable def baseUtility
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant) : ℝ :=
  ∑ i : ScreenApplicant, D.o i * D.muScreen i

/-- Screened-group coefficient of `p_i` in Eq. (lp1). -/
noncomputable def screenUtilityCoeff
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (i : ScreenApplicant) : ℝ :=
  D.q i * D.e i - D.o i * D.muScreen i

/-- Equation (lp1) is affine in the variables `p` and `a`. -/
theorem utility_eq_base_add
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    D.utility p a =
      D.baseUtility +
        (∑ i : ScreenApplicant, D.screenUtilityCoeff i * p i) +
          (∑ i : DirectApplicant, D.muDirect i * a i) := by
  classical
  have hscreen :
      (∑ i : ScreenApplicant,
        (D.q i * D.e i * p i +
          D.o i * D.muScreen i * (1 - p i))) =
        D.baseUtility +
          ∑ i : ScreenApplicant, D.screenUtilityCoeff i * p i := by
    simp only [baseUtility, screenUtilityCoeff]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  simp only [utility]
  rw [hscreen]

/-- Equation (lp2): optimized two-group budget use. -/
noncomputable def budgetUse
  (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
  (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : ℝ :=
  (∑ i : ScreenApplicant,
    (D.screenCost * p i + D.allocCost * D.q i * p i +
      D.allocCost * D.o i * (1 - p i))) +
  (∑ i : DirectApplicant, D.allocCost * a i)

/-- Constant term in the screened-group part of Eq. (lp2). -/
noncomputable def baseBudgetUse
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant) : ℝ :=
  ∑ i : ScreenApplicant, D.allocCost * D.o i

/-- Screened-group coefficient of `p_i` in Eq. (lp2). -/
noncomputable def screenBudgetCoeff
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (i : ScreenApplicant) : ℝ :=
  D.screenCost + D.allocCost * D.q i - D.allocCost * D.o i

/-- Equation (lp2) is affine in the variables `p` and `a`. -/
theorem budgetUse_eq_base_add
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) :
    D.budgetUse p a =
      D.baseBudgetUse +
        (∑ i : ScreenApplicant, D.screenBudgetCoeff i * p i) +
          (∑ i : DirectApplicant, D.allocCost * a i) := by
  classical
  have hscreen :
      (∑ i : ScreenApplicant,
        (D.screenCost * p i + D.allocCost * D.q i * p i +
          D.allocCost * D.o i * (1 - p i))) =
        D.baseBudgetUse +
          ∑ i : ScreenApplicant, D.screenBudgetCoeff i * p i := by
    simp only [baseBudgetUse, screenBudgetCoeff]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  simp only [budgetUse]
  rw [hscreen]

/-- Equation (lp3): screened-group utility equality target. -/
noncomputable def screenedGroupUtility
  (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
  (p : ScreenApplicant → ℝ) : ℝ :=
  ∑ i : ScreenApplicant,
    (D.q i * D.e i * p i + D.o i * D.muScreen i * (1 - p i))

/-- Equation (lp4): direct-allocation group utility equality target. -/
noncomputable def directGroupUtility
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (a : DirectApplicant → ℝ) : ℝ :=
  ∑ i : DirectApplicant, D.muDirect i * a i

/-- Equation (lp3) is affine in the screening probabilities. -/
theorem screenedGroupUtility_eq_base_add
    (D : OptimizedTwoGroupData ScreenApplicant DirectApplicant)
    (p : ScreenApplicant → ℝ) :
    D.screenedGroupUtility p =
      D.baseUtility +
        (∑ i : ScreenApplicant, D.screenUtilityCoeff i * p i) := by
  classical
  simp only [screenedGroupUtility, baseUtility, screenUtilityCoeff]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- The displayed upper bounds in Eq. (lp5). -/
def probabilityUpperBounds
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : Prop :=
  (∀ i : ScreenApplicant, p i ≤ 1) ∧
    ∀ i : DirectApplicant, a i ≤ 1

/-- The optimized variables are probabilities, hence lie in the unit interval. -/
def probabilityBounds
    (p : ScreenApplicant → ℝ) (a : DirectApplicant → ℝ) : Prop :=
  (∀ i : ScreenApplicant, 0 ≤ p i ∧ p i ≤ 1) ∧
    ∀ i : DirectApplicant, 0 ≤ a i ∧ a i ≤ 1

end OptimizedTwoGroupData

end CGGG20SelectiveInformationAcquisition
