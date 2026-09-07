import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Optimization.Argmax

/-!
# Finite Threshold Exchange

Reusable finite-sum exchange lemmas for threshold and fractional-knapsack
arguments.  The core statement compares a threshold policy `threshold` with an
arbitrary policy `other`: whenever positive deltas occur only where
`cost * t <= value` and negative deltas occur only where `value <= cost * t`,
the value delta dominates `t` times the cost delta.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Optimization

open AppliedModelingLib.Decision

noncomputable section

/--
Any target in a closed real interval is obtained by unit-interval
interpolation between the endpoints.

Threshold proofs use this to choose a boundary-randomization probability once
the strict and closed tail values bracket the target.
-/
theorem exists_unit_interval_interpolation
    {low high target : ℝ}
    (hlow_le_high : low ≤ high)
    (hlow_le_target : low ≤ target)
    (htarget_le_high : target ≤ high) :
    ∃ alpha : ℝ,
      0 ≤ alpha ∧ alpha ≤ 1 ∧
        low + alpha * (high - low) = target := by
  by_cases h_eq : high = low
  · have htarget : target = low := by
      exact le_antisymm (by simpa [h_eq] using htarget_le_high)
        hlow_le_target
    refine ⟨0, by norm_num, by norm_num, ?_⟩
    simp [htarget]
  · have hlow_ne_high : low ≠ high := by
      intro h
      exact h_eq h.symm
    have hlow_lt_high : low < high :=
      lt_of_le_of_ne hlow_le_high hlow_ne_high
    have hden_pos : 0 < high - low := sub_pos.mpr hlow_lt_high
    let alpha : ℝ := (target - low) / (high - low)
    have halpha_nonneg : 0 ≤ alpha := by
      dsimp [alpha]
      exact div_nonneg (sub_nonneg.mpr hlow_le_target) hden_pos.le
    have halpha_le_one : alpha ≤ 1 := by
      dsimp [alpha]
      have hnum : target - low ≤ high - low := by linarith
      exact (div_le_one hden_pos).mpr hnum
    have halpha_mul :
        alpha * (high - low) = target - low := by
      dsimp [alpha]
      field_simp [ne_of_gt hden_pos]
    refine ⟨alpha, halpha_nonneg, halpha_le_one, ?_⟩
    linarith

/-- Weighted value difference between a threshold policy and another policy. -/
def weightedDeltaValue {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ)
    (threshold other : Item → State → ℝ) : ℝ :=
  ∑ state : State,
    weight state *
      ∑ item : Item,
        (threshold item state - other item state) * value item state

/-- Weighted cost difference between a threshold policy and another policy. -/
def weightedDeltaCost {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) : ℝ :=
  ∑ state : State,
    weight state *
      ∑ item : Item,
        cost item * (threshold item state - other item state)

/--
Weighted difference against the threshold value `cost * t`.

This is a source-shaped intermediate form for appendix exchange proofs.
-/
def weightedDeltaThresholdCost {Item State : Type*}
    [Fintype Item] [Fintype State] (weight : State → ℝ)
    (cost : Item → ℝ) (threshold other : Item → State → ℝ)
    (t : ℝ) : ℝ :=
  ∑ state : State,
    weight state *
      ∑ item : Item,
        (threshold item state - other item state) * (cost item * t)

/--
Pointwise threshold exchange inequality.

If a strictly positive delta is allowed only where `bound <= value`, and a
strictly negative delta only where `value <= bound`, then the delta-valued
contribution beats the delta-bound contribution.  The zero-delta case needs no
comparison.
-/
theorem delta_mul_bound_le_delta_mul_value
    {delta value bound : ℝ}
    (hpos : 0 < delta → bound ≤ value)
    (hneg : delta < 0 → value ≤ bound) :
    delta * bound ≤ delta * value := by
  by_cases hdelta_pos : 0 < delta
  · exact mul_le_mul_of_nonneg_left (hpos hdelta_pos) hdelta_pos.le
  by_cases hdelta_neg : delta < 0
  · have hdelta_nonpos : delta ≤ 0 := hdelta_neg.le
    simpa [mul_comm] using
      mul_le_mul_of_nonpos_left (hneg hdelta_neg) hdelta_nonpos
  · have hdelta_nonpos : delta ≤ 0 := le_of_not_gt hdelta_pos
    have hdelta_nonneg : 0 ≤ delta := le_of_not_gt hdelta_neg
    have hdelta_zero : delta = 0 := le_antisymm hdelta_nonpos hdelta_nonneg
    simp [hdelta_zero]

/--
The source-shaped weighted threshold-cost delta is `t` times the weighted cost
delta.
-/
theorem weightedDeltaThresholdCost_eq_mul_weightedDeltaCost
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) (t : ℝ) :
    weightedDeltaThresholdCost weight cost threshold other t =
      t * weightedDeltaCost weight cost threshold other := by
  classical
  calc
    weightedDeltaThresholdCost weight cost threshold other t =
        ∑ state : State,
          weight state *
            (t * ∑ item : Item,
              cost item * (threshold item state - other item state)) := by
      simp only [weightedDeltaThresholdCost]
      refine Finset.sum_congr rfl ?_
      intro state _
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro item _
      ring
    _ = t * weightedDeltaCost weight cost threshold other := by
      simp only [weightedDeltaCost]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro state _
      ring

/--
Finite weighted threshold exchange inequality.

This is the finite algebraic core of a cost-aware threshold nondominance proof.
-/
theorem weightedDeltaThresholdCost_le_weightedDeltaValue
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) (t : ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hpos :
      ∀ item state,
        0 < threshold item state - other item state →
          cost item * t ≤ value item state)
    (hneg :
      ∀ item state,
        threshold item state - other item state < 0 →
          value item state ≤ cost item * t) :
    weightedDeltaThresholdCost weight cost threshold other t ≤
      weightedDeltaValue weight value threshold other := by
  classical
  simp only [weightedDeltaThresholdCost, weightedDeltaValue]
  refine Finset.sum_le_sum ?_
  intro state _
  refine mul_le_mul_of_nonneg_left ?_ (hweight state)
  refine Finset.sum_le_sum ?_
  intro item _
  exact delta_mul_bound_le_delta_mul_value
    (hpos item state) (hneg item state)

/--
The value delta dominates `t` times the cost delta.
-/
theorem mul_weightedDeltaCost_le_weightedDeltaValue
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) (t : ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hpos :
      ∀ item state,
        0 < threshold item state - other item state →
          cost item * t ≤ value item state)
    (hneg :
      ∀ item state,
        threshold item state - other item state < 0 →
          value item state ≤ cost item * t) :
    t * weightedDeltaCost weight cost threshold other ≤
      weightedDeltaValue weight value threshold other := by
  rw [← weightedDeltaThresholdCost_eq_mul_weightedDeltaCost]
  exact weightedDeltaThresholdCost_le_weightedDeltaValue
    weight value cost threshold other t hweight hpos hneg

/-! ## Abstract finite-linear expectation threshold exchange -/

/-- Expected value difference between a threshold policy and another policy. -/
def expectedDeltaValue {Item Outcome : Type*} [Fintype Item]
    (expect : (Outcome → ℝ) → ℝ) (value : Item → Outcome → ℝ)
    (threshold other : Item → Outcome → ℝ) : ℝ :=
  expect fun outcome =>
    ∑ item : Item,
      (threshold item outcome - other item outcome) * value item outcome

/-- Expected cost difference between a threshold policy and another policy. -/
def expectedDeltaCost {Item Outcome : Type*} [Fintype Item]
    (expect : (Outcome → ℝ) → ℝ) (cost : Item → ℝ)
    (threshold other : Item → Outcome → ℝ) : ℝ :=
  expect fun outcome =>
    ∑ item : Item,
      cost item * (threshold item outcome - other item outcome)

/-- Finite weighted expectation over an explicit state space. -/
def finiteWeightedExpectation {State : Type*} [Fintype State]
    (weight : State → ℝ) (f : State → ℝ) : ℝ :=
  ∑ state : State, weight state * f state

/-- Nonnegative finite weighted sums form a monotone finite-linear expectation. -/
theorem finiteWeightedExpectation_finiteLinear
    {State : Type*} [Fintype State]
    (weight : State → ℝ) (hweight : ∀ state, 0 ≤ weight state) :
    FiniteLinearExpectation (finiteWeightedExpectation weight) := by
  constructor
  · intro f g hfg
    simp only [finiteWeightedExpectation]
    exact Finset.sum_le_sum fun state _ =>
      mul_le_mul_of_nonneg_left (hfg state) (hweight state)
  constructor
  · intro c f
    simp only [finiteWeightedExpectation]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro state _
    ring
  · intro f g
    simp only [finiteWeightedExpectation]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro state _
    ring

/-- The abstract expected value delta specializes to the finite weighted delta. -/
theorem expectedDeltaValue_finiteWeightedExpectation
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ)
    (threshold other : Item → State → ℝ) :
    expectedDeltaValue (finiteWeightedExpectation weight)
        value threshold other =
      weightedDeltaValue weight value threshold other := rfl

/-- The abstract expected cost delta specializes to the finite weighted delta. -/
theorem expectedDeltaCost_finiteWeightedExpectation
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) :
    expectedDeltaCost (finiteWeightedExpectation weight)
        cost threshold other =
      weightedDeltaCost weight cost threshold other := rfl

/--
The value delta dominates `t` times the cost delta for any monotone finite
linear expectation.
-/
theorem mul_expectedDeltaCost_le_expectedDeltaValue
    {Item Outcome : Type*} [Fintype Item]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (value : Item → Outcome → ℝ) (cost : Item → ℝ)
    (threshold other : Item → Outcome → ℝ) (t : ℝ)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          cost item * t ≤ value item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          value item outcome ≤ cost item * t) :
    t * expectedDeltaCost expect cost threshold other ≤
      expectedDeltaValue expect value threshold other := by
  classical
  have hpoint :
      ∀ outcome,
        t *
            (∑ item : Item,
              cost item *
                (threshold item outcome - other item outcome)) ≤
          ∑ item : Item,
            (threshold item outcome - other item outcome) *
              value item outcome := by
    intro outcome
    calc
      t *
          (∑ item : Item,
            cost item *
              (threshold item outcome - other item outcome))
          =
          ∑ item : Item,
            (threshold item outcome - other item outcome) *
              (cost item * t) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro item _
        ring
      _ ≤
          ∑ item : Item,
            (threshold item outcome - other item outcome) *
              value item outcome := by
        refine Finset.sum_le_sum ?_
        intro item _
        exact delta_mul_bound_le_delta_mul_value
          (hpos item outcome) (hneg item outcome)
  have hmono :=
    FiniteLinearExpectation.monotone hlin
      (fun outcome =>
        t *
          (∑ item : Item,
            cost item *
              (threshold item outcome - other item outcome)))
      (fun outcome =>
        ∑ item : Item,
          (threshold item outcome - other item outcome) *
            value item outcome)
      hpoint
  have hscale :
      expect
          (fun outcome =>
            t *
              (∑ item : Item,
                cost item *
                  (threshold item outcome - other item outcome))) =
        t * expectedDeltaCost expect cost threshold other := by
    rw [FiniteLinearExpectation.const_mul hlin]
    rfl
  simpa [expectedDeltaValue, hscale] using hmono

/--
Equal expected cost implies the threshold policy has weakly higher expected
value under any monotone finite linear expectation.
-/
theorem expectedDeltaValue_nonneg_of_expectedDeltaCost_eq_zero
    {Item Outcome : Type*} [Fintype Item]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (value : Item → Outcome → ℝ) (cost : Item → ℝ)
    (threshold other : Item → Outcome → ℝ) (t : ℝ)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          cost item * t ≤ value item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          value item outcome ≤ cost item * t)
    (hcost : expectedDeltaCost expect cost threshold other = 0) :
    0 ≤ expectedDeltaValue expect value threshold other := by
  have hmain :=
    mul_expectedDeltaCost_le_expectedDeltaValue
      expect hlin value cost threshold other t hpos hneg
  rwa [hcost, mul_zero] at hmain

/--
Equal expected value and positive threshold imply the threshold policy has
weakly lower expected cost under any monotone finite linear expectation.
-/
theorem expectedDeltaCost_nonpos_of_expectedDeltaValue_eq_zero
    {Item Outcome : Type*} [Fintype Item]
    (expect : (Outcome → ℝ) → ℝ)
    (hlin : FiniteLinearExpectation expect)
    (value : Item → Outcome → ℝ) (cost : Item → ℝ)
    (threshold other : Item → Outcome → ℝ) (t : ℝ)
    (ht : 0 < t)
    (hpos :
      ∀ item outcome,
        0 < threshold item outcome - other item outcome →
          cost item * t ≤ value item outcome)
    (hneg :
      ∀ item outcome,
        threshold item outcome - other item outcome < 0 →
          value item outcome ≤ cost item * t)
    (hvalue : expectedDeltaValue expect value threshold other = 0) :
    expectedDeltaCost expect cost threshold other ≤ 0 := by
  have hmain :=
    mul_expectedDeltaCost_le_expectedDeltaValue
      expect hlin value cost threshold other t hpos hneg
  rw [hvalue] at hmain
  have hmain' :
      expectedDeltaCost expect cost threshold other * t ≤ 0 := by
    simpa [mul_comm] using hmain
  exact nonpos_of_mul_nonpos_left hmain' ht

/--
Equal cost implies the threshold policy has weakly higher weighted value.
-/
theorem weightedDeltaValue_nonneg_of_weightedDeltaCost_eq_zero
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) (t : ℝ)
    (hweight : ∀ state, 0 ≤ weight state)
    (hpos :
      ∀ item state,
        0 < threshold item state - other item state →
          cost item * t ≤ value item state)
    (hneg :
      ∀ item state,
        threshold item state - other item state < 0 →
          value item state ≤ cost item * t)
    (hcost : weightedDeltaCost weight cost threshold other = 0) :
    0 ≤ weightedDeltaValue weight value threshold other := by
  have hmain :=
    mul_weightedDeltaCost_le_weightedDeltaValue
      weight value cost threshold other t hweight hpos hneg
  rwa [hcost, mul_zero] at hmain

/--
Equal value and positive threshold imply the threshold policy has weakly lower
weighted cost.
-/
theorem weightedDeltaCost_nonpos_of_weightedDeltaValue_eq_zero
    {Item State : Type*} [Fintype Item] [Fintype State]
    (weight : State → ℝ) (value : Item → State → ℝ) (cost : Item → ℝ)
    (threshold other : Item → State → ℝ) (t : ℝ)
    (ht : 0 < t)
    (hweight : ∀ state, 0 ≤ weight state)
    (hpos :
      ∀ item state,
        0 < threshold item state - other item state →
          cost item * t ≤ value item state)
    (hneg :
      ∀ item state,
        threshold item state - other item state < 0 →
          value item state ≤ cost item * t)
    (hvalue : weightedDeltaValue weight value threshold other = 0) :
    weightedDeltaCost weight cost threshold other ≤ 0 := by
  have hmain :=
    mul_weightedDeltaCost_le_weightedDeltaValue
      weight value cost threshold other t hweight hpos hneg
  rw [hvalue] at hmain
  have hmain' :
      weightedDeltaCost weight cost threshold other * t ≤ 0 := by
    simpa [mul_comm] using hmain
  exact nonpos_of_mul_nonpos_left hmain' ht

/-! ## Finite threshold bracketing over score blocks -/

/-- Mass in score blocks strictly above a threshold. -/
def finiteScoreStrictAboveMass (scores : Finset ℝ) (mass : ℝ → ℝ)
    (threshold : ℝ) : ℝ :=
  ∑ score ∈ scores, if threshold < score then mass score else 0

/-- Mass in score blocks weakly above a threshold. -/
def finiteScoreClosedAboveMass (scores : Finset ℝ) (mass : ℝ → ℝ)
    (threshold : ℝ) : ℝ :=
  ∑ score ∈ scores, if threshold ≤ score then mass score else 0

/-- Total mass in a finite set of score blocks. -/
def finiteScoreTotalMass (scores : Finset ℝ) (mass : ℝ → ℝ) : ℝ :=
  ∑ score ∈ scores, mass score

theorem finiteScoreClosedAboveMass_eq_total_of_le_all
    {scores : Finset ℝ} {mass : ℝ → ℝ} {threshold : ℝ}
    (hle : ∀ score ∈ scores, threshold ≤ score) :
    finiteScoreClosedAboveMass scores mass threshold =
      finiteScoreTotalMass scores mass := by
  classical
  simp only [finiteScoreClosedAboveMass, finiteScoreTotalMass]
  refine Finset.sum_congr rfl ?_
  intro score hscore
  simp [hle score hscore]

theorem finiteScoreStrictAboveMass_eq_zero_of_no_above
    {scores : Finset ℝ} {mass : ℝ → ℝ} {threshold : ℝ}
    (hno : ∀ score ∈ scores, ¬ threshold < score) :
    finiteScoreStrictAboveMass scores mass threshold = 0 := by
  classical
  simp only [finiteScoreStrictAboveMass]
  exact Finset.sum_eq_zero fun score hscore => by
    simp [hno score hscore]

theorem finiteScoreClosedAboveMass_eq_strictAboveMass_of_min_above
    {scores : Finset ℝ} {mass : ℝ → ℝ} {threshold next : ℝ}
    (hnext_mem : next ∈ scores)
    (hthreshold_lt_next : threshold < next)
    (hnext_le :
      ∀ score ∈ scores, threshold < score → next ≤ score) :
    finiteScoreClosedAboveMass scores mass next =
      finiteScoreStrictAboveMass scores mass threshold := by
  classical
  simp only [finiteScoreClosedAboveMass, finiteScoreStrictAboveMass]
  refine Finset.sum_congr rfl ?_
  intro score hscore
  have hiff : next ≤ score ↔ threshold < score := by
    constructor
    · intro hle
      exact lt_of_lt_of_le hthreshold_lt_next hle
    · intro hlt
      exact hnext_le score hscore hlt
  by_cases hnext_score : next ≤ score
  · have hthreshold_score : threshold < score := hiff.mp hnext_score
    simp [hnext_score, hthreshold_score]
  · have hthreshold_not : ¬ threshold < score := by
      intro hlt
      exact hnext_score (hiff.mpr hlt)
    simp [hnext_score, hthreshold_not]

/--
Finite jump bracketing for threshold rules over score blocks.

If positive-mass score blocks are finite and a target lies between zero and the
total block mass, then the target lies in one of the jumps of the weak-upper
tail.  This is the reusable finite-support core behind boundary-randomized
threshold-attainment arguments.
-/
theorem exists_finiteScore_threshold_bracket
    (scores : Finset ℝ) (mass : ℝ → ℝ) (target : ℝ)
    (hscores_nonempty : scores.Nonempty)
    (hmass_pos : ∀ score ∈ scores, 0 < mass score)
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total : target ≤ finiteScoreTotalMass scores mass) :
    ∃ threshold ∈ scores,
      finiteScoreStrictAboveMass scores mass threshold ≤ target ∧
        target ≤ finiteScoreStrictAboveMass scores mass threshold +
          mass threshold := by
  classical
  let eligible : Finset ℝ :=
    scores.filter fun score =>
      target ≤ finiteScoreClosedAboveMass scores mass score
  have hmin_mem : scores.min' hscores_nonempty ∈ scores :=
    Finset.min'_mem scores hscores_nonempty
  have hclosed_min :
      finiteScoreClosedAboveMass scores mass (scores.min' hscores_nonempty) =
        finiteScoreTotalMass scores mass := by
    exact finiteScoreClosedAboveMass_eq_total_of_le_all
      (threshold := scores.min' hscores_nonempty)
      (fun score hscore => Finset.min'_le scores score hscore)
  have helig_nonempty : eligible.Nonempty := by
    refine ⟨scores.min' hscores_nonempty, ?_⟩
    simp only [eligible, Finset.mem_filter]
    exact ⟨hmin_mem, by simpa [hclosed_min] using htarget_le_total⟩
  let threshold : ℝ := eligible.max' helig_nonempty
  have hthreshold_eligible : threshold ∈ eligible :=
    Finset.max'_mem eligible helig_nonempty
  have hthreshold_eligible' :
      threshold ∈ scores ∧
        target ≤ finiteScoreClosedAboveMass scores mass threshold := by
    simpa [eligible] using hthreshold_eligible
  have hthreshold_mem : threshold ∈ scores := by
    exact hthreshold_eligible'.1
  have htarget_le_closed :
      target ≤ finiteScoreClosedAboveMass scores mass threshold := by
    exact hthreshold_eligible'.2
  have hstrict_le_target :
      finiteScoreStrictAboveMass scores mass threshold ≤ target := by
    let above : Finset ℝ := scores.filter fun score => threshold < score
    by_cases habove_nonempty : above.Nonempty
    · let next : ℝ := above.min' habove_nonempty
      have hnext_above : next ∈ above :=
        Finset.min'_mem above habove_nonempty
      have hnext_above' : next ∈ scores ∧ threshold < next := by
        simpa [above] using hnext_above
      have hnext_mem : next ∈ scores := by
        exact hnext_above'.1
      have hthreshold_lt_next : threshold < next := by
        exact hnext_above'.2
      have hnext_not_eligible : next ∉ eligible := by
        intro hnext_eligible
        have hle_next_threshold :
            next ≤ threshold := by
          simpa [threshold] using
            Finset.le_max' eligible next hnext_eligible
        exact (not_le_of_gt hthreshold_lt_next) hle_next_threshold
      have htarget_not_le_closed :
          ¬ target ≤ finiteScoreClosedAboveMass scores mass next := by
        intro hle
        exact hnext_not_eligible (by
          simp only [eligible, Finset.mem_filter]
          exact ⟨hnext_mem, hle⟩)
      have hclosed_next_lt_target :
          finiteScoreClosedAboveMass scores mass next < target :=
        lt_of_not_ge htarget_not_le_closed
      have hnext_le :
          ∀ score ∈ scores, threshold < score → next ≤ score := by
        intro score hscore hlt
        exact Finset.min'_le above score (by
          simp only [above, Finset.mem_filter]
          exact ⟨hscore, hlt⟩)
      have hclosed_eq :
          finiteScoreClosedAboveMass scores mass next =
            finiteScoreStrictAboveMass scores mass threshold :=
        finiteScoreClosedAboveMass_eq_strictAboveMass_of_min_above
          (scores := scores) (mass := mass) (threshold := threshold)
          (next := next) hnext_mem hthreshold_lt_next hnext_le
      linarith
    · have hno :
        ∀ score ∈ scores, ¬ threshold < score := by
        intro score hscore hlt
        exact habove_nonempty ⟨score, by
          simp only [above, Finset.mem_filter]
          exact ⟨hscore, hlt⟩⟩
      have hstrict_zero :
          finiteScoreStrictAboveMass scores mass threshold = 0 :=
        finiteScoreStrictAboveMass_eq_zero_of_no_above
          (scores := scores) (mass := mass) (threshold := threshold) hno
      linarith
  refine ⟨threshold, hthreshold_mem, hstrict_le_target, ?_⟩
  have hclosed_eq :
      finiteScoreClosedAboveMass scores mass threshold =
        finiteScoreStrictAboveMass scores mass threshold + mass threshold := by
    simp only [finiteScoreClosedAboveMass, finiteScoreStrictAboveMass]
    have hthreshold_in : threshold ∈ scores := hthreshold_mem
    have hsum_erase :
        (∑ score ∈ scores.erase threshold,
          if threshold ≤ score then mass score else 0) =
          (∑ score ∈ scores.erase threshold,
            if threshold < score then mass score else 0) := by
      refine Finset.sum_congr rfl ?_
      intro score hscore
      have hne : score ≠ threshold := by
        exact Finset.ne_of_mem_erase hscore
      have hle_iff : threshold ≤ score ↔ threshold < score := by
        constructor
        · intro hle
          exact lt_of_le_of_ne hle (Ne.symm hne)
        · exact le_of_lt
      by_cases hlt : threshold < score
      · simp [hlt, hle_iff.mpr hlt]
      · have hnle : ¬ threshold ≤ score := by
          intro hle
          exact hlt (hle_iff.mp hle)
        simp [hlt, hnle]
    have hsum_strict_erase :
        (∑ score ∈ scores.erase threshold,
          if threshold < score then mass score else 0) =
          (∑ score ∈ scores,
            if threshold < score then mass score else 0) := by
      have hsum :=
        Finset.sum_erase_add scores
          (fun score => if threshold < score then mass score else 0)
          hthreshold_in
      have hself : (if threshold < threshold then mass threshold else 0) = 0 := by
        simp
      simpa [hself] using hsum
    calc
      (∑ score ∈ scores, if threshold ≤ score then mass score else 0)
          =
          (∑ score ∈ scores.erase threshold,
            if threshold ≤ score then mass score else 0) +
            mass threshold := by
        simpa using
          (Finset.sum_erase_add scores
            (fun score => if threshold ≤ score then mass score else 0)
            hthreshold_in).symm
      _ =
          (∑ score ∈ scores.erase threshold,
            if threshold < score then mass score else 0) +
            mass threshold := by
        rw [hsum_erase]
      _ =
          (∑ score ∈ scores, if threshold < score then mass score else 0) +
            mass threshold := by
        rw [hsum_strict_erase]
      _ =
          finiteScoreStrictAboveMass scores mass threshold +
            mass threshold := by
        simp only [finiteScoreStrictAboveMass]
  simpa [hclosed_eq] using htarget_le_closed

/-! ## Finite threshold bracketing over atoms -/

/-- Mass of atoms whose score is strictly above a threshold. -/
def finiteAtomStrictAboveMass {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ) (threshold : ℝ) : ℝ :=
  ∑ atom : Atom, if threshold < score atom then mass atom else 0

/-- Mass of atoms whose score is exactly on a threshold boundary. -/
def finiteAtomBoundaryMass {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ) (threshold : ℝ) : ℝ :=
  ∑ atom : Atom, if score atom = threshold then mass atom else 0

/-- Mass of atoms whose score is weakly above a threshold. -/
def finiteAtomClosedAboveMass {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ) (threshold : ℝ) : ℝ :=
  ∑ atom : Atom, if threshold ≤ score atom then mass atom else 0

/-- Total finite atom mass. -/
def finiteAtomTotalMass {Atom : Type*} [Fintype Atom]
    (mass : Atom → ℝ) : ℝ :=
  ∑ atom : Atom, mass atom

theorem finiteAtomBoundaryMass_nonneg {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ)
    (hmass_nonneg : ∀ atom, 0 ≤ mass atom) (threshold : ℝ) :
    0 ≤ finiteAtomBoundaryMass score mass threshold := by
  classical
  simp only [finiteAtomBoundaryMass]
  exact Finset.sum_nonneg fun atom _ => by
    by_cases hscore : score atom = threshold
    · simp [hscore, hmass_nonneg atom]
    · simp [hscore]

theorem finiteAtomBoundaryMass_pos_of_mass_pos {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ)
    (hmass_nonneg : ∀ atom, 0 ≤ mass atom)
    {atom : Atom} (hmass_pos : 0 < mass atom) :
    0 < finiteAtomBoundaryMass score mass (score atom) := by
  classical
  have hterm_nonneg :
      ∀ x ∈ (Finset.univ : Finset Atom),
        0 ≤ (if score x = score atom then mass x else 0) := by
    intro x _
    by_cases hx : score x = score atom
    · simp [hx, hmass_nonneg x]
    · simp [hx]
  have hle :
      mass atom ≤
        ∑ x : Atom, if score x = score atom then mass x else 0 := by
    have hsingle :=
      Finset.single_le_sum hterm_nonneg (Finset.mem_univ atom)
    simpa using hsingle
  exact lt_of_lt_of_le hmass_pos hle

theorem finiteAtomClosedAboveMass_eq_total_of_le_positive_scores
    {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ) (threshold : ℝ)
    (hmass_nonneg : ∀ atom, 0 ≤ mass atom)
    (hle_positive :
      ∀ atom, 0 < mass atom → threshold ≤ score atom) :
    finiteAtomClosedAboveMass score mass threshold =
      finiteAtomTotalMass mass := by
  classical
  simp only [finiteAtomClosedAboveMass, finiteAtomTotalMass]
  refine Finset.sum_congr rfl ?_
  intro atom _
  by_cases hle : threshold ≤ score atom
  · simp [hle]
  · have hnot_pos : ¬ 0 < mass atom := by
      intro hpos
      exact hle (hle_positive atom hpos)
    have hmass_zero : mass atom = 0 :=
      le_antisymm (le_of_not_gt hnot_pos) (hmass_nonneg atom)
    simp [hle, hmass_zero]

theorem finiteAtomClosedAboveMass_eq_strictAboveMass_of_next_positive_score
    {Atom : Type*} [Fintype Atom]
    (score : Atom → ℝ) (mass : Atom → ℝ) (threshold next : ℝ)
    (hmass_nonneg : ∀ atom, 0 ≤ mass atom)
    (hthreshold_lt_next : threshold < next)
    (hnext_le_positive_above :
      ∀ atom, 0 < mass atom → threshold < score atom → next ≤ score atom) :
    finiteAtomClosedAboveMass score mass next =
      finiteAtomStrictAboveMass score mass threshold := by
  classical
  simp only [finiteAtomClosedAboveMass, finiteAtomStrictAboveMass]
  refine Finset.sum_congr rfl ?_
  intro atom _
  by_cases hnext_le : next ≤ score atom
  · have hthreshold_lt : threshold < score atom :=
      lt_of_lt_of_le hthreshold_lt_next hnext_le
    simp [hnext_le, hthreshold_lt]
  · by_cases hthreshold_lt : threshold < score atom
    · have hnot_pos : ¬ 0 < mass atom := by
        intro hpos
        exact hnext_le (hnext_le_positive_above atom hpos hthreshold_lt)
      have hmass_zero : mass atom = 0 :=
        le_antisymm (le_of_not_gt hnot_pos) (hmass_nonneg atom)
      simp [hnext_le, hthreshold_lt, hmass_zero]
    · simp [hnext_le, hthreshold_lt]

/--
Finite jump bracketing directly over atoms.

This version is convenient for threshold policies whose score blocks are
generated from finitely many weighted atoms.  Nonnegative masses make zero-mass
atoms harmless: they may have arbitrary scores and do not affect the bracket.
-/
theorem exists_finiteAtom_threshold_bracket
    {Atom : Type*} [Fintype Atom] (score : Atom → ℝ) (mass : Atom → ℝ)
    (target : ℝ)
    (hmass_nonneg : ∀ atom, 0 ≤ mass atom)
    (htotal_pos : 0 < finiteAtomTotalMass mass)
    (htarget_nonneg : 0 ≤ target)
    (htarget_le_total : target ≤ finiteAtomTotalMass mass) :
    ∃ threshold : ℝ,
      0 < finiteAtomBoundaryMass score mass threshold ∧
        finiteAtomStrictAboveMass score mass threshold ≤ target ∧
          target ≤ finiteAtomStrictAboveMass score mass threshold +
            finiteAtomBoundaryMass score mass threshold := by
  classical
  let positiveScores : Finset ℝ :=
    (Finset.univ.image score).filter fun threshold =>
      0 < finiteAtomBoundaryMass score mass threshold
  have hpositiveScores_nonempty : positiveScores.Nonempty := by
    have hzero_sum : (∑ atom : Atom, (0 : ℝ)) < ∑ atom : Atom, mass atom := by
      simpa [finiteAtomTotalMass] using htotal_pos
    rcases Finset.exists_lt_of_sum_lt hzero_sum with ⟨atom, _, hpos⟩
    refine ⟨score atom, ?_⟩
    simp only [positiveScores, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨⟨atom, rfl⟩,
      finiteAtomBoundaryMass_pos_of_mass_pos score mass hmass_nonneg hpos⟩
  let eligible : Finset ℝ :=
    positiveScores.filter fun threshold =>
      target ≤ finiteAtomClosedAboveMass score mass threshold
  have hmin_positive_mem :
      positiveScores.min' hpositiveScores_nonempty ∈ positiveScores :=
    Finset.min'_mem positiveScores hpositiveScores_nonempty
  have hmin_le_positive :
      ∀ atom, 0 < mass atom →
        positiveScores.min' hpositiveScores_nonempty ≤ score atom := by
    intro atom hpos
    have hscore_mem : score atom ∈ positiveScores := by
      simp only [positiveScores, Finset.mem_filter, Finset.mem_image,
        Finset.mem_univ, true_and]
      exact ⟨⟨atom, rfl⟩,
        finiteAtomBoundaryMass_pos_of_mass_pos score mass hmass_nonneg hpos⟩
    exact Finset.min'_le positiveScores (score atom) hscore_mem
  have hclosed_min :
      finiteAtomClosedAboveMass score mass
          (positiveScores.min' hpositiveScores_nonempty) =
        finiteAtomTotalMass mass :=
    finiteAtomClosedAboveMass_eq_total_of_le_positive_scores
      score mass (positiveScores.min' hpositiveScores_nonempty)
      hmass_nonneg hmin_le_positive
  have helig_nonempty : eligible.Nonempty := by
    refine ⟨positiveScores.min' hpositiveScores_nonempty, ?_⟩
    simp only [eligible, Finset.mem_filter]
    exact ⟨hmin_positive_mem, by simpa [hclosed_min] using htarget_le_total⟩
  let threshold : ℝ := eligible.max' helig_nonempty
  have hthreshold_eligible : threshold ∈ eligible :=
    Finset.max'_mem eligible helig_nonempty
  have hthreshold_eligible' :
      threshold ∈ positiveScores ∧
        target ≤ finiteAtomClosedAboveMass score mass threshold := by
    simpa [eligible] using hthreshold_eligible
  have hthreshold_boundary_pos :
      0 < finiteAtomBoundaryMass score mass threshold := by
    have hpositive :
        (∃ atom, score atom = threshold) ∧
          0 < finiteAtomBoundaryMass score mass threshold := by
      simpa [positiveScores] using hthreshold_eligible'.1
    exact hpositive.2
  have htarget_le_closed :
      target ≤ finiteAtomClosedAboveMass score mass threshold :=
    hthreshold_eligible'.2
  have hstrict_le_target :
      finiteAtomStrictAboveMass score mass threshold ≤ target := by
    let abovePositiveScores : Finset ℝ :=
      positiveScores.filter fun scoreValue => threshold < scoreValue
    by_cases habove_nonempty : abovePositiveScores.Nonempty
    · let next : ℝ := abovePositiveScores.min' habove_nonempty
      have hnext_above : next ∈ abovePositiveScores :=
        Finset.min'_mem abovePositiveScores habove_nonempty
      have hnext_above' : next ∈ positiveScores ∧ threshold < next := by
        simpa [abovePositiveScores] using hnext_above
      have hthreshold_lt_next : threshold < next := hnext_above'.2
      have hnext_not_eligible : next ∉ eligible := by
        intro hnext_eligible
        have hle_next_threshold : next ≤ threshold := by
          simpa [threshold] using
            Finset.le_max' eligible next hnext_eligible
        exact (not_le_of_gt hthreshold_lt_next) hle_next_threshold
      have hclosed_next_lt_target :
          finiteAtomClosedAboveMass score mass next < target := by
        have hnot :
            ¬ target ≤ finiteAtomClosedAboveMass score mass next := by
          intro hle
          exact hnext_not_eligible (by
            simp only [eligible, Finset.mem_filter]
            exact ⟨hnext_above'.1, hle⟩)
        exact lt_of_not_ge hnot
      have hnext_le_positive_above :
          ∀ atom, 0 < mass atom → threshold < score atom → next ≤ score atom := by
        intro atom hpos hlt
        have hscore_mem_positive : score atom ∈ positiveScores := by
          simp only [positiveScores, Finset.mem_filter, Finset.mem_image,
            Finset.mem_univ, true_and]
          exact ⟨⟨atom, rfl⟩,
            finiteAtomBoundaryMass_pos_of_mass_pos score mass hmass_nonneg hpos⟩
        exact Finset.min'_le abovePositiveScores (score atom) (by
          simp only [abovePositiveScores, Finset.mem_filter]
          exact ⟨hscore_mem_positive, hlt⟩)
      have hclosed_eq :
          finiteAtomClosedAboveMass score mass next =
            finiteAtomStrictAboveMass score mass threshold :=
        finiteAtomClosedAboveMass_eq_strictAboveMass_of_next_positive_score
          score mass threshold next hmass_nonneg hthreshold_lt_next
          hnext_le_positive_above
      linarith
    · have hno_positive_above :
          ∀ atom, 0 < mass atom → ¬ threshold < score atom := by
        intro atom hpos hlt
        have hscore_mem_positive : score atom ∈ positiveScores := by
          simp only [positiveScores, Finset.mem_filter, Finset.mem_image,
            Finset.mem_univ, true_and]
          exact ⟨⟨atom, rfl⟩,
            finiteAtomBoundaryMass_pos_of_mass_pos score mass hmass_nonneg hpos⟩
        exact habove_nonempty ⟨score atom, by
          simp only [abovePositiveScores, Finset.mem_filter]
          exact ⟨hscore_mem_positive, hlt⟩⟩
      have hstrict_zero :
          finiteAtomStrictAboveMass score mass threshold = 0 := by
        simp only [finiteAtomStrictAboveMass]
        exact Finset.sum_eq_zero fun atom _ => by
          by_cases hlt : threshold < score atom
          · have hnot_pos : ¬ 0 < mass atom :=
              fun hpos => hno_positive_above atom hpos hlt
            have hmass_zero : mass atom = 0 :=
              le_antisymm (le_of_not_gt hnot_pos) (hmass_nonneg atom)
            simp [hlt, hmass_zero]
          · simp [hlt]
      linarith
  refine ⟨threshold, hthreshold_boundary_pos, hstrict_le_target, ?_⟩
  have hclosed_eq :
      finiteAtomClosedAboveMass score mass threshold =
        finiteAtomStrictAboveMass score mass threshold +
          finiteAtomBoundaryMass score mass threshold := by
    simp only [finiteAtomClosedAboveMass, finiteAtomStrictAboveMass,
      finiteAtomBoundaryMass]
    calc
      (∑ atom : Atom, if threshold ≤ score atom then mass atom else 0)
          =
          ∑ atom : Atom,
            ((if threshold < score atom then mass atom else 0) +
              (if score atom = threshold then mass atom else 0)) := by
        refine Finset.sum_congr rfl ?_
        intro atom _
        by_cases hlt : threshold < score atom
        · have hne : score atom ≠ threshold := ne_of_gt hlt
          simp [hlt, hlt.le, hne]
        · by_cases heq : score atom = threshold
          · have hle : threshold ≤ score atom := by
              simpa [heq]
            simp [heq]
          · have hnle : ¬ threshold ≤ score atom := by
              intro hle
              exact heq (le_antisymm (le_of_not_gt hlt) hle)
            simp [hlt, heq, hnle]
      _ =
          (∑ atom : Atom, if threshold < score atom then mass atom else 0) +
            ∑ atom : Atom, if score atom = threshold then mass atom else 0 := by
        rw [Finset.sum_add_distrib]
  simpa [hclosed_eq] using htarget_le_closed

end

end Optimization
end AppliedModelingLib
