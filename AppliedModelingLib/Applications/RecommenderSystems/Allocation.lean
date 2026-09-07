import AppliedModelingLib.Applications.RecommenderSystems.Policy
import AppliedModelingLib.Foundations.Math.FiniteRounding
import AppliedModelingLib.Foundations.Math.FiniteSum
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators

namespace AppliedModelingLib

/--
A finite integer allocation over a finite class/type space `κ`.

This is the common representation behind the recommendation-diversity paper:
`count k` is the number of recommended items of type `k`.
-/
structure Allocation (κ : Type*) where
  count : κ → ℕ

namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Total number of allocated units. -/
def total (a : Allocation κ) : ℕ :=
  ∑ k, a.count k

/-- The positive-support classes/types in an allocation. -/
def support (a : Allocation κ) : Finset κ :=
  Finset.univ.filter fun k => a.count k ≠ 0

/-- `a` is an allocation of exactly `N` units. -/
def HasTotal (a : Allocation κ) (N : ℕ) : Prop :=
  a.total = N

/-- `a` is an allocation of at most `N` units. -/
def BoundedBy (a : Allocation κ) (N : ℕ) : Prop :=
  a.total ≤ N

/-- Real-valued representation share of class/type `k` in allocation `a`. -/
noncomputable def share (a : Allocation κ) (k : κ) : ℝ :=
  if h : a.total = 0 then 0 else (a.count k : ℝ) / (a.total : ℝ)

/-- Weighted finite objective over allocation counts. -/
noncomputable def objective
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) : ℝ :=
  ∑ k, weight k * valueOfCount k (a.count k)

/--
Move one unit from `src` to `dst`. If `src = dst`, the allocation is unchanged.
If the source count is zero, natural-number subtraction leaves it at zero; callers should
use `CanMoveOne` when they need an honest transfer.
-/
def moveOne (a : Allocation κ) (src dst : κ) : Allocation κ where
  count := fun k =>
    if src = dst then a.count k
    else if k = src then a.count k - 1
    else if k = dst then a.count k + 1
    else a.count k

/-- There is at least one unit available to move out of `src`. -/
def CanMoveOne (a : Allocation κ) (src : κ) : Prop :=
  0 < a.count src

/-- Marginal value of increasing a count from `q` to `q + 1`. -/
noncomputable def marginal (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  valueOfCount k (q + 1) - valueOfCount k q

/-- Nonnegative marginal values for every class/type. -/
def HasNonnegativeMarginals (valueOfCount : κ → ℕ → ℝ) : Prop :=
  ∀ k q, 0 ≤ marginal valueOfCount k q

/-- Diminishing marginal returns for every class/type. -/
def HasDiminishingReturns (valueOfCount : κ → ℕ → ℝ) : Prop :=
  ∀ k q, marginal valueOfCount k (q + 1) ≤ marginal valueOfCount k q

@[simp] theorem total_mk (f : κ → ℕ) :
    total ({ count := f } : Allocation κ) = ∑ k, f k := rfl

@[simp] theorem mem_support (a : Allocation κ) (k : κ) :
    k ∈ support a ↔ a.count k ≠ 0 := by
  simp [support]

/-- Each class count is bounded by the total allocation size. -/
theorem count_le_total (a : Allocation κ) (k : κ) :
    a.count k ≤ a.total := by
  unfold total
  exact Finset.single_le_sum
    (by intro _ _; exact Nat.zero_le _)
    (Finset.mem_univ k)

/--
Finite-prefix scaled-count bound from a positive weight floor.

If a fixed-total allocation has total below `threshold` and every coordinate
weight is at least `weightFloor > 0`, then any two scaled counts differ by at
most `2 * threshold / weightFloor`.
-/
theorem pairwise_scaled_abs_le_of_total_lt
    (a : Allocation κ) (weight : κ → ℝ) {N threshold : ℕ} {weightFloor : ℝ}
    (htotal : HasTotal a N) (hNlt : N < threshold)
    (hfloor_pos : 0 < weightFloor)
    (hfloor_le : ∀ k, weightFloor ≤ weight k) :
    ∀ i j,
      |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤
        2 * ((threshold : ℝ) / weightFloor) := by
  intro i j
  let U : ℝ := (threshold : ℝ) / weightFloor
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact div_nonneg (Nat.cast_nonneg threshold) (le_of_lt hfloor_pos)
  have hweight_pos : ∀ k, 0 < weight k := fun k =>
    lt_of_lt_of_le hfloor_pos (hfloor_le k)
  have hupper : ∀ k, (a.count k : ℝ) / weight k ≤ U := by
    intro k
    have hcount_le_total := count_le_total a k
    have hcount_le_N : a.count k ≤ N := by
      have htotal_eq : a.total = N := htotal
      simpa [htotal_eq] using hcount_le_total
    have hcount_le_threshold : (a.count k : ℝ) ≤ (threshold : ℝ) := by
      exact_mod_cast (le_trans hcount_le_N (le_of_lt hNlt))
    dsimp [U]
    exact div_le_div₀ (Nat.cast_nonneg threshold) hcount_le_threshold
      hfloor_pos (hfloor_le k)
  have hnonneg : ∀ k, 0 ≤ (a.count k : ℝ) / weight k := by
    intro k
    exact div_nonneg (Nat.cast_nonneg (a.count k)) (le_of_lt (hweight_pos k))
  rw [abs_le]
  constructor
  · have hlow :
        -U ≤ (a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j := by
      linarith [hnonneg i, hupper j]
    have hU_le : U ≤ 2 * U := by linarith
    dsimp [U] at hlow hU_le
    linarith
  · have hupp :
        (a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j ≤ U := by
      linarith [hupper i, hnonneg j]
    have hU_le : U ≤ 2 * U := by linarith
    dsimp [U] at hupp hU_le
    linarith

/--
If the total count is larger than `card κ * K`, then some coordinate count is
larger than `K`.
-/
theorem exists_count_gt_of_card_mul_lt_total
    (a : Allocation κ) {K : ℕ}
    (hgt : Fintype.card κ * K < a.total) :
    ∃ k : κ, K < a.count k := by
  by_contra hnone
  push Not at hnone
  have hsum_le : a.total ≤ Fintype.card κ * K := by
    unfold total
    calc
      (∑ k : κ, a.count k)
          ≤ ∑ _k : κ, K := by
            exact Finset.sum_le_sum (fun k _ => hnone k)
      _ = Fintype.card κ * K := by
            simp [Finset.sum_const]
  exact (not_lt_of_ge hsum_le) hgt

@[simp] theorem share_of_total_zero (a : Allocation κ) (k : κ)
    (h : a.total = 0) :
    share a k = 0 := by
  simp [share, h]

theorem share_eq_div_of_total_ne_zero (a : Allocation κ) (k : κ)
    (h : a.total ≠ 0) :
    share a k = (a.count k : ℝ) / (a.total : ℝ) := by
  simp [share, h]

@[simp] theorem objective_mk (f : κ → ℕ) (weight : κ → ℝ)
    (valueOfCount : κ → ℕ → ℝ) :
    objective ({ count := f } : Allocation κ) weight valueOfCount =
      ∑ k, weight k * valueOfCount k (f k) := rfl

@[simp] theorem marginal_apply (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) :
    marginal valueOfCount k q = valueOfCount k (q + 1) - valueOfCount k q := rfl

/-- Linear value-of-count function with a fixed per-unit value for each type. -/
def linearValueOfCount (perUnitValue : κ → ℝ) : κ → ℕ → ℝ :=
  fun k q => (q : ℝ) * perUnitValue k

/-- Allocation putting all `N` units on one type. -/
def allOnTypeAllocation (N : ℕ) (best : κ) : Allocation κ where
  count := fun k => if k = best then N else 0

@[simp] theorem linearValueOfCount_zero
    (perUnitValue : κ → ℝ) (k : κ) :
    linearValueOfCount perUnitValue k 0 = 0 := by
  simp [linearValueOfCount]

@[simp] theorem allOnTypeAllocation_self
    (N : ℕ) (best : κ) :
    (allOnTypeAllocation N best).count best = N := by
  simp [allOnTypeAllocation]

theorem allOnTypeAllocation_of_ne
    (N : ℕ) {best k : κ} (hne : k ≠ best) :
    (allOnTypeAllocation N best).count k = 0 := by
  simp [allOnTypeAllocation, hne]

@[simp] theorem allOnTypeAllocation_total
    (N : ℕ) (best : κ) :
    total (allOnTypeAllocation N best) = N := by
  classical
  unfold total allOnTypeAllocation
  simp

theorem objective_linearValueOfCount_eq_sum_count_mul_score
    (weight perUnitValue : κ → ℝ) (a : Allocation κ) :
    objective a weight (linearValueOfCount perUnitValue) =
      ∑ k : κ, (a.count k : ℝ) * (weight k * perUnitValue k) := by
  unfold objective linearValueOfCount
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

/-- Weighted forward marginal gain from adding one unit to coordinate `k`. -/
noncomputable def weightedForwardMarginal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  weight k * marginal valueOfCount k q

/--
Weighted value lost by removing the `q`-th unit from coordinate `k`.

The value is set to `0` at `q = 0`; exchange theorems that model an actual
transfer separately assume `CanMoveOne a k`.
-/
noncomputable def weightedBackwardMarginal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) : ℝ :=
  if h : q = 0 then 0 else weight k * (valueOfCount k q - valueOfCount k (q - 1))

/-- A one-unit exchange loses no more at `src` than it gains at `dst`. -/
def ExchangeCondition
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (a : Allocation κ) (src dst : κ) : Prop :=
  weightedBackwardMarginal weight valueOfCount src (a.count src) ≤
    weightedForwardMarginal weight valueOfCount dst (a.count dst)

/-- `a` maximizes a weighted separable count objective among allocations of total `N`. -/
def IsOptimalAtTotal
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (N : ℕ) (a : Allocation κ) : Prop :=
  HasTotal a N ∧
    ∀ b : Allocation κ, HasTotal b N →
      objective b weight valueOfCount ≤ objective a weight valueOfCount

/--
For a linear objective, putting all mass on a maximizing type is optimal among
allocations with the same total.
-/
theorem allOnTypeAllocation_isOptimalAtTotal_linearValueOfCount
    (weight perUnitValue : κ → ℝ) (N : ℕ) (best : κ)
    (hbest : ∀ k, weight k * perUnitValue k ≤ weight best * perUnitValue best) :
    IsOptimalAtTotal weight (linearValueOfCount perUnitValue) N
      (allOnTypeAllocation N best) := by
  constructor
  · exact allOnTypeAllocation_total N best
  · intro b hb
    have hsum_counts : (∑ k : κ, (b.count k : ℝ)) = (N : ℝ) := by
      rw [← Nat.cast_sum]
      exact_mod_cast hb
    rw [objective_linearValueOfCount_eq_sum_count_mul_score]
    rw [objective_linearValueOfCount_eq_sum_count_mul_score]
    calc
      (∑ k : κ, (b.count k : ℝ) * (weight k * perUnitValue k))
          ≤ ∑ k : κ,
              (b.count k : ℝ) * (weight best * perUnitValue best) :=
            Finset.sum_le_sum (fun k _ =>
              mul_le_mul_of_nonneg_left (hbest k) (Nat.cast_nonneg _))
      _ = (N : ℝ) * (weight best * perUnitValue best) := by
            rw [← Finset.sum_mul, hsum_counts]
      _ = ∑ k : κ,
              ((allOnTypeAllocation N best).count k : ℝ) *
                (weight k * perUnitValue k) := by
            symm
            unfold allOnTypeAllocation
            change
              (∑ k : κ,
                ((if k = best then N else 0 : ℕ) : ℝ) *
                  (weight k * perUnitValue k)) =
                (N : ℝ) * (weight best * perUnitValue best)
            simp

@[simp] theorem weightedForwardMarginal_apply
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (k : κ) (q : ℕ) :
    weightedForwardMarginal weight valueOfCount k q =
      weight k * marginal valueOfCount k q := rfl

/-- Moving one unit from a positive source to a distinct destination preserves total size. -/
theorem total_moveOne_eq (a : Allocation κ)
    {src dst : κ} (hne : src ≠ dst) (hcan : CanMoveOne a src) :
    total (moveOne a src dst) = total a := by
  classical
  unfold total
  have hsum :
      (∑ k : κ, ((moveOne a src dst).count k : ℝ)) =
        (∑ k : κ, (a.count k : ℝ)) +
          (((moveOne a src dst).count src : ℝ) - (a.count src : ℝ)) +
          (((moveOne a src dst).count dst : ℝ) - (a.count dst : ℝ)) := by
    exact AppliedModelingLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
      (f := fun k : κ => ((moveOne a src dst).count k : ℝ))
      (g := fun k : κ => (a.count k : ℝ))
      (a := src) (b := dst) hne
      (by
        intro x hxsrc hxdst
        unfold moveOne
        simp [hne, hxsrc, hxdst])
  have hreal : ((∑ k : κ, (moveOne a src dst).count k : ℕ) : ℝ) =
      ((∑ k : κ, a.count k : ℕ) : ℝ) := by
    norm_num only [Nat.cast_sum]
    rw [hsum]
    unfold moveOne
    have hle : 1 ≤ a.count src := Nat.succ_le_of_lt hcan
    have hsrc_sub : ((a.count src - 1 : ℕ) : ℝ) = (a.count src : ℝ) - 1 := by
      have hnat : a.count src - 1 + 1 = a.count src := Nat.sub_add_cancel hle
      have hcast := congrArg (fun q : ℕ => (q : ℝ)) hnat
      norm_num at hcast
      linarith
    simp [hne, hne.symm]
    rw [hsrc_sub]
    ring
  exact_mod_cast hreal

/--
Exact objective accounting for one valid exchange: the destination gains its
forward marginal and the source loses its backward marginal.
-/
theorem objective_moveOne_eq
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    {src dst : κ} (hne : src ≠ dst) (hcan : CanMoveOne a src) :
    objective (moveOne a src dst) weight valueOfCount =
      objective a weight valueOfCount -
        weightedBackwardMarginal weight valueOfCount src (a.count src) +
        weightedForwardMarginal weight valueOfCount dst (a.count dst) := by
  classical
  unfold objective
  have hsum :
      (∑ k : κ,
          weight k * valueOfCount k ((moveOne a src dst).count k)) =
        (∑ k : κ, weight k * valueOfCount k (a.count k)) +
          (weight src * valueOfCount src ((moveOne a src dst).count src) -
            weight src * valueOfCount src (a.count src)) +
          (weight dst * valueOfCount dst ((moveOne a src dst).count dst) -
            weight dst * valueOfCount dst (a.count dst)) := by
    exact AppliedModelingLib.FiniteSum.sum_eq_sum_add_sub_add_sub_of_eq_off
      (f := fun k : κ => weight k * valueOfCount k ((moveOne a src dst).count k))
      (g := fun k : κ => weight k * valueOfCount k (a.count k))
      (a := src) (b := dst) hne
      (by
        intro x hxsrc hxdst
        unfold moveOne
        simp [hne, hxsrc, hxdst])
  rw [hsum]
  unfold moveOne weightedBackwardMarginal weightedForwardMarginal marginal
  have hsrc_ne_zero : ¬ a.count src = 0 := ne_of_gt hcan
  simp [hne, hne.symm, hsrc_ne_zero]
  ring

/-- Exact marginal accounting turns the exchange condition into weak improvement. -/
theorem objective_le_objective_moveOne_of_exchangeCondition
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    {src dst : κ} (hne : src ≠ dst) (hcan : CanMoveOne a src)
    (hcond : ExchangeCondition weight valueOfCount a src dst) :
    objective a weight valueOfCount ≤
      objective (moveOne a src dst) weight valueOfCount := by
  rw [objective_moveOne_eq (a := a) (weight := weight)
    (valueOfCount := valueOfCount) hne hcan]
  unfold ExchangeCondition at hcond
  linarith

/-- A valid one-unit exchange from a fixed-total optimum cannot improve the objective. -/
theorem objective_moveOne_le_of_isOptimalAtTotal
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (N : ℕ)
    {src dst : κ} (hopt : IsOptimalAtTotal weight valueOfCount N a)
    (hne : src ≠ dst) (hcan : CanMoveOne a src) :
    objective (moveOne a src dst) weight valueOfCount ≤
      objective a weight valueOfCount := by
  exact hopt.2 (moveOne a src dst) (by
    change total (moveOne a src dst) = N
    rw [total_moveOne_eq (a := a) hne hcan]
    exact hopt.1)

/--
First-order finite optimality condition: at an optimum, adding to `dst` cannot
gain more than removing from a positive, distinct `src` would lose.
-/
theorem weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (N : ℕ)
    {src dst : κ} (hopt : IsOptimalAtTotal weight valueOfCount N a)
    (hne : src ≠ dst) (hcan : CanMoveOne a src) :
    weightedForwardMarginal weight valueOfCount dst (a.count dst) ≤
      weightedBackwardMarginal weight valueOfCount src (a.count src) := by
  have hno :=
    objective_moveOne_le_of_isOptimalAtTotal
      (a := a) (weight := weight) (valueOfCount := valueOfCount)
      (N := N) hopt hne hcan
  rw [objective_moveOne_eq (a := a) (weight := weight)
    (valueOfCount := valueOfCount) hne hcan] at hno
  linarith

/--
For a linear objective, a type whose per-unit score is strictly below another
type's score receives zero count in every optimum.
-/
theorem count_eq_zero_of_isOptimalAtTotal_linearValueOfCount_of_strict_score_lt
    {weight perUnitValue : κ → ℝ} {N : ℕ} {a : Allocation κ} {k best : κ}
    (hopt : IsOptimalAtTotal weight (linearValueOfCount perUnitValue) N a)
    (hstrict : weight k * perUnitValue k < weight best * perUnitValue best) :
    a.count k = 0 := by
  by_contra hne_zero
  have hpos : 0 < a.count k := Nat.pos_of_ne_zero hne_zero
  have hk_ne_best : k ≠ best := by
    intro h
    rw [h] at hstrict
    exact (lt_irrefl (weight best * perUnitValue best)) hstrict
  have hle :=
    weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (a := a) (weight := weight) (valueOfCount := linearValueOfCount perUnitValue)
      (N := N) hopt hk_ne_best hpos
  have hforward :
      weightedForwardMarginal weight (linearValueOfCount perUnitValue)
          best (a.count best) =
        weight best * perUnitValue best := by
    unfold weightedForwardMarginal marginal linearValueOfCount
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have hbackward :
      weightedBackwardMarginal weight (linearValueOfCount perUnitValue)
          k (a.count k) =
        weight k * perUnitValue k := by
    unfold weightedBackwardMarginal linearValueOfCount
    rw [dif_neg hpos.ne']
    have hsucc : a.count k = (a.count k - 1) + 1 := by omega
    nth_rewrite 1 [hsucc]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  rw [hforward, hbackward] at hle
  exact not_le_of_gt hstrict hle

/--
If every scaled-count gap above `error * N` would make the source backward
marginal strictly smaller than the destination forward marginal, then the
finite FOC at an optimum bounds every pairwise scaled-count gap.

The `objectiveWeight` used in the objective may differ from the `scaledWeight`
used for the target profile.
-/
theorem pairwise_scaled_abs_le_of_large_gap_backward_lt_forward
    (a : Allocation κ) (objectiveWeight scaledWeight : κ → ℝ)
    (valueOfCount : κ → ℕ → ℝ) (N : ℕ) {error : ℝ}
    (hscaledWeight_pos : ∀ k, 0 < scaledWeight k)
    (herror_total_nonneg : 0 ≤ error * (N : ℝ))
    (hopt : IsOptimalAtTotal objectiveWeight valueOfCount N a)
    (hlarge :
      ∀ src dst,
        error * (N : ℝ) <
          (a.count src : ℝ) / scaledWeight src -
            (a.count dst : ℝ) / scaledWeight dst →
        weightedBackwardMarginal objectiveWeight valueOfCount src (a.count src) <
          weightedForwardMarginal objectiveWeight valueOfCount dst (a.count dst)) :
    ∀ src dst,
      |(a.count src : ℝ) / scaledWeight src -
        (a.count dst : ℝ) / scaledWeight dst| ≤ error * (N : ℝ) := by
  intro src dst
  have no_large_gap :
      ¬ error * (N : ℝ) <
        (a.count src : ℝ) / scaledWeight src -
          (a.count dst : ℝ) / scaledWeight dst := by
    intro hgap
    have hdiff_pos :
        0 <
          (a.count src : ℝ) / scaledWeight src -
            (a.count dst : ℝ) / scaledWeight dst :=
      lt_of_le_of_lt herror_total_nonneg hgap
    have hdst_nonneg :
        0 ≤ (a.count dst : ℝ) / scaledWeight dst :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hscaledWeight_pos dst))
    have hsrc_div_pos : 0 < (a.count src : ℝ) / scaledWeight src := by
      linarith
    have hsrc_pos : 0 < a.count src := by
      by_contra hnot
      have hzero : a.count src = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hsrc_div_pos
      simp at hsrc_div_pos
    have hne : src ≠ dst := by
      intro hsame
      subst dst
      have hneg : error * (N : ℝ) < 0 := by
        simpa using hgap
      exact (not_lt_of_ge herror_total_nonneg) hneg
    have hfoc :=
      weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
        (a := a) (weight := objectiveWeight) (valueOfCount := valueOfCount)
        (N := N) hopt hne hsrc_pos
    have hdom := hlarge src dst hgap
    exact (not_lt_of_ge hfoc) hdom
  have hupper :
      (a.count src : ℝ) / scaledWeight src -
          (a.count dst : ℝ) / scaledWeight dst ≤ error * (N : ℝ) :=
    le_of_not_gt no_large_gap
  have no_large_gap_rev :
      ¬ error * (N : ℝ) <
        (a.count dst : ℝ) / scaledWeight dst -
          (a.count src : ℝ) / scaledWeight src := by
    intro hgap
    have hdiff_pos :
        0 <
          (a.count dst : ℝ) / scaledWeight dst -
            (a.count src : ℝ) / scaledWeight src :=
      lt_of_le_of_lt herror_total_nonneg hgap
    have hsrc_nonneg :
        0 ≤ (a.count src : ℝ) / scaledWeight src :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt (hscaledWeight_pos src))
    have hdst_div_pos : 0 < (a.count dst : ℝ) / scaledWeight dst := by
      linarith
    have hdst_pos : 0 < a.count dst := by
      by_contra hnot
      have hzero : a.count dst = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero] at hdst_div_pos
      simp at hdst_div_pos
    have hne : dst ≠ src := by
      intro hsame
      subst src
      have hneg : error * (N : ℝ) < 0 := by
        simpa using hgap
      exact (not_lt_of_ge herror_total_nonneg) hneg
    have hfoc :=
      weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
        (a := a) (weight := objectiveWeight) (valueOfCount := valueOfCount)
        (N := N) hopt hne hdst_pos
    have hdom := hlarge dst src hgap
    exact (not_lt_of_ge hfoc) hdom
  have hlower :
      -(error * (N : ℝ)) ≤
        (a.count src : ℝ) / scaledWeight src -
          (a.count dst : ℝ) / scaledWeight dst := by
    have hrev :
        (a.count dst : ℝ) / scaledWeight dst -
            (a.count src : ℝ) / scaledWeight src ≤ error * (N : ℝ) :=
      le_of_not_gt no_large_gap_rev
    linarith
  rw [abs_le]
  exact ⟨hlower, hupper⟩

/-- Diminishing returns make marginal values antitone in the count. -/
theorem marginal_antitone_of_diminishing
    (valueOfCount : κ → ℕ → ℝ) (hDR : HasDiminishingReturns valueOfCount)
    (k : κ) {q r : ℕ} (hqr : q ≤ r) :
    marginal valueOfCount k r ≤ marginal valueOfCount k q := by
  exact Nat.le_induction (by rfl)
    (fun n _ ih => le_trans (hDR k n) ih) r hqr

/-- Nonnegative weights preserve antitonicity of forward weighted marginals. -/
theorem weightedForwardMarginal_antitone_of_diminishing
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (hDR : HasDiminishingReturns valueOfCount) (hweight_nonneg : ∀ k, 0 ≤ weight k)
    (k : κ) {q r : ℕ} (hqr : q ≤ r) :
    weightedForwardMarginal weight valueOfCount k r ≤
      weightedForwardMarginal weight valueOfCount k q := by
  unfold weightedForwardMarginal
  exact mul_le_mul_of_nonneg_left
    (marginal_antitone_of_diminishing valueOfCount hDR k hqr) (hweight_nonneg k)

/-- A positive backward marginal is the previous forward marginal. -/
theorem weightedBackwardMarginal_eq_weightedForwardMarginal_pred
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (k : κ) {q : ℕ} (hq : 0 < q) :
    weightedBackwardMarginal weight valueOfCount k q =
      weightedForwardMarginal weight valueOfCount k (q - 1) := by
  unfold weightedBackwardMarginal weightedForwardMarginal marginal
  have hq_ne : ¬ q = 0 := ne_of_gt hq
  have hq_cancel : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  simp [hq_ne, hq_cancel]

/--
If every one-count gap would make the high coordinate's last forward marginal
strictly smaller than the low coordinate's next forward marginal, then an
optimum has pairwise counts differing by at most one.
-/
theorem count_le_succ_of_cross_strict_antitone_forwardMarginal
    (a : Allocation κ) (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (N : ℕ)
    (hopt : IsOptimalAtTotal weight valueOfCount N a)
    (hstrict :
      ∀ src dst q r,
        q < r →
          weightedForwardMarginal weight valueOfCount src r <
            weightedForwardMarginal weight valueOfCount dst q) :
    ∀ src dst : κ, a.count src ≤ a.count dst + 1 := by
  intro src dst
  by_contra hnot
  have hdst_succ_lt : a.count dst + 1 < a.count src :=
    Nat.lt_of_not_ge hnot
  have hdst_lt_pred : a.count dst < a.count src - 1 :=
    (Nat.lt_sub_iff_add_lt).mpr hdst_succ_lt
  have hcan : CanMoveOne a src :=
    (Nat.succ_pos (a.count dst)).trans hdst_succ_lt
  have hne : src ≠ dst := by
    intro hsame
    subst dst
    exact hnot (Nat.le_succ _)
  have hfoc :=
    weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (a := a) (weight := weight) (valueOfCount := valueOfCount)
      (N := N) hopt hne hcan
  rw [weightedBackwardMarginal_eq_weightedForwardMarginal_pred
    (weight := weight) (valueOfCount := valueOfCount) src hcan] at hfoc
  exact (not_lt_of_ge hfoc)
    (hstrict src dst (a.count dst) (a.count src - 1) hdst_lt_pred)

/--
Under diminishing returns, a later backward marginal is bounded by any earlier
forward marginal when the earlier count is at least one step below it.
-/
theorem weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (hDR : HasDiminishingReturns valueOfCount) (hweight_nonneg : ∀ k, 0 ≤ weight k)
    (k : κ) {q r : ℕ} (hrq : r + 1 ≤ q) :
    weightedBackwardMarginal weight valueOfCount k q ≤
      weightedForwardMarginal weight valueOfCount k r := by
  have hq_pos : 0 < q := lt_of_lt_of_le (Nat.succ_pos r) hrq
  rw [weightedBackwardMarginal_eq_weightedForwardMarginal_pred
    (weight := weight) (valueOfCount := valueOfCount) k hq_pos]
  have hr_pred : r ≤ q - 1 := by omega
  exact weightedForwardMarginal_antitone_of_diminishing
    weight valueOfCount hDR hweight_nonneg k hr_pred

/--
A strict exchange certificate between integer lower/upper anchors.

If adding to any high coordinate at the upper anchor is still strictly worse
than removing from any positive low coordinate at the lower anchor, finite
optimality and diminishing returns rule out a high/low rounding crossing.
-/
def StrictRoundingExchangeCertificateBetween
    (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ)
    (lower upper : Allocation κ) : Prop :=
  ∀ high low,
    0 < lower.count low →
      weightedForwardMarginal weight valueOfCount high (upper.count high) <
        weightedBackwardMarginal weight valueOfCount low (lower.count low)

/--
Strict exchange dominance between lower/upper anchors yields the generic
no-crossing condition needed by finite rounding arguments.
-/
theorem noRoundingCrossingBetween_of_strictExchangeCertificate
    (a lower upper : Allocation κ) (weight : κ → ℝ)
    (valueOfCount : κ → ℕ → ℝ) (N : ℕ)
    (hopt : IsOptimalAtTotal weight valueOfCount N a)
    (hDR : HasDiminishingReturns valueOfCount)
    (hweight_nonneg : ∀ k, 0 ≤ weight k)
    (horder : ∀ k, lower.count k ≤ upper.count k)
    (hcert : StrictRoundingExchangeCertificateBetween weight valueOfCount lower upper) :
    AppliedModelingLib.FiniteRounding.NoRoundingCrossingBetween
      (fun k : κ => a.count k)
      (fun k : κ => lower.count k)
      (fun k : κ => upper.count k) := by
  intro high low
  rintro ⟨h_high, h_low⟩
  have h_low_pos : 0 < lower.count low :=
    lt_of_le_of_lt (Nat.zero_le _) h_low
  have h_can : CanMoveOne a high :=
    lt_of_lt_of_le (Nat.succ_pos _) h_high
  have hne : high ≠ low := by
    rintro rfl
    have hle : upper.count high + 1 ≤ upper.count high :=
      le_trans h_high
        (le_trans (Nat.le_of_succ_le h_low) (horder high))
    exact (Nat.not_succ_le_self (upper.count high)) hle
  have h_foc :=
    weightedForwardMarginal_le_weightedBackwardMarginal_of_optimum
      (a := a) (weight := weight) (valueOfCount := valueOfCount)
      (N := N) hopt hne h_can
  have h_high_bound :
      weightedBackwardMarginal weight valueOfCount high (a.count high) ≤
        weightedForwardMarginal weight valueOfCount high (upper.count high) :=
    weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
      weight valueOfCount hDR hweight_nonneg high h_high
  have h_low_bound :
      weightedBackwardMarginal weight valueOfCount low (lower.count low) ≤
        weightedForwardMarginal weight valueOfCount low (a.count low) :=
    weightedBackwardMarginal_le_weightedForwardMarginal_of_diminishing
      weight valueOfCount hDR hweight_nonneg low h_low
  have h_cert_eval := hcert high low h_low_pos
  linarith

end Allocation
end AppliedModelingLib

namespace AppliedModelingLib
namespace Allocation

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Representation shares are always nonnegative. -/
theorem share_nonneg (a : Allocation κ) (k : κ) :
    0 ≤ share a k := by
  by_cases h : a.total = 0
  · simp [share, h]
  · rw [share_eq_div_of_total_ne_zero (a := a) (k := k) h]
    exact div_nonneg (by positivity) (by positivity)

/-- If the total allocation is nonzero, representation shares sum to one. -/
theorem sum_share_eq_one_of_total_ne_zero (a : Allocation κ)
    (h : a.total ≠ 0) :
    ∑ k, share a k = 1 := by
  have hreal : (a.total : ℝ) ≠ 0 := by exact_mod_cast h
  have hsum : (∑ k, (a.count k : ℝ)) = (a.total : ℝ) := by
    simp [total]
  calc
    ∑ k, share a k = ∑ k, (a.count k : ℝ) / (a.total : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [share_eq_div_of_total_ne_zero (a := a) (k := k) h]
    _ = (∑ k, (a.count k : ℝ)) / (a.total : ℝ) := by
      rw [div_eq_mul_inv]
      simp_rw [div_eq_mul_inv]
      simpa using (Finset.sum_mul (s := (Finset.univ : Finset κ))
        (f := fun k => (a.count k : ℝ)) (a := (a.total : ℝ)⁻¹)).symm
    _ = (a.total : ℝ) / (a.total : ℝ) := by
      rw [hsum]
    _ = 1 := by
      field_simp [hreal]

/-- A positive count has positive representation share when the total is nonzero. -/
theorem share_pos_of_count_pos (a : Allocation κ) (k : κ)
    (hcount : 0 < a.count k) :
    0 < share a k := by
  have htotal : a.total ≠ 0 := by
    intro hzero
    have hsumzero : ∑ x, a.count x = 0 := by simpa [total] using hzero
    have hk_le : a.count k ≤ ∑ x, a.count x := by
      exact Finset.single_le_sum (by intro _ _; exact Nat.zero_le _) (Finset.mem_univ k)
    omega
  rw [share_eq_div_of_total_ne_zero (a := a) (k := k) htotal]
  exact div_pos (by exact_mod_cast hcount) (by positivity)

/--
Pairwise bounded scaled counts imply bounded distance from the weighted target.

If all scaled quantities `count k / weight k` are within `C` of one another,
then each count is within `C * weight k` of the allocation with shares
proportional to `weight`.
-/
theorem count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded
    [Nonempty κ]
    (a : Allocation κ) (weight : κ → ℝ) {N C : ℝ}
    (hN : (∑ i : κ, (a.count i : ℝ)) = N)
    (hweight_pos : ∀ i, 0 < weight i)
    (hC : 0 ≤ C)
    (hpair :
      ∀ i j,
        |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤ C) :
    ∀ k,
      |(a.count k : ℝ) -
        weight k * (N / ∑ i : κ, weight i)| ≤ C * weight k := by
  classical
  let y : κ → ℝ := fun i => (a.count i : ℝ) / weight i
  have hWpos : 0 < ∑ i : κ, weight i := by
    exact Finset.sum_pos (fun i _ => hweight_pos i) Finset.univ_nonempty
  have hy_sum : (∑ i : κ, weight i * y i) = N := by
    calc
      (∑ i : κ, weight i * y i)
          = ∑ i : κ, (a.count i : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            dsimp [y]
            field_simp [y, (ne_of_gt (hweight_pos i))]
      _ = N := hN
  intro k
  have hlower_point : ∀ j, y k - C ≤ y j := by
    intro j
    have h := (abs_le.mp (hpair k j)).2
    linarith
  have hupper_point : ∀ j, y j ≤ y k + C := by
    intro j
    have h := (abs_le.mp (hpair k j)).1
    linarith
  have hlower_sum :
      (∑ j : κ, weight j) * (y k - C) ≤ N := by
    rw [← hy_sum]
    calc
      (∑ j : κ, weight j) * (y k - C)
          = ∑ j : κ, weight j * (y k - C) := by
            rw [Finset.sum_mul]
      _ ≤ ∑ j : κ, weight j * y j := by
            exact Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hlower_point j) (le_of_lt (hweight_pos j)))
  have hupper_sum :
      N ≤ (∑ j : κ, weight j) * (y k + C) := by
    rw [← hy_sum]
    calc
      (∑ j : κ, weight j * y j)
          ≤ ∑ j : κ, weight j * (y k + C) := by
            exact Finset.sum_le_sum (fun j _ =>
              mul_le_mul_of_nonneg_left (hupper_point j) (le_of_lt (hweight_pos j)))
      _ = (∑ j : κ, weight j) * (y k + C) := by
            rw [Finset.sum_mul]
  have hlow_avg : y k - C ≤ N / ∑ i : κ, weight i := by
    exact (le_div_iff₀ hWpos).2 (by simpa [mul_comm] using hlower_sum)
  have hupp_avg : N / ∑ i : κ, weight i ≤ y k + C := by
    exact (div_le_iff₀ hWpos).2 (by simpa [mul_comm] using hupper_sum)
  have hy_close : |y k - N / ∑ i : κ, weight i| ≤ C := by
    rw [abs_le]
    constructor <;> linarith
  have hcount_eq : (a.count k : ℝ) = weight k * y k := by
    dsimp [y]
    field_simp [y, (ne_of_gt (hweight_pos k))]
  calc
    |(a.count k : ℝ) - weight k * (N / ∑ i : κ, weight i)|
        = |weight k * (y k - N / ∑ i : κ, weight i)| := by
          rw [hcount_eq]
          ring_nf
    _ = weight k * |y k - N / ∑ i : κ, weight i| := by
          rw [abs_mul, abs_of_pos (hweight_pos k)]
    _ ≤ weight k * C := by
          exact mul_le_mul_of_nonneg_left hy_close (le_of_lt (hweight_pos k))
    _ = C * weight k := by ring

/--
Pairwise bounded scaled counts imply that the allocation shares are close to
the weight-proportional target profile, with the coordinate-specific error
`C * weight k / N`.
-/
theorem share_abs_sub_weighted_target_le_scaled_weight_of_pairwise_scaled_bounded
    [Nonempty κ] (a : Allocation κ) (weight : κ → ℝ)
    {N : ℕ} {C : ℝ}
    (hN : HasTotal a N) (hNpos : 0 < N)
    (hweight_pos : ∀ k, 0 < weight k) (hC : 0 ≤ C)
    (hpair :
      ∀ i j,
        |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤ C) :
    ∀ k,
      |share a k - weight k / ∑ i : κ, weight i| ≤
        C * weight k / (N : ℝ) := by
  intro k
  have hN_ne_nat : N ≠ 0 := Nat.ne_of_gt hNpos
  have htotal_ne : a.total ≠ 0 := by
    rw [hN]
    exact hN_ne_nat
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast hN_ne_nat
  have hNpos_real : 0 < (N : ℝ) := by exact_mod_cast hNpos
  let W : ℝ := ∑ i : κ, weight i
  have hWpos : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos (fun i _ => hweight_pos i) Finset.univ_nonempty
  have hW_ne : W ≠ 0 := ne_of_gt hWpos
  have hNsum : (∑ i : κ, (a.count i : ℝ)) = (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hN
  have hclose :=
    count_abs_sub_weighted_average_le_of_pairwise_scaled_bounded
      (a := a) (weight := weight) (N := (N : ℝ)) (C := C)
      hNsum hweight_pos hC hpair k
  have htarget :
      weight k * ((N : ℝ) / W) = (N : ℝ) * (weight k / W) := by
    ring
  rw [htarget] at hclose
  calc
    |share a k - weight k / ∑ i : κ, weight i|
        = |(a.count k : ℝ) / (N : ℝ) - weight k / W| := by
            rw [share_eq_div_of_total_ne_zero (a := a) (k := k) htotal_ne, hN]
    _ = |((a.count k : ℝ) - (N : ℝ) * (weight k / W)) / (N : ℝ)| := by
            congr 1
            field_simp [hN_ne, hW_ne]
    _ = |(a.count k : ℝ) - (N : ℝ) * (weight k / W)| / (N : ℝ) := by
            rw [abs_div, abs_of_pos hNpos_real]
    _ ≤ C * weight k / (N : ℝ) :=
            div_le_div_of_nonneg_right hclose (le_of_lt hNpos_real)

/--
A uniform version of
`share_abs_sub_weighted_target_le_scaled_weight_of_pairwise_scaled_bounded`,
using total target weight as a coordinate-independent error bound.
-/
theorem share_abs_sub_weighted_target_le_total_weight_of_pairwise_scaled_bounded
    [Nonempty κ] (a : Allocation κ) (weight : κ → ℝ)
    {N : ℕ} {C : ℝ}
    (hN : HasTotal a N) (hNpos : 0 < N)
    (hweight_pos : ∀ k, 0 < weight k) (hC : 0 ≤ C)
    (hpair :
      ∀ i j,
        |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤ C) :
    ∀ k,
      |share a k - weight k / ∑ i : κ, weight i| ≤
        C * (∑ i : κ, weight i) / (N : ℝ) := by
  intro k
  have hfirst :=
    share_abs_sub_weighted_target_le_scaled_weight_of_pairwise_scaled_bounded
      (a := a) (weight := weight) (N := N) (C := C)
      hN hNpos hweight_pos hC hpair k
  have hweight_le_sum :
      weight k ≤ ∑ i : κ, weight i := by
    exact Finset.single_le_sum
      (fun i _ => le_of_lt (hweight_pos i)) (Finset.mem_univ k)
  have hC_weight_le_sum :
      C * weight k ≤ C * ∑ i : κ, weight i :=
    mul_le_mul_of_nonneg_left hweight_le_sum hC
  have hNpos_real : 0 < (N : ℝ) := by exact_mod_cast hNpos
  exact le_trans hfirst
    (div_le_div_of_nonneg_right hC_weight_le_sum (le_of_lt hNpos_real))

/--
If pairwise scaled-count gaps are at most `error * N`, then shares are within
`error * totalWeight` of the weight-proportional target profile.
-/
theorem share_abs_sub_weighted_target_le_error_total_weight_of_pairwise_scaled
    [Nonempty κ] (a : Allocation κ) (weight : κ → ℝ)
    {N : ℕ} {error : ℝ}
    (hN : HasTotal a N) (hNpos : 0 < N)
    (hweight_pos : ∀ k, 0 < weight k) (herror_nonneg : 0 ≤ error)
    (hpair :
      ∀ i j,
        |(a.count i : ℝ) / weight i - (a.count j : ℝ) / weight j| ≤
          error * (N : ℝ)) :
    ∀ k,
      |share a k - weight k / ∑ i : κ, weight i| ≤
        error * ∑ i : κ, weight i := by
  intro k
  have hNpos_real : 0 < (N : ℝ) := by exact_mod_cast hNpos
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hNpos_real
  have hC_nonneg : 0 ≤ error * (N : ℝ) :=
    mul_nonneg herror_nonneg (le_of_lt hNpos_real)
  have h :=
    share_abs_sub_weighted_target_le_total_weight_of_pairwise_scaled_bounded
      (a := a) (weight := weight) (N := N) (C := error * (N : ℝ))
      hN hNpos hweight_pos hC_nonneg hpair k
  calc
    |share a k - weight k / ∑ i : κ, weight i|
        ≤ (error * (N : ℝ)) * (∑ i : κ, weight i) / (N : ℝ) := h
    _ = error * ∑ i : κ, weight i := by
          field_simp [hN_ne]

/--
If all coordinate counts are pairwise bounded by `C`, then each count is within
`C` of the uniform real average `N / card κ`.
-/
theorem count_abs_sub_uniform_average_le_C_of_pairwise_bounded
    [Nonempty κ]
    (a : Allocation κ) {N : ℕ} {C : ℝ}
    (hN : a.total = N)
    (hbound : ∀ i j : κ, (a.count i : ℝ) ≤ (a.count j : ℝ) + C)
    (k : κ) :
    |(a.count k : ℝ) - (N : ℝ) / (Fintype.card κ : ℝ)| ≤ C := by
  have hcard_pos_nat : 0 < Fintype.card κ := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast hcard_pos_nat
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hsum_counts : (∑ j : κ, (a.count j : ℝ)) = (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hN
  rw [abs_le]
  constructor
  · field_simp [hcard_ne]
    have hsum : (∑ j : κ, (a.count j : ℝ)) ≤
        ∑ j : κ, ((a.count k : ℝ) + C) := by
      apply Finset.sum_le_sum
      intro j _
      exact hbound j k
    simp [Finset.sum_const, nsmul_eq_mul] at hsum
    linarith
  · field_simp [hcard_ne]
    have hsum : (∑ j : κ, (a.count k : ℝ)) ≤
        ∑ j : κ, ((a.count j : ℝ) + C) := by
      apply Finset.sum_le_sum
      intro j _
      exact hbound k j
    rw [Finset.sum_add_distrib] at hsum
    simp [hsum_counts, Finset.sum_const, nsmul_eq_mul] at hsum
    linarith

/--
If all coordinate counts differ pairwise by at most one, then each count is
within one of the uniform real average `N / card κ`.
-/
theorem count_abs_sub_uniform_average_le_one_of_pairwise_balanced
    [Nonempty κ]
    (a : Allocation κ) {N : ℕ}
    (hN : a.total = N)
    (hbal : ∀ i j : κ, a.count i ≤ a.count j + 1)
    (k : κ) :
    |(a.count k : ℝ) - (N : ℝ) / (Fintype.card κ : ℝ)| ≤ 1 := by
  have hcard_pos_nat : 0 < Fintype.card κ := Fintype.card_pos
  have hcard_pos : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast hcard_pos_nat
  have hcard_ne : (Fintype.card κ : ℝ) ≠ 0 := ne_of_gt hcard_pos
  have hsum_counts : (∑ j : κ, (a.count j : ℝ)) = (N : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast hN
  have hsum_add_one :
      (∑ j : κ, ((a.count j : ℝ) + 1)) =
        (N : ℝ) + (Fintype.card κ : ℝ) := by
    calc
      (∑ j : κ, ((a.count j : ℝ) + 1))
          = (∑ j : κ, (a.count j : ℝ)) +
              ∑ _j : κ, (1 : ℝ) := by
              simpa using (Finset.sum_add_distrib
                (s := (Finset.univ : Finset κ))
                (f := fun j : κ => (a.count j : ℝ))
                (g := fun _j : κ => (1 : ℝ)))
      _ = (N : ℝ) + (Fintype.card κ : ℝ) := by
          simp [hsum_counts, Finset.sum_const, nsmul_eq_mul]
  have hsum_const_count :
      (∑ _j : κ, (a.count k : ℝ)) =
        (Fintype.card κ : ℝ) * (a.count k : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hsum_const_count_add_one :
      (∑ _j : κ, ((a.count k : ℝ) + 1)) =
        (Fintype.card κ : ℝ) * (a.count k : ℝ) +
          (Fintype.card κ : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  have hupper_sum :
      ∑ j : κ, (a.count k : ℝ) ≤
        ∑ j : κ, ((a.count j : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact_mod_cast hbal k j
  have hupper :
      (Fintype.card κ : ℝ) * (a.count k : ℝ) ≤
        (N : ℝ) + (Fintype.card κ : ℝ) := by
    rw [← hsum_const_count, ← hsum_add_one]
    exact hupper_sum
  have hlower_sum :
      ∑ j : κ, (a.count j : ℝ) ≤
        ∑ j : κ, ((a.count k : ℝ) + 1) := by
    refine Finset.sum_le_sum ?_
    intro j _hj
    exact_mod_cast hbal j k
  have hlower :
      (N : ℝ) ≤
        (Fintype.card κ : ℝ) * (a.count k : ℝ) +
          (Fintype.card κ : ℝ) := by
    rw [← hsum_counts, ← hsum_const_count_add_one]
    exact hlower_sum
  rw [abs_le]
  constructor
  · field_simp [hcard_ne]
    nlinarith
  · field_simp [hcard_ne]
    nlinarith

/--
Finite code for allocations of exactly `N` units.

Each coordinate is stored as a `Fin (N + 1)`, and the subtype proof records
that the decoded allocation has total `N`.
-/
abbrev FeasibleCode (κ : Type*) [Fintype κ] (N : ℕ) :=
  { f : κ → Fin (N + 1) // ∑ k : κ, (f k).val = N }

namespace FeasibleCode

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Decode a feasible allocation code into an allocation. -/
def toAllocation {N : ℕ} (x : FeasibleCode κ N) : Allocation κ where
  count := fun k => (x.1 k).val

@[simp] theorem toAllocation_count {N : ℕ}
    (x : FeasibleCode κ N) (k : κ) :
    x.toAllocation.count k = (x.1 k).val := rfl

/-- Decoded feasible codes have the requested total. -/
theorem toAllocation_hasTotal {N : ℕ}
    (x : FeasibleCode κ N) :
    HasTotal x.toAllocation N := by
  exact x.2

/-- A fixed-total allocation can be encoded in the finite search space. -/
def ofHasTotal {N : ℕ} (a : Allocation κ)
    (hfeas : HasTotal a N) : FeasibleCode κ N :=
  ⟨fun k =>
      ⟨a.count k, Nat.lt_succ_of_le
        (by
          have hle := count_le_total a k
          have htotal : a.total = N := hfeas
          rw [htotal] at hle
          exact hle)⟩,
    by
      simpa [HasTotal] using hfeas⟩

@[simp] theorem toAllocation_ofHasTotal {N : ℕ}
    (a : Allocation κ) (hfeas : HasTotal a N) :
    (ofHasTotal a hfeas).toAllocation = a := by
  cases a
  rfl

/-- A canonical feasible code putting all `N` units on one available coordinate. -/
noncomputable def singleton {N : ℕ} [Nonempty κ] :
    FeasibleCode κ N := by
  classical
  let k0 : κ := Classical.choice inferInstance
  refine ⟨fun k =>
    if k = k0 then ⟨N, Nat.lt_succ_self N⟩ else ⟨0, Nat.succ_pos N⟩, ?_⟩
  simp only [apply_ite]
  calc
    (∑ k : κ, (if k = k0 then N else 0 : ℕ))
        = ∑ k ∈ (Finset.univ : Finset κ),
            (if k = k0 then N else 0 : ℕ) := rfl
    _ = (if k0 = k0 then N else 0 : ℕ) := by
        exact Finset.sum_eq_single k0
          (by
            intro b _ hb
            simp [hb])
          (by
            intro hnot
            simp at hnot)
    _ = N := by
        simp

end FeasibleCode

/-- A finite fixed-total count-allocation problem always has a maximizer. -/
theorem exists_isOptimalAtTotal
    [Nonempty κ] (weight : κ → ℝ) (valueOfCount : κ → ℕ → ℝ) (N : ℕ) :
    ∃ a : Allocation κ,
      HasTotal a N ∧
        ∀ b : Allocation κ, HasTotal b N →
          objective b weight valueOfCount ≤ objective a weight valueOfCount := by
  classical
  let instCode : Nonempty (FeasibleCode κ N) :=
    ⟨FeasibleCode.singleton (κ := κ) (N := N)⟩
  haveI : Nonempty (FeasibleCode κ N) := instCode
  let score : FeasibleCode κ N → ℝ :=
    fun x => objective x.toAllocation weight valueOfCount
  obtain ⟨xmax, _hxmem, hxmax⟩ :=
    Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset (FeasibleCode κ N)))
      (H := Finset.univ_nonempty) (f := score)
  refine ⟨xmax.toAllocation, ?_, ?_⟩
  · exact FeasibleCode.toAllocation_hasTotal xmax
  · intro b hb
    let xb : FeasibleCode κ N :=
      FeasibleCode.ofHasTotal b hb
    have hle : score xb ≤ AppliedModelingLib.finiteMax score :=
      AppliedModelingLib.le_finiteMax score xb
    unfold AppliedModelingLib.finiteMax at hle
    rw [hxmax] at hle
    simpa [score, xb] using hle

end Allocation
end AppliedModelingLib
