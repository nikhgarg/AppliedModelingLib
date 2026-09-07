import LG24ServiceLevelAgreements.ProposedParitySymmetry
import Mathlib.Tactic

/-!
# Proposed theory: constructive all-request alignment bound

This file formalizes the quantitative replacement for the invalid continuity
argument in the July 2026 GPT revision memo.  At fixed admitted load, each
cell's all-request burden is affine and strictly increasing in its conditional
delay.  Starting from an efficiency endpoint, we can therefore raise the delay
of every better-served cell until it reaches the largest burden in its
category.  Reciprocal-capacity feasibility is coordinatewise upward closed, so
this repair is feasible.  Its exact efficiency cost gives a constructive upper
bound on the price of all-request equity.

The theorem is stated for arbitrary nonempty finite Borough sets.  It is more
general than the paper model: only an affine positive delay slope, nonnegative
reciprocal-capacity coefficients, and nonnegative arrival weights are needed.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Finite category maxima, minima, and the alignment repair -/

/-- Largest burden in a category over a finite nonempty Borough set. -/
def finiteCategoryMaximum
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) (k : Category) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (burden k)

/-- Smallest burden in a category over a finite nonempty Borough set. -/
def finiteCategoryMinimum
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) (k : Category) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (burden k)

theorem burden_le_finiteCategoryMaximum
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) (k : Category) (b : Borough) :
    burden k b ≤ finiteCategoryMaximum burden k := by
  classical
  exact Finset.le_sup' (burden k) (Finset.mem_univ b)

theorem finiteCategoryMinimum_le_burden
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) (k : Category) (b : Borough) :
    finiteCategoryMinimum burden k ≤ burden k b := by
  classical
  exact Finset.inf'_le (burden k) (Finset.mem_univ b)

/-- A generic cell burden that is affine in conditional delay. -/
def affineDelayBurden
    {Category Borough : Type*}
    (offset slope delay : Category → Borough → ℝ) :
    Category → Borough → ℝ :=
  fun k b ↦ offset k b + slope k b * delay k b

/--
Raise each cell's delay just enough to reach the pre-repair category maximum.
-/
def finiteAlignmentRepair
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (offset slope delay : Category → Borough → ℝ) :
    Category → Borough → ℝ :=
  fun k b ↦ delay k b +
    (finiteCategoryMaximum (affineDelayBurden offset slope delay) k -
      affineDelayBurden offset slope delay k b) / slope k b

/-- The repair raises, rather than lowers, every delay. -/
theorem finiteAlignmentRepair_ge
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {offset slope delay : Category → Borough → ℝ}
    (hslope : ∀ k b, 0 < slope k b) :
    ∀ k b, delay k b ≤ finiteAlignmentRepair offset slope delay k b := by
  intro k b
  unfold finiteAlignmentRepair
  have hgap : 0 ≤
      finiteCategoryMaximum (affineDelayBurden offset slope delay) k -
        affineDelayBurden offset slope delay k b :=
    sub_nonneg.mpr (burden_le_finiteCategoryMaximum
      (affineDelayBurden offset slope delay) k b)
  exact le_add_of_nonneg_right (div_nonneg hgap (hslope k b).le)

/-- Every repaired cell has exactly its category's pre-repair maximum burden. -/
theorem affineDelayBurden_finiteAlignmentRepair
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    {offset slope delay : Category → Borough → ℝ}
    (hslope : ∀ k b, 0 < slope k b) (k : Category) (b : Borough) :
    affineDelayBurden offset slope
        (finiteAlignmentRepair offset slope delay) k b =
      finiteCategoryMaximum (affineDelayBurden offset slope delay) k := by
  change offset k b + slope k b *
      (delay k b +
        (finiteCategoryMaximum (affineDelayBurden offset slope delay) k -
          affineDelayBurden offset slope delay k b) / slope k b) = _
  field_simp [(hslope k b).ne']
  simp only [affineDelayBurden]
  ring

/-! ## Upward closure of reciprocal-capacity feasibility -/

/-- Matrix form of the memo's finite reciprocal-capacity feasible set. -/
def finiteMatrixReciprocalCapacityFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (tail : Category → Borough → ℝ) (excessCapacity : ℝ)
    (delay : Category → Borough → ℝ) : Prop :=
  (∀ k b, 0 < delay k b) ∧
    (∑ k, ∑ b, tail k b / delay k b) ≤ excessCapacity

/-- Increasing positive delays weakly decreases reciprocal capacity use. -/
theorem finiteMatrix_reciprocalCapacityUse_antitone
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail x y : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hx : ∀ k b, 0 < x k b)
    (hxy : ∀ k b, x k b ≤ y k b) :
    (∑ k, ∑ b, tail k b / y k b) ≤
      ∑ k, ∑ b, tail k b / x k b := by
  classical
  apply Finset.sum_le_sum
  intro k _hk
  apply Finset.sum_le_sum
  intro b _hb
  have hy : 0 < y k b := lt_of_lt_of_le (hx k b) (hxy k b)
  apply (div_le_div_iff₀ hy (hx k b)).2
  exact mul_le_mul_of_nonneg_left (hxy k b) (htail k b)

/-- Reciprocal-capacity feasibility is coordinatewise upward closed. -/
theorem finiteMatrixReciprocalCapacityFeasible_of_le
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → Borough → ℝ} {excessCapacity : ℝ}
    {x y : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hx : finiteMatrixReciprocalCapacityFeasible tail excessCapacity x)
    (hxy : ∀ k b, x k b ≤ y k b) :
    finiteMatrixReciprocalCapacityFeasible tail excessCapacity y := by
  constructor
  · intro k b
    exact lt_of_lt_of_le (hx.1 k b) (hxy k b)
  · exact (finiteMatrix_reciprocalCapacityUse_antitone
      htail hx.1 hxy).trans hx.2

/-- The matrix reciprocal-capacity feasible set is convex. -/
theorem finiteMatrixReciprocalCapacityFeasible_mix
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {tail : Category → Borough → ℝ} {excessCapacity t : ℝ}
    {x y : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : finiteMatrixReciprocalCapacityFeasible tail excessCapacity x)
    (hy : finiteMatrixReciprocalCapacityFeasible tail excessCapacity y) :
    finiteMatrixReciprocalCapacityFeasible tail excessCapacity
      (fun k b ↦ t * x k b + (1 - t) * y k b) := by
  constructor
  · intro k b
    exact delayMix_pos ht0 ht1 (hx.1 k) (hy.1 k) b
  · calc
      (∑ k, ∑ b, tail k b /
          (t * x k b + (1 - t) * y k b)) ≤
          ∑ k, ∑ b,
            (t * (tail k b / x k b) +
              (1 - t) * (tail k b / y k b)) := by
        apply Finset.sum_le_sum
        intro k _hk
        apply Finset.sum_le_sum
        intro b _hb
        exact weighted_reciprocal_mix_le
          (htail k b) ht0 ht1 (hx.1 k b) (hy.1 k b)
      _ = t * (∑ k, ∑ b, tail k b / x k b) +
          (1 - t) * (∑ k, ∑ b, tail k b / y k b) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ excessCapacity := by
        have htx := mul_le_mul_of_nonneg_left hx.2 ht0
        have hty := mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr ht1)
        nlinarith

/-! ## Exact constructive price bound -/

/-- Arrival-weighted sum of cell burdens. -/
def finiteArrivalWeightedBurden
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival burden : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, arrival k b * burden k b

/-- Exact objective increase incurred by the category-maximum repair. -/
def finiteAlignmentGap
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival burden : Category → Borough → ℝ) : ℝ :=
  ∑ k, ∑ b, arrival k b *
    (finiteCategoryMaximum burden k - burden k b)

/-- Nonnegative weighted scalarization of efficiency and all-request equity. -/
def finiteFixedLoadScalarization
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (efficiencyWeight equityWeight : ℝ)
    (arrival offset slope delay : Category → Borough → ℝ) : ℝ :=
  efficiencyWeight * finiteArrivalWeightedBurden arrival
      (affineDelayBurden offset slope delay) +
    equityWeight * finiteAllRequestRangeObjective
      (affineDelayBurden offset slope delay)

/-- Affine burden profiles commute with delay mixing. -/
theorem affineDelayBurden_mix
    {Category Borough : Type*}
    (offset slope x y : Category → Borough → ℝ) (t : ℝ) :
    affineDelayBurden offset slope
        (fun k b ↦ t * x k b + (1 - t) * y k b) =
      fun k b ↦ t * affineDelayBurden offset slope x k b +
        (1 - t) * affineDelayBurden offset slope y k b := by
  funext k b
  unfold affineDelayBurden
  ring

/-- Arrival-weighted burden is affine under burden mixing. -/
theorem finiteArrivalWeightedBurden_mix
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (arrival x y : Category → Borough → ℝ) (t : ℝ) :
    finiteArrivalWeightedBurden arrival
        (fun k b ↦ t * x k b + (1 - t) * y k b) =
      t * finiteArrivalWeightedBurden arrival x +
        (1 - t) * finiteArrivalWeightedBurden arrival y := by
  classical
  unfold finiteArrivalWeightedBurden
  calc
    ∑ k, ∑ b, arrival k b *
        (t * x k b + (1 - t) * y k b) =
        ∑ k, ∑ b,
          (t * (arrival k b * x k b) +
            (1 - t) * (arrival k b * y k b)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = t * (∑ k, ∑ b, arrival k b * x k b) +
        (1 - t) * (∑ k, ∑ b, arrival k b * y k b) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Every nonnegative weighted fixed-load tradeoff objective is convex. -/
theorem finiteFixedLoadScalarization_mix_le
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {efficiencyWeight equityWeight t : ℝ}
    (arrival offset slope x y : Category → Borough → ℝ)
    (_heffWeight : 0 ≤ efficiencyWeight)
    (hequityWeight : 0 ≤ equityWeight)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteFixedLoadScalarization efficiencyWeight equityWeight
        arrival offset slope
        (fun k b ↦ t * x k b + (1 - t) * y k b) ≤
      t * finiteFixedLoadScalarization efficiencyWeight equityWeight
          arrival offset slope x +
        (1 - t) * finiteFixedLoadScalarization efficiencyWeight equityWeight
          arrival offset slope y := by
  have heff := finiteArrivalWeightedBurden_mix arrival
    (affineDelayBurden offset slope x)
    (affineDelayBurden offset slope y) t
  have hequity := finiteAllRequestRangeObjective_mix_le
    (affineDelayBurden offset slope x)
    (affineDelayBurden offset slope y) ht0 ht1
  unfold finiteFixedLoadScalarization
  rw [affineDelayBurden_mix, heff]
  have hequityMul := mul_le_mul_of_nonneg_left hequity hequityWeight
  nlinarith

/-- The arbitrary-Borough range objective is nonnegative. -/
theorem finiteAllRequestRangeObjective_nonneg
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) :
    0 ≤ finiteAllRequestRangeObjective burden := by
  classical
  unfold finiteAllRequestRangeObjective
  exact Finset.sum_nonneg fun k _hk ↦ finiteBoroughRange_nonneg (burden k)

/-- The alignment repair has zero all-request range in every category. -/
theorem finiteAlignmentRepair_zero_range
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {offset slope delay : Category → Borough → ℝ}
    (hslope : ∀ k b, 0 < slope k b) :
    finiteAllRequestRangeObjective
      (affineDelayBurden offset slope
        (finiteAlignmentRepair offset slope delay)) = 0 := by
  apply finiteAllRequestRangeObjective_eq_zero_of_constant
    (level := finiteCategoryMaximum (affineDelayBurden offset slope delay))
  exact affineDelayBurden_finiteAlignmentRepair hslope

/-- The repair's efficiency increase is exactly the weighted alignment gap. -/
theorem finiteArrivalWeightedBurden_repair_sub
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival offset slope delay : Category → Borough → ℝ)
    (hslope : ∀ k b, 0 < slope k b) :
    finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope
          (finiteAlignmentRepair offset slope delay)) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope delay) =
      finiteAlignmentGap arrival (affineDelayBurden offset slope delay) := by
  classical
  unfold finiteArrivalWeightedBurden finiteAlignmentGap
  simp_rw [affineDelayBurden_finiteAlignmentRepair hslope]
  simp_rw [mul_sub, Finset.sum_sub_distrib]

/--
The category-maximum repair is an attained minimizer of the all-request range
objective.  This is a genuine existence theorem: it constructs the minimizer
from any feasible delay profile, rather than assuming that an equitable
endpoint has already been selected.

The result deliberately concerns the primary equity objective only.  Selecting
the most efficient point among all zero-range profiles is a separate
continuous optimization problem and requires its own attainment assumptions.
-/
theorem finiteAlignmentRepair_is_equityMinimizer
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail offset slope delay : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hslope : ∀ k b, 0 < slope k b)
    (hdelay : finiteMatrixReciprocalCapacityFeasible
      tail excessCapacity delay) :
    MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (affineDelayBurden offset slope z))
      (finiteAlignmentRepair offset slope delay) := by
  have hrepair : finiteMatrixReciprocalCapacityFeasible tail excessCapacity
      (finiteAlignmentRepair offset slope delay) := by
    apply finiteMatrixReciprocalCapacityFeasible_of_le htail hdelay
    exact finiteAlignmentRepair_ge hslope
  refine ⟨hrepair, ?_⟩
  intro z _hz
  change finiteAllRequestRangeObjective
      (affineDelayBurden offset slope
        (finiteAlignmentRepair offset slope delay)) ≤
    finiteAllRequestRangeObjective (affineDelayBurden offset slope z)
  rw [finiteAlignmentRepair_zero_range hslope]
  exact finiteAllRequestRangeObjective_nonneg _

/--
Constructive equity endpoint and exact price certificate.  Whenever an
efficiency endpoint exists, the category-maximum repair supplies an explicit
feasible equity minimizer.  Its efficiency increase is nonnegative and is
exactly the finite alignment gap.  Thus the constructive price bound itself
does not depend on existence of a lexicographic tie-break minimizer.
-/
theorem finite_fixedLoadAlignment_constructive_equity_endpoint
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival offset slope : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    {efficient : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hslope : ∀ k b, 0 < slope k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) efficient) :
    ∃ aligned : Category → Borough → ℝ,
      MinimizesOn
        (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
        (fun z ↦ finiteAllRequestRangeObjective
          (affineDelayBurden offset slope z)) aligned ∧
      finiteAllRequestRangeObjective
          (affineDelayBurden offset slope aligned) = 0 ∧
      0 ≤ finiteArrivalWeightedBurden arrival
          (affineDelayBurden offset slope aligned) -
        finiteArrivalWeightedBurden arrival
          (affineDelayBurden offset slope efficient) ∧
      finiteArrivalWeightedBurden arrival
          (affineDelayBurden offset slope aligned) -
        finiteArrivalWeightedBurden arrival
          (affineDelayBurden offset slope efficient) =
        finiteAlignmentGap arrival
          (affineDelayBurden offset slope efficient) := by
  refine ⟨finiteAlignmentRepair offset slope efficient, ?_, ?_, ?_, ?_⟩
  · exact finiteAlignmentRepair_is_equityMinimizer
      htail hslope hefficient.1
  · exact finiteAlignmentRepair_zero_range hslope
  · exact sub_nonneg.mpr (hefficient.2 _
      (finiteAlignmentRepair_is_equityMinimizer
        htail hslope hefficient.1).1)
  · exact finiteArrivalWeightedBurden_repair_sub
      arrival offset slope efficient hslope

/--
The constructive fixed-load alignment theorem.  The additive price of equity
is nonnegative and no larger than the cost of raising all cells to their
category's efficient-endpoint maximum burden.
-/
theorem finite_fixedLoadAlignment_price_le_gap
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival offset slope : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    {efficient equitable : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (hslope : ∀ k b, 0 < slope k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) efficient)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (affineDelayBurden offset slope z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) equitable) :
    0 ≤ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope equitable) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope efficient) ∧
    finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope equitable) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope efficient) ≤
      finiteAlignmentGap arrival
        (affineDelayBurden offset slope efficient) := by
  let repair := finiteAlignmentRepair offset slope efficient
  have hrepair : finiteMatrixReciprocalCapacityFeasible
      tail excessCapacity repair := by
    apply finiteMatrixReciprocalCapacityFeasible_of_le htail hefficient.1
    exact finiteAlignmentRepair_ge hslope
  have hrepair_zero : finiteAllRequestRangeObjective
      (affineDelayBurden offset slope repair) = 0 := by
    exact finiteAlignmentRepair_zero_range hslope
  have hequitable_nonneg : 0 ≤ finiteAllRequestRangeObjective
      (affineDelayBurden offset slope equitable) :=
    finiteAllRequestRangeObjective_nonneg _
  have hequitable_le_zero : finiteAllRequestRangeObjective
      (affineDelayBurden offset slope equitable) ≤ 0 := by
    rw [← hrepair_zero]
    exact hequitable.2.1 repair hrepair
  have hequitable_zero : finiteAllRequestRangeObjective
      (affineDelayBurden offset slope equitable) = 0 :=
    le_antisymm hequitable_le_zero hequitable_nonneg
  have hlower := hefficient.2 equitable hequitable.1
  have hupper := hequitable.2.2 repair hrepair (by
    change finiteAllRequestRangeObjective
        (affineDelayBurden offset slope repair) =
      finiteAllRequestRangeObjective
        (affineDelayBurden offset slope equitable)
    rw [hrepair_zero, hequitable_zero])
  have hrepair_cost := finiteArrivalWeightedBurden_repair_sub
    arrival offset slope efficient hslope
  constructor
  · linarith
  · dsimp [repair] at hupper hrepair_cost ⊢
    linarith

/-- The exact constructive gap is bounded by arrival mass times burden range. -/
theorem finiteAlignmentGap_le_mass_mul_range
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (arrival burden : Category → Borough → ℝ)
    (harrival : ∀ k b, 0 ≤ arrival k b) :
    finiteAlignmentGap arrival burden ≤
      ∑ k, (∑ b, arrival k b) * finiteBoroughRange (burden k) := by
  classical
  unfold finiteAlignmentGap
  apply Finset.sum_le_sum
  intro k _hk
  calc
    (∑ b, arrival k b *
        (finiteCategoryMaximum burden k - burden k b)) ≤
        ∑ b, arrival k b * finiteBoroughRange (burden k) := by
      apply Finset.sum_le_sum
      intro b _hb
      apply mul_le_mul_of_nonneg_left _ (harrival k b)
      have hmin := finiteCategoryMinimum_le_burden burden k b
      change finiteCategoryMaximum burden k - burden k b ≤
        finiteCategoryMaximum burden k - finiteCategoryMinimum burden k
      linarith
    _ = (∑ b, arrival k b) * finiteBoroughRange (burden k) := by
      rw [Finset.sum_mul]

/--
Combined quantitative near-alignment statement from the revision memo.
-/
theorem finite_fixedLoadAlignment_price_bounds
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival offset slope : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    {efficient equitable : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (harrival : ∀ k b, 0 ≤ arrival k b)
    (hslope : ∀ k b, 0 < slope k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) efficient)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (affineDelayBurden offset slope z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope z)) equitable) :
    0 ≤ finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope equitable) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope efficient) ∧
    finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope equitable) -
      finiteArrivalWeightedBurden arrival
        (affineDelayBurden offset slope efficient) ≤
      finiteAlignmentGap arrival
        (affineDelayBurden offset slope efficient) ∧
    finiteAlignmentGap arrival
        (affineDelayBurden offset slope efficient) ≤
      ∑ k, (∑ b, arrival k b) *
        finiteBoroughRange
          (affineDelayBurden offset slope efficient k) := by
  exact ⟨(finite_fixedLoadAlignment_price_le_gap htail hslope
      hefficient hequitable).1,
    (finite_fixedLoadAlignment_price_le_gap htail hslope
      hefficient hequitable).2,
    finiteAlignmentGap_le_mass_mul_range arrival
      (affineDelayBurden offset slope efficient) harrival⟩

/-! ## Instantiation by the paper's all-request burden -/

/-- Offset in the paper's fixed-load all-request burden. -/
def fixedLoadAllRequestOffset
    (arrival admitted risk penalty : ℝ) : ℝ :=
  allRequestFixedOffset risk
    (fixedLoadInspectionProbability arrival admitted) penalty

/-- Positive delay slope in the paper's fixed-load all-request burden. -/
def fixedLoadAllRequestSlope
    (arrival admitted risk : ℝ) : ℝ :=
  allRequestDelaySlope risk
    (fixedLoadInspectionProbability arrival admitted)

/-- The concrete all-request burden is the generic affine burden above. -/
theorem fixedLoadAllRequestBurden_eq_offset_add_slope
    (arrival admitted risk delay penalty : ℝ) :
    fixedLoadAllRequestBurden arrival admitted risk delay penalty =
      fixedLoadAllRequestOffset arrival admitted risk penalty +
        fixedLoadAllRequestSlope arrival admitted risk * delay := by
  exact allRequestBurden_eq_fixedOffset_add_slope_mul_delay
    risk (fixedLoadInspectionProbability arrival admitted) delay penalty

/-- Positive arrival, admitted load, and risk give a positive burden slope. -/
theorem fixedLoadAllRequestSlope_pos
    {arrival admitted risk : ℝ}
    (harrival : 0 < arrival) (hadmitted : 0 < admitted) (hrisk : 0 < risk) :
    0 < fixedLoadAllRequestSlope arrival admitted risk := by
  unfold fixedLoadAllRequestSlope allRequestDelaySlope
    fixedLoadInspectionProbability
  positivity

/-- The paper's finite matrix of fixed-load all-request burdens. -/
def finiteFixedLoadAllRequestBurdenProfile
    {Category Borough : Type*}
    (arrival admitted risk penalty delay : Category → Borough → ℝ) :
    Category → Borough → ℝ :=
  fun k b ↦ fixedLoadAllRequestBurden
    (arrival k b) (admitted k b) (risk k b) (delay k b) (penalty k b)

theorem finiteFixedLoadAllRequestBurdenProfile_eq_affine
    {Category Borough : Type*}
    (arrival admitted risk penalty delay : Category → Borough → ℝ) :
    finiteFixedLoadAllRequestBurdenProfile
        arrival admitted risk penalty delay =
      affineDelayBurden
        (fun k b ↦ fixedLoadAllRequestOffset
          (arrival k b) (admitted k b) (risk k b) (penalty k b))
        (fun k b ↦ fixedLoadAllRequestSlope
          (arrival k b) (admitted k b) (risk k b)) delay := by
  funext k b
  exact fixedLoadAllRequestBurden_eq_offset_add_slope
    (arrival k b) (admitted k b) (risk k b) (delay k b) (penalty k b)

/--
Source-shaped fixed-load alignment bound for the paper's actual all-request
burden.  This is the quantitative near-alignment theorem that replaces the
memo's invalid global continuity argument.
-/
theorem finite_fixedLoadAllRequest_price_bounds
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival admitted risk penalty : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    {efficient equitable : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z)) efficient)
    (hequitable : LexicographicallyMinimizesEquityThenEfficiencyOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteAllRequestRangeObjective
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z))
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z)) equitable) :
    0 ≤ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty equitable) -
      finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty efficient) ∧
    finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty equitable) -
      finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty efficient) ≤
      finiteAlignmentGap arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty efficient) ∧
    finiteAlignmentGap arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty efficient) ≤
      ∑ k, (∑ b, arrival k b) *
        finiteBoroughRange
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty efficient k) := by
  let offset : Category → Borough → ℝ := fun k b ↦
    fixedLoadAllRequestOffset
      (arrival k b) (admitted k b) (risk k b) (penalty k b)
  let slope : Category → Borough → ℝ := fun k b ↦
    fixedLoadAllRequestSlope (arrival k b) (admitted k b) (risk k b)
  have hslope : ∀ k b, 0 < slope k b := fun k b ↦
    fixedLoadAllRequestSlope_pos (harrival k b) (hadmitted k b) (hrisk k b)
  have hprofile : ∀ z,
      finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty z =
        affineDelayBurden offset slope z := by
    intro z
    exact finiteFixedLoadAllRequestBurdenProfile_eq_affine
      arrival admitted risk penalty z
  simp_rw [hprofile] at hefficient hequitable ⊢
  exact finite_fixedLoadAlignment_price_bounds htail
    (fun k b ↦ (harrival k b).le) hslope hefficient hequitable

/--
Existence-free paper-shaped version of the constructive alignment result.
Starting only from an attained efficiency endpoint, it explicitly constructs
an attained minimizer of the all-request range objective and certifies its
exact efficiency cost.  No lexicographic tie-break endpoint is assumed.
-/
theorem finite_fixedLoadAllRequest_constructive_equity_endpoint
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    {tail arrival admitted risk penalty : Category → Borough → ℝ}
    {excessCapacity : ℝ}
    {efficient : Category → Borough → ℝ}
    (htail : ∀ k b, 0 ≤ tail k b)
    (harrival : ∀ k b, 0 < arrival k b)
    (hadmitted : ∀ k b, 0 < admitted k b)
    (hrisk : ∀ k b, 0 < risk k b)
    (hefficient : MinimizesOn
      (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
      (fun z ↦ finiteArrivalWeightedBurden arrival
        (finiteFixedLoadAllRequestBurdenProfile
          arrival admitted risk penalty z)) efficient) :
    ∃ aligned : Category → Borough → ℝ,
      MinimizesOn
        (finiteMatrixReciprocalCapacityFeasible tail excessCapacity)
        (fun z ↦ finiteAllRequestRangeObjective
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty z)) aligned ∧
      finiteAllRequestRangeObjective
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty aligned) = 0 ∧
      0 ≤ finiteArrivalWeightedBurden arrival
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty aligned) -
        finiteArrivalWeightedBurden arrival
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty efficient) ∧
      finiteArrivalWeightedBurden arrival
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty aligned) -
        finiteArrivalWeightedBurden arrival
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty efficient) =
        finiteAlignmentGap arrival
          (finiteFixedLoadAllRequestBurdenProfile
            arrival admitted risk penalty efficient) := by
  let offset : Category → Borough → ℝ := fun k b ↦
    fixedLoadAllRequestOffset
      (arrival k b) (admitted k b) (risk k b) (penalty k b)
  let slope : Category → Borough → ℝ := fun k b ↦
    fixedLoadAllRequestSlope (arrival k b) (admitted k b) (risk k b)
  have hslope : ∀ k b, 0 < slope k b := fun k b ↦
    fixedLoadAllRequestSlope_pos (harrival k b) (hadmitted k b) (hrisk k b)
  have hprofile : ∀ z,
      finiteFixedLoadAllRequestBurdenProfile arrival admitted risk penalty z =
        affineDelayBurden offset slope z := by
    intro z
    exact finiteFixedLoadAllRequestBurdenProfile_eq_affine
      arrival admitted risk penalty z
  simp_rw [hprofile] at hefficient ⊢
  exact finite_fixedLoadAlignment_constructive_equity_endpoint
    htail hslope hefficient

end

end LG24ServiceLevelAgreements
