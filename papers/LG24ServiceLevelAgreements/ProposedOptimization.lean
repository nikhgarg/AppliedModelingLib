import LG24ServiceLevelAgreements.ProposedFixedLoad
import AppliedModelingLib.Foundations.Optimization.Certificate
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Proposed theory: fixed-load optimization and all-request ranges

This file formalizes the finite-dimensional optimization core proposed in the
July 2026 revision memo for *Redesigning Service Level Agreements*.

The results here deliberately begin after the paper's cited queueing tail
bound.  They prove:

* convex-combination closure of the reciprocal-capacity feasible set;
* finite weighted reciprocal-allocation optimality, including an explicit
  square-root minimizer and an `IsMinimizerOn` certificate;
* affinity of the fixed-load efficiency objective;
* a two-Borough specialization of the sum of within-category all-request
  ranges and its convexity.

No continuity or near-symmetry theorem is asserted.  Such a theorem needs a
precise nondegenerate parameter domain and an attainment/compactness argument
that is not part of the memo's elementary algebraic core.  The parity-weight
identity and exact-symmetry lexicographic bridge live in
`RevisionBoundaries.lean`.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Finite reciprocal-capacity feasibility -/

/-- Total reciprocal capacity used by positive delays `z`. -/
def reciprocalCapacityUse {Cell : Type*} [Fintype Cell]
    (tail delay : Cell → ℝ) : ℝ :=
  ∑ i, tail i / delay i

/-- The memo's fixed-load feasible set after admitted loads have been fixed. -/
def reciprocalCapacityFeasible {Cell : Type*} [Fintype Cell]
    (tail : Cell → ℝ) (excessCapacity : ℝ) (delay : Cell → ℝ) : Prop :=
  (∀ i, 0 < delay i) ∧ reciprocalCapacityUse tail delay ≤ excessCapacity

/-- Total effective capacity, including admitted load and reciprocal SLA slack. -/
def totalFixedLoadEffectiveCapacity {Cell : Type*} [Fintype Cell]
    (admitted tail delay : Cell → ℝ) : ℝ :=
  ∑ i, fixedLoadEffectiveCapacity (admitted i) (tail i) (delay i)

/-- Separating admitted load from the reciprocal SLA capacity term. -/
theorem totalFixedLoadEffectiveCapacity_eq
    {Cell : Type*} [Fintype Cell]
    (admitted tail delay : Cell → ℝ) :
    totalFixedLoadEffectiveCapacity admitted tail delay =
      (∑ i, admitted i) + reciprocalCapacityUse tail delay := by
  classical
  simp only [totalFixedLoadEffectiveCapacity, fixedLoadEffectiveCapacity,
    reciprocalCapacityUse, Finset.sum_add_distrib]

/--
The aggregate effective-capacity constraint is exactly the memo's excess-
capacity constraint after subtracting admitted load.
-/
theorem totalFixedLoadEffectiveCapacity_le_iff
    {Cell : Type*} [Fintype Cell]
    (admitted tail delay : Cell → ℝ) (capacity : ℝ) :
    totalFixedLoadEffectiveCapacity admitted tail delay ≤ capacity ↔
      reciprocalCapacityUse tail delay ≤ capacity - ∑ i, admitted i := by
  rw [totalFixedLoadEffectiveCapacity_eq]
  constructor <;> intro h <;> linarith

/-- Convex combination of two finite delay vectors. -/
def delayMix {Cell : Type*} (t : ℝ) (x y : Cell → ℝ) : Cell → ℝ :=
  fun i ↦ t * x i + (1 - t) * y i

/-- A scalar reciprocal is convex on positive delays, with explicit assumptions. -/
theorem weighted_reciprocal_mix_le
    {a t x y : ℝ}
    (ha : 0 ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : 0 < x) (hy : 0 < y) :
    a / (t * x + (1 - t) * y) ≤ t * (a / x) + (1 - t) * (a / y) := by
  have hmix : 0 < t * x + (1 - t) * y := by
    by_cases ht : t = 0
    · subst t
      simpa using hy
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
      exact add_pos_of_pos_of_nonneg (mul_pos htpos hx)
        (mul_nonneg (sub_nonneg.mpr ht1) hy.le)
  apply (div_le_iff₀ hmix).2
  have hxy : 0 < x * y := mul_pos hx hy
  have hgap :
      0 ≤ a * t * (1 - t) * (x - y) ^ 2 / (x * y) := by
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg ha ht0) (sub_nonneg.mpr ht1))
        (sq_nonneg (x - y)))
      hxy.le
  have hid :
      (t * (a / x) + (1 - t) * (a / y)) *
          (t * x + (1 - t) * y) - a =
        a * t * (1 - t) * (x - y) ^ 2 / (x * y) := by
    field_simp [hx.ne', hy.ne']
    ring
  nlinarith

/-- Positive delay vectors remain positive under a convex combination. -/
theorem delayMix_pos
    {Cell : Type*} {t : ℝ} {x y : Cell → ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ∀ i, 0 < delayMix t x y i := by
  intro i
  unfold delayMix
  by_cases ht : t = 0
  · subst t
    simpa using hy i
  · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    exact add_pos_of_pos_of_nonneg (mul_pos htpos (hx i))
      (mul_nonneg (sub_nonneg.mpr ht1) (hy i).le)

/-- Reciprocal capacity use is convex along positive finite delay vectors. -/
theorem reciprocalCapacityUse_delayMix_le
    {Cell : Type*} [Fintype Cell]
    {tail x y : Cell → ℝ} {t : ℝ}
    (htail : ∀ i, 0 ≤ tail i)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    reciprocalCapacityUse tail (delayMix t x y) ≤
      t * reciprocalCapacityUse tail x +
        (1 - t) * reciprocalCapacityUse tail y := by
  classical
  unfold reciprocalCapacityUse
  calc
    ∑ i, tail i / delayMix t x y i ≤
        ∑ i, (t * (tail i / x i) + (1 - t) * (tail i / y i)) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact weighted_reciprocal_mix_le (htail i) ht0 ht1 (hx i) (hy i)
    _ = t * (∑ i, tail i / x i) + (1 - t) * (∑ i, tail i / y i) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The fixed-load reciprocal feasible region is closed under convex combinations. -/
theorem reciprocalCapacityFeasible_delayMix
    {Cell : Type*} [Fintype Cell]
    {tail : Cell → ℝ} {excessCapacity t : ℝ} {x y : Cell → ℝ}
    (htail : ∀ i, 0 ≤ tail i)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : reciprocalCapacityFeasible tail excessCapacity x)
    (hy : reciprocalCapacityFeasible tail excessCapacity y) :
    reciprocalCapacityFeasible tail excessCapacity (delayMix t x y) := by
  constructor
  · exact delayMix_pos ht0 ht1 hx.1 hy.1
  · have hconvex := reciprocalCapacityUse_delayMix_le htail ht0 ht1 hx.1 hy.1
    have htx := mul_le_mul_of_nonneg_left hx.2 ht0
    have hty := mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr ht1)
    nlinarith

/-! ## Finite weighted reciprocal-allocation endpoint -/

/-- Served-delay part of fixed-load efficiency for arbitrary finite cells. -/
def servedDelayEfficiency {Cell : Type*} [Fintype Cell]
    (weight delay : Cell → ℝ) : ℝ :=
  ∑ i, weight i * delay i

/-- Aggregate square-root weight in the memo's closed-form endpoint. -/
def aggregateRootWeight {Cell : Type*} [Fintype Cell]
    (tail weight : Cell → ℝ) : ℝ :=
  ∑ i, Real.sqrt (tail i * weight i)

/--
Finite reciprocal-allocation Cauchy--Schwarz inequality:
`(∑ √(aᵢwᵢ))² ≤ (∑ aᵢ/zᵢ)(∑ wᵢzᵢ)`.
-/
theorem aggregateRootWeight_sq_le_use_mul_efficiency
    {Cell : Type*} [Fintype Cell]
    {tail weight delay : Cell → ℝ}
    (htail : ∀ i, 0 ≤ tail i)
    (hweight : ∀ i, 0 ≤ weight i)
    (hdelay : ∀ i, 0 < delay i) :
    aggregateRootWeight tail weight ^ 2 ≤
      reciprocalCapacityUse tail delay * servedDelayEfficiency weight delay := by
  classical
  unfold aggregateRootWeight reciprocalCapacityUse servedDelayEfficiency
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
  · intro i _hi
    exact div_nonneg (htail i) (hdelay i).le
  · intro i _hi
    exact mul_nonneg (hweight i) (hdelay i).le
  · intro i _hi
    rw [Real.sq_sqrt (mul_nonneg (htail i) (hweight i))]
    field_simp [(hdelay i).ne']

/-- Every feasible positive delay vector obeys the memo's efficiency lower bound. -/
theorem aggregateRootWeight_sq_div_excess_le_efficiency
    {Cell : Type*} [Fintype Cell]
    {tail weight delay : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 ≤ tail i)
    (hweight : ∀ i, 0 ≤ weight i)
    (hexcess : 0 < excessCapacity)
    (hfeasible : reciprocalCapacityFeasible tail excessCapacity delay) :
    aggregateRootWeight tail weight ^ 2 / excessCapacity ≤
      servedDelayEfficiency weight delay := by
  have hcs := aggregateRootWeight_sq_le_use_mul_efficiency
    htail hweight hfeasible.1
  have heffNonneg : 0 ≤ servedDelayEfficiency weight delay := by
    unfold servedDelayEfficiency
    exact Finset.sum_nonneg fun i _hi ↦
      mul_nonneg (hweight i) (hfeasible.1 i).le
  have hproduct :
      reciprocalCapacityUse tail delay * servedDelayEfficiency weight delay ≤
        excessCapacity * servedDelayEfficiency weight delay :=
    mul_le_mul_of_nonneg_right hfeasible.2 heffNonneg
  apply (div_le_iff₀ hexcess).2
  simpa [mul_comm] using hcs.trans hproduct

/-- The explicit square-root allocation written in a division-stable form. -/
def squareRootAllocationDelay {Cell : Type*} [Fintype Cell]
    (tail weight : Cell → ℝ) (excessCapacity : ℝ) : Cell → ℝ :=
  fun i ↦
    tail i * aggregateRootWeight tail weight /
      (excessCapacity * Real.sqrt (tail i * weight i))

private theorem positive_eq_sqrt_mul_sqrt_div
    {x : ℝ} (hx : 0 < x) : x / Real.sqrt x = Real.sqrt x := by
  apply (div_eq_iff (Real.sqrt_pos.2 hx).ne').2
  nlinarith [Real.sq_sqrt hx.le]

/-- Positive cell primitives give positive aggregate square-root weight. -/
theorem aggregateRootWeight_pos
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i) :
    0 < aggregateRootWeight tail weight := by
  classical
  let i : Cell := Classical.choice (inferInstance : Nonempty Cell)
  have hterm : 0 < Real.sqrt (tail i * weight i) :=
    Real.sqrt_pos.2 (mul_pos (htail i) (hweight i))
  have hle : Real.sqrt (tail i * weight i) ≤
      ∑ j, Real.sqrt (tail j * weight j) := by
    exact Finset.single_le_sum
      (fun j _hj ↦ Real.sqrt_nonneg (tail j * weight j))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm hle

/-- The square-root candidate has positive delay in every active cell. -/
theorem squareRootAllocationDelay_pos
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) :
    ∀ i, 0 < squareRootAllocationDelay tail weight excessCapacity i := by
  intro i
  unfold squareRootAllocationDelay
  have hroot : 0 < aggregateRootWeight tail weight :=
    aggregateRootWeight_pos htail hweight
  have hcell : 0 < Real.sqrt (tail i * weight i) :=
    Real.sqrt_pos.2 (mul_pos (htail i) (hweight i))
  exact div_pos (mul_pos (htail i) hroot) (mul_pos hexcess hcell)

/-- Cellwise reciprocal use at the square-root allocation. -/
theorem tail_div_squareRootAllocationDelay
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) (i : Cell) :
    tail i / squareRootAllocationDelay tail weight excessCapacity i =
      excessCapacity * Real.sqrt (tail i * weight i) /
        aggregateRootWeight tail weight := by
  have hroot : aggregateRootWeight tail weight ≠ 0 :=
    (aggregateRootWeight_pos htail hweight).ne'
  have hcell : Real.sqrt (tail i * weight i) ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (htail i) (hweight i))).ne'
  unfold squareRootAllocationDelay
  field_simp [hroot, hcell, hexcess.ne', (htail i).ne']

/-- Cellwise efficiency contribution at the square-root allocation. -/
theorem weight_mul_squareRootAllocationDelay
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) (i : Cell) :
    weight i * squareRootAllocationDelay tail weight excessCapacity i =
      aggregateRootWeight tail weight / excessCapacity *
        Real.sqrt (tail i * weight i) := by
  have hcellPos : 0 < tail i * weight i := mul_pos (htail i) (hweight i)
  have hcell : Real.sqrt (tail i * weight i) ≠ 0 :=
    (Real.sqrt_pos.2 hcellPos).ne'
  unfold squareRootAllocationDelay
  have hquot :
      (tail i * weight i) / Real.sqrt (tail i * weight i) =
        Real.sqrt (tail i * weight i) :=
    positive_eq_sqrt_mul_sqrt_div hcellPos
  calc
    weight i *
          (tail i * aggregateRootWeight tail weight /
            (excessCapacity * Real.sqrt (tail i * weight i))) =
        aggregateRootWeight tail weight / excessCapacity *
          ((tail i * weight i) / Real.sqrt (tail i * weight i)) := by
      field_simp [hcell, hexcess.ne']
    _ = aggregateRootWeight tail weight / excessCapacity *
        Real.sqrt (tail i * weight i) := by rw [hquot]

/-- The square-root allocation uses exactly all excess capacity. -/
theorem reciprocalCapacityUse_squareRootAllocationDelay
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) :
    reciprocalCapacityUse tail
        (squareRootAllocationDelay tail weight excessCapacity) = excessCapacity := by
  classical
  unfold reciprocalCapacityUse
  simp_rw [tail_div_squareRootAllocationDelay htail hweight hexcess]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change excessCapacity * aggregateRootWeight tail weight /
      aggregateRootWeight tail weight = excessCapacity
  field_simp [(aggregateRootWeight_pos htail hweight).ne']

/-- The square-root allocation attains the Cauchy lower-bound value. -/
theorem servedDelayEfficiency_squareRootAllocationDelay
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) :
    servedDelayEfficiency weight
        (squareRootAllocationDelay tail weight excessCapacity) =
      aggregateRootWeight tail weight ^ 2 / excessCapacity := by
  classical
  unfold servedDelayEfficiency
  simp_rw [weight_mul_squareRootAllocationDelay htail hweight hexcess]
  rw [← Finset.mul_sum]
  unfold aggregateRootWeight
  ring

/-- The finite square-root allocation is feasible. -/
theorem squareRootAllocationDelay_feasible
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) :
    reciprocalCapacityFeasible tail excessCapacity
      (squareRootAllocationDelay tail weight excessCapacity) := by
  exact ⟨squareRootAllocationDelay_pos htail hweight hexcess,
    (reciprocalCapacityUse_squareRootAllocationDelay htail hweight hexcess).le⟩

/--
The memo's finite closed-form efficiency endpoint is an actual minimizer, not
merely a stationary point or an algebraic candidate.
-/
theorem squareRootAllocationDelay_isMinimizerOn
    {Cell : Type*} [Fintype Cell] [Nonempty Cell]
    {tail weight : Cell → ℝ} {excessCapacity : ℝ}
    (htail : ∀ i, 0 < tail i) (hweight : ∀ i, 0 < weight i)
    (hexcess : 0 < excessCapacity) :
    AppliedModelingLib.Optimization.IsMinimizerOn
      (reciprocalCapacityFeasible tail excessCapacity)
      (servedDelayEfficiency weight)
      (squareRootAllocationDelay tail weight excessCapacity) := by
  constructor
  · exact squareRootAllocationDelay_feasible htail hweight hexcess
  · intro delay hdelay
    rw [servedDelayEfficiency_squareRootAllocationDelay htail hweight hexcess]
    exact aggregateRootWeight_sq_div_excess_le_efficiency
      (fun i ↦ (htail i).le) (fun i ↦ (hweight i).le) hexcess hdelay

/-! ## Affine efficiency and two-Borough all-request ranges -/

/-- Fixed-load non-inspection cost, constant as the conditional delays vary. -/
def fixedLoadNoninspectionCost {Cell : Type*} [Fintype Cell]
    (arrival admitted risk penalty : Cell → ℝ) : ℝ :=
  ∑ i, (arrival i - admitted i) * risk i * penalty i

/-- Full fixed-load efficiency: served delay plus the constant non-inspection term. -/
def finiteFixedLoadEfficiency {Cell : Type*} [Fintype Cell]
    (arrival admitted risk penalty delay : Cell → ℝ) : ℝ :=
  servedDelayEfficiency (fun i ↦ admitted i * risk i) delay +
    fixedLoadNoninspectionCost arrival admitted risk penalty

/-- The served-delay efficiency objective is linear in the delay vector. -/
theorem servedDelayEfficiency_delayMix
    {Cell : Type*} [Fintype Cell]
    (weight x y : Cell → ℝ) (t : ℝ) :
    servedDelayEfficiency weight (delayMix t x y) =
      t * servedDelayEfficiency weight x +
        (1 - t) * servedDelayEfficiency weight y := by
  classical
  unfold servedDelayEfficiency delayMix
  calc
    ∑ i, weight i * (t * x i + (1 - t) * y i) =
        ∑ i, (t * (weight i * x i) + (1 - t) * (weight i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = t * (∑ i, weight i * x i) +
        (1 - t) * (∑ i, weight i * y i) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The full fixed-load efficiency objective is affine in conditional delays. -/
theorem finiteFixedLoadEfficiency_delayMix
    {Cell : Type*} [Fintype Cell]
    (arrival admitted risk penalty x y : Cell → ℝ) (t : ℝ) :
    finiteFixedLoadEfficiency arrival admitted risk penalty (delayMix t x y) =
      t * finiteFixedLoadEfficiency arrival admitted risk penalty x +
        (1 - t) * finiteFixedLoadEfficiency arrival admitted risk penalty y := by
  rw [finiteFixedLoadEfficiency, finiteFixedLoadEfficiency,
    finiteFixedLoadEfficiency, servedDelayEfficiency_delayMix]
  ring

/-- All-request burden is affine in conditional delay when primitives are fixed. -/
theorem allRequestBurden_delayMix
    (risk inspectionProbability penalty x y t : ℝ) :
    allRequestBurden risk inspectionProbability
        (t * x + (1 - t) * y) penalty =
      t * allRequestBurden risk inspectionProbability x penalty +
        (1 - t) * allRequestBurden risk inspectionProbability y penalty := by
  unfold allRequestBurden
  ring

/-- Fixed-load all-request burden inherits affinity in conditional delay. -/
theorem fixedLoadAllRequestBurden_delayMix
    (arrival admitted risk penalty x y t : ℝ) :
    fixedLoadAllRequestBurden arrival admitted risk
        (t * x + (1 - t) * y) penalty =
      t * fixedLoadAllRequestBurden arrival admitted risk x penalty +
        (1 - t) * fixedLoadAllRequestBurden arrival admitted risk y penalty := by
  unfold fixedLoadAllRequestBurden
  exact allRequestBurden_delayMix risk
    (fixedLoadInspectionProbability arrival admitted) penalty x y t

/-- The two-Borough range is the absolute difference of the two burdens. -/
theorem twoBoroughRange_eq_abs_sub (x y : ℝ) :
    twoBoroughRange x y = |x - y| := by
  unfold twoBoroughRange
  by_cases hxy : x ≤ y
  · rw [max_eq_right hxy, min_eq_left hxy, abs_of_nonpos (sub_nonpos.mpr hxy)]
    ring
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [max_eq_left hyx, min_eq_right hyx, abs_of_nonneg (sub_nonneg.mpr hyx)]

/-- A two-Borough range is always nonnegative. -/
theorem twoBoroughRange_nonneg (x y : ℝ) :
    0 ≤ twoBoroughRange x y := by
  rw [twoBoroughRange_eq_abs_sub]
  exact abs_nonneg _

/-- Convexity of a two-Borough range under simultaneous burden mixing. -/
theorem twoBoroughRange_mix_le
    {x₁ x₂ y₁ y₂ t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoBoroughRange (t * x₁ + (1 - t) * y₁)
        (t * x₂ + (1 - t) * y₂) ≤
      t * twoBoroughRange x₁ x₂ +
        (1 - t) * twoBoroughRange y₁ y₂ := by
  rw [twoBoroughRange_eq_abs_sub, twoBoroughRange_eq_abs_sub,
    twoBoroughRange_eq_abs_sub]
  calc
    |t * x₁ + (1 - t) * y₁ - (t * x₂ + (1 - t) * y₂)| =
        |t * (x₁ - x₂) + (1 - t) * (y₁ - y₂)| := by
          apply congrArg abs
          ring
    _ ≤ |t * (x₁ - x₂)| + |(1 - t) * (y₁ - y₂)| := abs_add_le _ _
    _ = t * |x₁ - x₂| + (1 - t) * |y₁ - y₂| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ht0,
        abs_of_nonneg (sub_nonneg.mpr ht1)]

/-- Sum of within-category ranges for a finite set of categories and two Boroughs. -/
def twoBoroughRangeObjective {Category : Type*} [Fintype Category]
    (borough₁ borough₂ : Category → ℝ) : ℝ :=
  ∑ k, twoBoroughRange (borough₁ k) (borough₂ k)

/-- The sum of two-Borough within-category ranges is nonnegative. -/
theorem twoBoroughRangeObjective_nonneg
    {Category : Type*} [Fintype Category]
    (borough₁ borough₂ : Category → ℝ) :
    0 ≤ twoBoroughRangeObjective borough₁ borough₂ := by
  unfold twoBoroughRangeObjective
  exact Finset.sum_nonneg fun k _hk ↦
    twoBoroughRange_nonneg (borough₁ k) (borough₂ k)

/-- Equal burdens in every category give zero total within-category range. -/
theorem twoBoroughRangeObjective_eq_zero_of_eq
    {Category : Type*} [Fintype Category]
    {borough₁ borough₂ : Category → ℝ}
    (heq : ∀ k, borough₁ k = borough₂ k) :
    twoBoroughRangeObjective borough₁ borough₂ = 0 := by
  classical
  unfold twoBoroughRangeObjective
  apply Finset.sum_eq_zero
  intro k _hk
  exact twoBoroughRange_eq_zero_of_eq _ _ (heq k)

/-- Convexity of the sum of within-category two-Borough ranges. -/
theorem twoBoroughRangeObjective_mix_le
    {Category : Type*} [Fintype Category]
    {x₁ x₂ y₁ y₂ : Category → ℝ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoBoroughRangeObjective
        (fun k ↦ t * x₁ k + (1 - t) * y₁ k)
        (fun k ↦ t * x₂ k + (1 - t) * y₂ k) ≤
      t * twoBoroughRangeObjective x₁ x₂ +
        (1 - t) * twoBoroughRangeObjective y₁ y₂ := by
  classical
  unfold twoBoroughRangeObjective
  calc
    ∑ k, twoBoroughRange (t * x₁ k + (1 - t) * y₁ k)
        (t * x₂ k + (1 - t) * y₂ k) ≤
        ∑ k, (t * twoBoroughRange (x₁ k) (x₂ k) +
          (1 - t) * twoBoroughRange (y₁ k) (y₂ k)) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact twoBoroughRange_mix_le ht0 ht1
    _ = t * (∑ k, twoBoroughRange (x₁ k) (x₂ k)) +
        (1 - t) * (∑ k, twoBoroughRange (y₁ k) (y₂ k)) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- All-request burden profile for a finite category and two-Borough model. -/
def twoBoroughAllRequestBurdenProfile
    {Category : Type*}
    (arrival admitted risk delay penalty : Category → Bool → ℝ) :
    Category → Bool → ℝ :=
  fun k b ↦ fixedLoadAllRequestBurden
    (arrival k b) (admitted k b) (risk k b) (delay k b) (penalty k b)

/-- The memo's sum of within-category all-request ranges, for two Boroughs. -/
def twoBoroughAllRequestRangeObjective
    {Category : Type*} [Fintype Category]
    (arrival admitted risk delay penalty : Category → Bool → ℝ) : ℝ :=
  twoBoroughRangeObjective
    (fun k ↦ twoBoroughAllRequestBurdenProfile
      arrival admitted risk delay penalty k false)
    (fun k ↦ twoBoroughAllRequestBurdenProfile
      arrival admitted risk delay penalty k true)

/-- The two-Borough all-request range objective is nonnegative. -/
theorem twoBoroughAllRequestRangeObjective_nonneg
    {Category : Type*} [Fintype Category]
    (arrival admitted risk delay penalty : Category → Bool → ℝ) :
    0 ≤ twoBoroughAllRequestRangeObjective arrival admitted risk delay penalty := by
  exact twoBoroughRangeObjective_nonneg _ _

/--
With arrival, admission, risk, and penalty fixed, the two-Borough all-request
range objective is convex in the conditional-delay vector.
-/
theorem twoBoroughAllRequestRangeObjective_delayMix_le
    {Category : Type*} [Fintype Category]
    (arrival admitted risk penalty x y : Category → Bool → ℝ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    twoBoroughAllRequestRangeObjective arrival admitted risk
        (fun k b ↦ t * x k b + (1 - t) * y k b) penalty ≤
      t * twoBoroughAllRequestRangeObjective arrival admitted risk x penalty +
        (1 - t) *
          twoBoroughAllRequestRangeObjective arrival admitted risk y penalty := by
  classical
  unfold twoBoroughAllRequestRangeObjective twoBoroughAllRequestBurdenProfile
  simpa only [fixedLoadAllRequestBurden_delayMix] using
    (twoBoroughRangeObjective_mix_le
      (x₁ := fun k ↦ fixedLoadAllRequestBurden
        (arrival k false) (admitted k false) (risk k false)
        (x k false) (penalty k false))
      (x₂ := fun k ↦ fixedLoadAllRequestBurden
        (arrival k true) (admitted k true) (risk k true)
        (x k true) (penalty k true))
      (y₁ := fun k ↦ fixedLoadAllRequestBurden
        (arrival k false) (admitted k false) (risk k false)
        (y k false) (penalty k false))
      (y₂ := fun k ↦ fixedLoadAllRequestBurden
        (arrival k true) (admitted k true) (risk k true)
        (y k true) (penalty k true))
      ht0 ht1)

/-! ## Arbitrary finite Borough ranges -/

/-- Range of a real-valued burden over an arbitrary nonempty finite Borough set. -/
def finiteBoroughRange
    {Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Borough → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty burden -
    Finset.univ.inf' Finset.univ_nonempty burden

/-- Every finite Borough range is nonnegative. -/
theorem finiteBoroughRange_nonneg
    {Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Borough → ℝ) :
    0 ≤ finiteBoroughRange burden := by
  classical
  let b : Borough := Classical.choice (inferInstance : Nonempty Borough)
  have hinf : Finset.univ.inf' Finset.univ_nonempty burden ≤ burden b :=
    Finset.inf'_le burden (Finset.mem_univ b)
  have hsup : burden b ≤ Finset.univ.sup' Finset.univ_nonempty burden :=
    Finset.le_sup' burden (Finset.mem_univ b)
  unfold finiteBoroughRange
  linarith

/-- A constant burden profile has zero finite Borough range. -/
theorem finiteBoroughRange_eq_zero_of_constant
    {Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (burden : Borough → ℝ) (level : ℝ)
    (hconstant : ∀ b, burden b = level) :
    finiteBoroughRange burden = 0 := by
  classical
  unfold finiteBoroughRange
  have hsup : Finset.univ.sup' Finset.univ_nonempty burden = level := by
    apply le_antisymm
    · exact Finset.sup'_le Finset.univ_nonempty burden
        (fun b _hb ↦ (hconstant b).le)
    · let b : Borough := Classical.choice (inferInstance : Nonempty Borough)
      rw [← hconstant b]
      exact Finset.le_sup' burden (Finset.mem_univ b)
  have hinf : Finset.univ.inf' Finset.univ_nonempty burden = level := by
    apply le_antisymm
    · let b : Borough := Classical.choice (inferInstance : Nonempty Borough)
      rw [← hconstant b]
      exact Finset.inf'_le burden (Finset.mem_univ b)
    · exact Finset.le_inf' Finset.univ_nonempty burden
        (fun b _hb ↦ (hconstant b).ge)
  rw [hsup, hinf]
  ring

/-- Convexity of max-minus-min over an arbitrary finite Borough set. -/
theorem finiteBoroughRange_mix_le
    {Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (x y : Borough → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteBoroughRange (fun b ↦ t * x b + (1 - t) * y b) ≤
      t * finiteBoroughRange x + (1 - t) * finiteBoroughRange y := by
  classical
  have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht1
  have hsup :
      Finset.univ.sup' Finset.univ_nonempty
          (fun b ↦ t * x b + (1 - t) * y b) ≤
        t * Finset.univ.sup' Finset.univ_nonempty x +
          (1 - t) * Finset.univ.sup' Finset.univ_nonempty y := by
    apply Finset.sup'_le Finset.univ_nonempty
    intro b _hb
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' x (Finset.mem_univ b)) ht0)
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' y (Finset.mem_univ b)) hone)
  have hinf :
      t * Finset.univ.inf' Finset.univ_nonempty x +
          (1 - t) * Finset.univ.inf' Finset.univ_nonempty y ≤
        Finset.univ.inf' Finset.univ_nonempty
          (fun b ↦ t * x b + (1 - t) * y b) := by
    apply Finset.le_inf' Finset.univ_nonempty
    intro b _hb
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (Finset.inf'_le x (Finset.mem_univ b)) ht0)
      (mul_le_mul_of_nonneg_left
        (Finset.inf'_le y (Finset.mem_univ b)) hone)
  unfold finiteBoroughRange
  linarith

/-- The memo's sum of within-category ranges for arbitrary finite Boroughs. -/
def finiteAllRequestRangeObjective
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) : ℝ :=
  ∑ k, finiteBoroughRange (burden k)

/-- A finite sum of arbitrary-Borough category ranges is convex. -/
theorem finiteAllRequestRangeObjective_mix_le
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (x y : Category → Borough → ℝ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteAllRequestRangeObjective
        (fun k b ↦ t * x k b + (1 - t) * y k b) ≤
      t * finiteAllRequestRangeObjective x +
        (1 - t) * finiteAllRequestRangeObjective y := by
  classical
  unfold finiteAllRequestRangeObjective
  calc
    ∑ k, finiteBoroughRange (fun b ↦ t * x k b + (1 - t) * y k b) ≤
        ∑ k, (t * finiteBoroughRange (x k) +
          (1 - t) * finiteBoroughRange (y k)) := by
      exact Finset.sum_le_sum fun k _hk ↦
        finiteBoroughRange_mix_le (x k) (y k) ht0 ht1
    _ = t * (∑ k, finiteBoroughRange (x k)) +
        (1 - t) * (∑ k, finiteBoroughRange (y k)) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Common burden within every category gives zero total finite-Borough range. -/
theorem finiteAllRequestRangeObjective_eq_zero_of_constant
    {Category Borough : Type*}
    [Fintype Category] [Fintype Borough] [Nonempty Borough]
    (burden : Category → Borough → ℝ) (level : Category → ℝ)
    (hconstant : ∀ k b, burden k b = level k) :
    finiteAllRequestRangeObjective burden = 0 := by
  classical
  unfold finiteAllRequestRangeObjective
  apply Finset.sum_eq_zero
  intro k _hk
  exact finiteBoroughRange_eq_zero_of_constant
    (burden k) (level k) (hconstant k)

end

end LG24ServiceLevelAgreements
