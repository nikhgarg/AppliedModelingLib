import LG24ServiceLevelAgreements.ProposedAlignment
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

/-!
# Heterogeneous-offset all-request parity reduction

This file checks the general (Borough-heterogeneous offset) reduced problem in
the July 2026 revision appendix.  The common burden in category `k` is `u k`,
the fixed offset of cell `(k,b)` is `q k b`, and its reciprocal-capacity
coefficient is `c k b`.

The formal results make two qualifications that are easy to lose in prose:

* the domain is the strict cellwise condition `q k b < u k`, equivalently
  `max_b q k b < u k` for a finite nonempty Borough set; and
* blow-up at the lower boundary requires a *positive* coefficient on a cell
  attaining the maximum offset.  A zero-coefficient maximum-offset cell does
  not force divergence.

We prove convex-combination closure of the domain and capacity sublevel set,
affinity of the reduced objective, and the displayed KKT identity as an exact
one-coordinate derivative calculation.  We do not assert optimizer existence
or KKT sufficiency.  Capacity binding is stated with the precise local
slack-improvement qualification needed by the elementary minimizer argument.
-/

namespace LG24ServiceLevelAgreements

open scoped BigOperators

noncomputable section

/-! ## Reduced heterogeneous-offset problem -/

/-- Strict positive-denominator domain of the heterogeneous parity reduction. -/
def heterogeneousParityDomain
    {Category Borough : Type*}
    (offset : Category → Borough → ℝ) (level : Category → ℝ) : Prop :=
  ∀ k b, offset k b < level k

/-- Reciprocal capacity used by common category burden levels. -/
def heterogeneousParityCapacityUse
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (coefficient offset : Category → Borough → ℝ)
    (level : Category → ℝ) : ℝ :=
  ∑ k, ∑ b, coefficient k b / (level k - offset k b)

/-- Linear efficiency tie-break objective after all-request parity reduction. -/
def heterogeneousParityObjective
    {Category : Type*} [Fintype Category]
    (arrivalMass level : Category → ℝ) : ℝ :=
  ∑ k, arrivalMass k * level k

/-- Feasibility for the reduced all-request parity problem. -/
def heterogeneousParityFeasible
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    (coefficient offset : Category → Borough → ℝ)
    (excessCapacity : ℝ) (level : Category → ℝ) : Prop :=
  heterogeneousParityDomain offset level ∧
    heterogeneousParityCapacityUse coefficient offset level ≤ excessCapacity

/-- The maximum-offset notation is exactly the cellwise strict domain. -/
theorem heterogeneousParityDomain_iff_above_finiteMaximum
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (offset : Category → Borough → ℝ) (level : Category → ℝ) :
    heterogeneousParityDomain offset level ↔
      ∀ k, finiteCategoryMaximum offset k < level k := by
  classical
  constructor
  · intro h k
    unfold finiteCategoryMaximum
    rw [Finset.sup'_lt_iff]
    intro b _hb
    exact h k b
  · intro h k b
    exact lt_of_le_of_lt (burden_le_finiteCategoryMaximum offset k b) (h k)

/-- Every denominator in the strict parity domain is positive. -/
theorem heterogeneousParityDenominator_pos
    {Category Borough : Type*}
    {offset : Category → Borough → ℝ} {level : Category → ℝ}
    (hlevel : heterogeneousParityDomain offset level) (k : Category) (b : Borough) :
    0 < level k - offset k b :=
  sub_pos.mpr (hlevel k b)

/-- A positive active coefficient makes its reciprocal term exceed any
nonnegative target sufficiently close to its offset boundary. -/
theorem positive_active_offset_term_exceeds
    {coefficient offset target : ℝ}
    (hcoefficient : 0 < coefficient) (htarget : 0 ≤ target) :
    offset < offset + coefficient / (target + 1) ∧
      target < coefficient /
        ((offset + coefficient / (target + 1)) - offset) := by
  have hden : 0 < target + 1 := by linarith
  constructor
  · exact lt_add_of_pos_right _ (div_pos hcoefficient hden)
  · have heq :
        coefficient /
            ((offset + coefficient / (target + 1)) - offset) =
          target + 1 := by
      field_simp [hcoefficient.ne', hden.ne']
      ring
    rw [heq]
    linarith

/-- Explicit finite-maximum version of boundary blow-up.  The hypothesis that
the maximum-offset cell has positive coefficient is essential. -/
theorem positive_active_finiteMaximum_term_exceeds
    {Category Borough : Type*} [Fintype Borough] [Nonempty Borough]
    (offset coefficient : Category → Borough → ℝ) (k : Category) (b : Borough)
    (hmax : offset k b = finiteCategoryMaximum offset k)
    (hcoefficient : 0 < coefficient k b) (target : ℝ) (htarget : 0 ≤ target) :
    finiteCategoryMaximum offset k <
        finiteCategoryMaximum offset k + coefficient k b / (target + 1) ∧
      target < coefficient k b /
        ((finiteCategoryMaximum offset k + coefficient k b / (target + 1)) -
          offset k b) := by
  rw [hmax]
  exact positive_active_offset_term_exceeds hcoefficient htarget

/-! ## Convexity on the strict domain -/

/-- Each shifted reciprocal `c / (u-q)` is convex on `u>q` when `c≥0`. -/
theorem shifted_weighted_reciprocal_mix_le
    {coefficient offset t x y : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : offset < x) (hy : offset < y) :
    coefficient / (t * x + (1 - t) * y - offset) ≤
      t * (coefficient / (x - offset)) +
        (1 - t) * (coefficient / (y - offset)) := by
  have h := weighted_reciprocal_mix_le hcoefficient ht0 ht1
    (sub_pos.mpr hx) (sub_pos.mpr hy)
  convert h using 1 <;> ring

/-- The strict positive-denominator domain is closed under convex mixtures. -/
theorem heterogeneousParityDomain_delayMix
    {Category Borough : Type*}
    {offset : Category → Borough → ℝ}
    {x y : Category → ℝ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : heterogeneousParityDomain offset x)
    (hy : heterogeneousParityDomain offset y) :
    heterogeneousParityDomain offset (delayMix t x y) := by
  intro k b
  have hpos := delayMix_pos ht0 ht1
    (fun k ↦ sub_pos.mpr (hx k b)) (fun k ↦ sub_pos.mpr (hy k b)) k
  unfold delayMix at hpos ⊢
  linarith

/-- The heterogeneous parity capacity use is convex along domain mixtures. -/
theorem heterogeneousParityCapacityUse_delayMix_le
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {x y : Category → ℝ} {t : ℝ}
    (hcoefficient : ∀ k b, 0 ≤ coefficient k b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : heterogeneousParityDomain offset x)
    (hy : heterogeneousParityDomain offset y) :
    heterogeneousParityCapacityUse coefficient offset (delayMix t x y) ≤
      t * heterogeneousParityCapacityUse coefficient offset x +
        (1 - t) * heterogeneousParityCapacityUse coefficient offset y := by
  classical
  unfold heterogeneousParityCapacityUse
  calc
    ∑ k, ∑ b, coefficient k b / (delayMix t x y k - offset k b) ≤
        ∑ k, ∑ b,
          (t * (coefficient k b / (x k - offset k b)) +
            (1 - t) * (coefficient k b / (y k - offset k b))) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro b _hb
      unfold delayMix
      exact shifted_weighted_reciprocal_mix_le
        (hcoefficient k b) ht0 ht1 (hx k b) (hy k b)
    _ = t * (∑ k, ∑ b, coefficient k b / (x k - offset k b)) +
        (1 - t) * (∑ k, ∑ b, coefficient k b / (y k - offset k b)) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Hence the reduced heterogeneous parity feasible set is convex. -/
theorem heterogeneousParityFeasible_delayMix
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {excessCapacity t : ℝ} {x y : Category → ℝ}
    (hcoefficient : ∀ k b, 0 ≤ coefficient k b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : heterogeneousParityFeasible coefficient offset excessCapacity x)
    (hy : heterogeneousParityFeasible coefficient offset excessCapacity y) :
    heterogeneousParityFeasible coefficient offset excessCapacity (delayMix t x y) := by
  constructor
  · exact heterogeneousParityDomain_delayMix ht0 ht1 hx.1 hy.1
  · have hconvex := heterogeneousParityCapacityUse_delayMix_le
      hcoefficient ht0 ht1 hx.1 hy.1
    have htx := mul_le_mul_of_nonneg_left hx.2 ht0
    have hty := mul_le_mul_of_nonneg_left hy.2 (sub_nonneg.mpr ht1)
    linarith

/-- The reduced efficiency tie-break objective is affine in the burden levels. -/
theorem heterogeneousParityObjective_delayMix
    {Category : Type*} [Fintype Category]
    (arrivalMass x y : Category → ℝ) (t : ℝ) :
    heterogeneousParityObjective arrivalMass (delayMix t x y) =
      t * heterogeneousParityObjective arrivalMass x +
        (1 - t) * heterogeneousParityObjective arrivalMass y := by
  classical
  unfold heterogeneousParityObjective delayMix
  calc
    ∑ k, arrivalMass k * (t * x k + (1 - t) * y k) =
        ∑ k, (t * (arrivalMass k * x k) +
          (1 - t) * (arrivalMass k * y k)) := by
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = t * (∑ k, arrivalMass k * x k) +
        (1 - t) * (∑ k, arrivalMass k * y k) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]

/-! ## Capacity binding: the needed qualification -/

/--
An elementary binding conclusion is valid once strict capacity slack is known
to admit a feasible strict objective improvement.  This isolates the local
attainment/tightening step that the appendix's monotonicity prose must supply;
it is not an optimizer-existence assertion.
-/
theorem heterogeneousParityCapacity_binds_of_slack_improvable
    {Category Borough : Type*} [Fintype Category] [Fintype Borough]
    {coefficient offset : Category → Borough → ℝ}
    {arrivalMass : Category → ℝ} {excessCapacity : ℝ}
    {level : Category → ℝ}
    (hmin : MinimizesOn
      (heterogeneousParityFeasible coefficient offset excessCapacity)
      (heterogeneousParityObjective arrivalMass) level)
    (hslackImproves :
      heterogeneousParityCapacityUse coefficient offset level < excessCapacity →
        ∃ improved,
          heterogeneousParityFeasible coefficient offset excessCapacity improved ∧
          heterogeneousParityObjective arrivalMass improved <
            heterogeneousParityObjective arrivalMass level) :
    heterogeneousParityCapacityUse coefficient offset level = excessCapacity := by
  rcases hmin with ⟨hfeasible, hoptimal⟩
  apply le_antisymm hfeasible.2
  by_contra hnot
  have hslack :
      heterogeneousParityCapacityUse coefficient offset level < excessCapacity :=
    lt_of_not_ge hnot
  rcases hslackImproves hslack with ⟨improved, himproved, hlt⟩
  exact (not_lt_of_ge (hoptimal improved himproved)) hlt

/-! ## Coordinate derivative and KKT identity -/

/-- One category's scalar Lagrangian contribution for fixed multiplier `eta`. -/
def heterogeneousParityCategoryLagrangian
    {Borough : Type*} [Fintype Borough]
    (arrivalMass eta : ℝ) (coefficient offset : Borough → ℝ)
    (level : ℝ) : ℝ :=
  arrivalMass * level + eta * ∑ b, coefficient b / (level - offset b)

/-- Exact derivative of one shifted reciprocal term away from its pole. -/
theorem hasDerivAt_shifted_reciprocal
    {coefficient offset level : ℝ} (hlevel : level ≠ offset) :
    HasDerivAt (fun u : ℝ ↦ coefficient / (u - offset))
      (-coefficient / (level - offset) ^ 2) level := by
  have hlinear : HasDerivAt (fun u : ℝ ↦ u - offset) 1 level :=
    (hasDerivAt_id level).sub_const offset
  simpa [div_eq_mul_inv] using
    (hlinear.inv (sub_ne_zero.mpr hlevel)).const_mul coefficient

/-- The appendix's category-coordinate derivative formula is exact. -/
theorem hasDerivAt_heterogeneousParityCategoryLagrangian
    {Borough : Type*} [Fintype Borough]
    {arrivalMass eta level : ℝ} {coefficient offset : Borough → ℝ}
    (hlevel : ∀ b, offset b < level) :
    HasDerivAt
      (heterogeneousParityCategoryLagrangian arrivalMass eta coefficient offset)
      (arrivalMass - eta * ∑ b, coefficient b / (level - offset b) ^ 2)
      level := by
  classical
  unfold heterogeneousParityCategoryLagrangian
  have hlinear : HasDerivAt (fun u : ℝ ↦ arrivalMass * u) arrivalMass level := by
    simpa using (hasDerivAt_id level).const_mul arrivalMass
  have hsum : HasDerivAt
      (fun u : ℝ ↦ ∑ b, coefficient b / (u - offset b))
      (∑ b, -coefficient b / (level - offset b) ^ 2) level := by
    apply HasDerivAt.fun_sum
    intro b _hb
    exact hasDerivAt_shifted_reciprocal (ne_of_gt (hlevel b))
  have hsumneg :
      (∑ b, -coefficient b / (level - offset b) ^ 2) =
        -(∑ b, coefficient b / (level - offset b) ^ 2) := by
    calc
      ∑ b, -coefficient b / (level - offset b) ^ 2 =
          ∑ b, -(coefficient b / (level - offset b) ^ 2) := by
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = -(∑ b, coefficient b / (level - offset b) ^ 2) := by
        simp
  convert hlinear.add (hsum.const_mul eta) using 1
  rw [hsumneg]
  ring

/--
The displayed KKT first-order identity is algebraically equivalent to a zero
coordinate derivative.  Positivity of `eta` records the appendix's multiplier
domain but is not used to infer existence, necessity, or sufficiency of KKT.
-/
theorem heterogeneousParity_kkt_identity_iff_derivative_zero
    {Borough : Type*} [Fintype Borough]
    {arrivalMass eta level : ℝ} {coefficient offset : Borough → ℝ}
    (heta : 0 < eta) (hlevel : ∀ b, offset b < level) :
    deriv (heterogeneousParityCategoryLagrangian
        arrivalMass eta coefficient offset) level = 0 ↔
      arrivalMass = eta * ∑ b, coefficient b / (level - offset b) ^ 2 := by
  have hderiv :=
    (hasDerivAt_heterogeneousParityCategoryLagrangian
      (arrivalMass := arrivalMass) (eta := eta)
      (coefficient := coefficient) (offset := offset) hlevel).deriv
  rw [hderiv]
  constructor <;> intro h <;> linarith

end

end LG24ServiceLevelAgreements
