import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic
import AppliedModelingLib.Foundations.Math.ExtremalGraph
import AppliedModelingLib.Foundations.Math.EuclideanNets
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms
import AppliedModelingLib.Foundations.Math.FiniteRanking

/-!
# Finite Linear Compressed Sensing

Paper-neutral finite-dimensional primitives for linear representation/recovery
arguments.  Columns are represented as functions `Feature -> Coord -> R`, which
keeps paper statements close to their displayed finite sums while avoiding
unnecessary matrix-basis overhead.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Math
namespace LinearCompressedSensing

variable {Feature Coord : Type*}

/-- Finite real inner product written as a sum over coordinates. -/
def inner [Fintype Coord] (x y : Coord → ℝ) : ℝ :=
  ∑ r, x r * y r

theorem inner_eq_dot [Fintype Coord] (x y : Coord → ℝ) :
    inner x y = AppliedModelingLib.FiniteDimensionalNorms.dot x y := by
  rfl

theorem inner_comm [Fintype Coord] (x y : Coord → ℝ) :
    inner x y = inner y x := by
  simp [inner, mul_comm]

/-- Embed a finite coordinate vector into a larger `Fin` coordinate space by zero padding. -/
def padFinVector {d D : ℕ} (h : d ≤ D) (x : Fin d → ℝ) : Fin D → ℝ :=
  fun r => if hr : (r : ℕ) < d then x ⟨r, hr⟩ else 0

theorem inner_padFinVector {d D : ℕ} (h : d ≤ D)
    (x y : Fin d → ℝ) :
    inner (padFinVector h x) (padFinVector h y) = inner x y := by
  classical
  unfold inner
  have hsumD :
      (∑ r : Fin D, padFinVector h x r * padFinVector h y r) =
        ∑ n ∈ Finset.range D,
          if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0 := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun n => if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0) D]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    by_cases hr : (r : ℕ) < d
    · simp [padFinVector, hr]
    · simp [padFinVector, hr]
  have hsubset : Finset.range d ⊆ Finset.range D := by
    intro n hn
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) h)
  have hsum_subset :
      (∑ n ∈ Finset.range d,
          if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0) =
        ∑ n ∈ Finset.range D,
          if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0 := by
    refine Finset.sum_subset hsubset ?_
    intro n _hnD hn_not
    have hn_ge : d ≤ n := by
      exact Nat.le_of_not_gt (by simpa using hn_not)
    simp [not_lt.mpr hn_ge]
  have hsumd_range :
      (∑ n ∈ Finset.range d,
          if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0) =
        ∑ r : Fin d, x r * y r := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun n => if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0) d]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    simp [r.isLt]
  calc
    (∑ r : Fin D, padFinVector h x r * padFinVector h y r)
        = ∑ n ∈ Finset.range D,
            if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0 := hsumD
    _ = ∑ n ∈ Finset.range d,
            if hn : n < d then x ⟨n, hn⟩ * y ⟨n, hn⟩ else 0 := hsum_subset.symm
    _ = ∑ r : Fin d, x r * y r := hsumd_range

theorem inner_self_eq_l2Sq [Fintype Coord] (x : Coord → ℝ) :
    inner x x = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.dot_self_eq_l2Sq x

theorem abs_inner_le_l2_mul_l2 [Fintype Coord] (x y : Coord → ℝ) :
    |inner x y| ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2 x *
        AppliedModelingLib.FiniteDimensionalNorms.l2 y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.abs_dot_le_l2_mul_l2 x y

/-- Finite Euclidean column norm associated with `inner`. -/
noncomputable def vectorNorm [Fintype Coord] (x : Coord → ℝ) : ℝ :=
  AppliedModelingLib.FiniteDimensionalNorms.l2 x

theorem vectorNorm_nonneg [Fintype Coord] (x : Coord → ℝ) :
    0 ≤ vectorNorm x :=
  AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg x

theorem vectorNorm_sq_eq_inner_self [Fintype Coord] (x : Coord → ℝ) :
    vectorNorm x ^ 2 = inner x x := by
  rw [vectorNorm, AppliedModelingLib.FiniteDimensionalNorms.l2]
  rw [inner_self_eq_l2Sq]
  exact Real.sq_sqrt (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x)

theorem inner_self_eq_vectorNorm_sq [Fintype Coord] (x : Coord → ℝ) :
    inner x x = vectorNorm x ^ 2 := by
  rw [vectorNorm_sq_eq_inner_self]

theorem abs_inner_le_vectorNorm_mul_vectorNorm [Fintype Coord]
    (x y : Coord → ℝ) :
    |inner x y| ≤ vectorNorm x * vectorNorm y :=
  abs_inner_le_l2_mul_l2 x y

theorem inner_le_vectorNorm_mul_vectorNorm [Fintype Coord]
    (x y : Coord → ℝ) :
    inner x y ≤ vectorNorm x * vectorNorm y :=
  (le_abs_self _).trans (abs_inner_le_vectorNorm_mul_vectorNorm x y)

theorem vectorNorm_lower_bound_of_inner_gt_of_vectorNorm_le
    [Fintype Coord] {x y : Coord → ℝ} {t gamma : ℝ}
    (ht : 0 < t) (hinner : t < inner x y)
    (hynorm : vectorNorm y ≤ gamma) (hgamma : 0 < gamma) :
    t / gamma < vectorNorm x := by
  have hinner_pos : 0 < inner x y := lt_trans ht hinner
  have habs : inner x y ≤ |inner x y| := le_abs_self _
  have hcs := abs_inner_le_vectorNorm_mul_vectorNorm x y
  have hmul_norm :
      vectorNorm x * vectorNorm y ≤ vectorNorm x * gamma := by
    exact mul_le_mul_of_nonneg_left hynorm (vectorNorm_nonneg x)
  have ht_mul : t < vectorNorm x * gamma := by
    exact hinner.trans_le (habs.trans (hcs.trans hmul_norm))
  exact (div_lt_iff₀ hgamma).mpr (by simpa [mul_comm] using ht_mul)

theorem inner_smul_smul [Fintype Coord]
    (a b : ℝ) (x y : Coord → ℝ) :
    inner (fun r => a * x r) (fun r => b * y r) =
      a * b * inner x y := by
  classical
  rw [inner, inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

theorem inner_add_left [Fintype Coord]
    (x y z : Coord → ℝ) :
    inner (fun r => x r + y r) z = inner x z + inner y z := by
  classical
  simp [inner, add_mul, Finset.sum_add_distrib]

theorem inner_add_right [Fintype Coord]
    (x y z : Coord → ℝ) :
    inner x (fun r => y r + z r) = inner x y + inner x z := by
  classical
  simp [inner, mul_add, Finset.sum_add_distrib]

theorem inner_neg_left [Fintype Coord]
    (x y : Coord → ℝ) :
    inner (fun r => -x r) y = -inner x y := by
  classical
  simp [inner, Finset.sum_neg_distrib]

theorem inner_neg_right [Fintype Coord]
    (x y : Coord → ℝ) :
    inner x (fun r => -y r) = -inner x y := by
  classical
  simp [inner, Finset.sum_neg_distrib]

theorem inner_sub_left [Fintype Coord]
    (x y z : Coord → ℝ) :
    inner (fun r => x r - y r) z = inner x z - inner y z := by
  classical
  simp [inner, sub_eq_add_neg, add_mul, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

theorem inner_sub_right [Fintype Coord]
    (x y z : Coord → ℝ) :
    inner x (fun r => y r - z r) = inner x y - inner x z := by
  classical
  simp [inner, sub_eq_add_neg, mul_add, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]

theorem l2Sq_add_eq [Fintype Coord]
    (x y : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun r => x r + y r) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq y + 2 * inner x y := by
  classical
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq, inner]
  calc
    (∑ r : Coord, (x r + y r) ^ 2) =
        ∑ r : Coord, ((x r) ^ 2 + (y r) ^ 2 + 2 * (x r * y r)) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          ring
    _ = (∑ r : Coord, (x r) ^ 2) +
          (∑ r : Coord, (y r) ^ 2) +
            2 * (∑ r : Coord, x r * y r) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]

theorem l2Sq_sub_eq [Fintype Coord]
    (x y : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun r => x r - y r) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq y - 2 * inner x y := by
  classical
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq, inner]
  calc
    (∑ r : Coord, (x r - y r) ^ 2) =
        ∑ r : Coord, ((x r) ^ 2 + (y r) ^ 2 - 2 * (x r * y r)) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          ring
    _ = (∑ r : Coord, (x r) ^ 2) +
          (∑ r : Coord, (y r) ^ 2) -
            2 * (∑ r : Coord, x r * y r) := by
          simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem four_mul_inner_eq_l2Sq_add_sub_l2Sq_sub [Fintype Coord]
    (x y : Coord → ℝ) :
    4 * inner x y =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun r => x r + y r) -
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun r => x r - y r) := by
  rw [l2Sq_add_eq, l2Sq_sub_eq]
  ring

theorem l2Sq_smul [Fintype Coord]
    (a : ℝ) (x : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun r => a * x r) =
      a ^ 2 * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  classical
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  ring

theorem inner_add_smul_add_smul [Fintype Coord]
    (lambda : ℝ) (x y z w : Coord → ℝ) :
    inner (fun r => x r + lambda * y r)
      (fun r => z r + lambda * w r) =
        inner x z + lambda * inner x w +
          lambda * inner y z + lambda ^ 2 * inner y w := by
  classical
  simp [inner, add_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    pow_two]
  ring_nf

/-- Normalize a finite vector using `vectorNorm`. Zero vectors normalize to zero. -/
noncomputable def normalizedVector [Fintype Coord] (x : Coord → ℝ) : Coord → ℝ :=
  fun r => (vectorNorm x)⁻¹ * x r

/-- Finite Euclidean correlation of two vectors. -/
noncomputable def vectorCorrelation [Fintype Coord]
    (x y : Coord → ℝ) : ℝ :=
  inner (normalizedVector x) (normalizedVector y)

theorem vectorCorrelation_eq_inv_mul_inv_mul_inner [Fintype Coord]
    (x y : Coord → ℝ) :
    vectorCorrelation x y =
      (vectorNorm x)⁻¹ * (vectorNorm y)⁻¹ * inner x y := by
  rw [vectorCorrelation]
  change inner (fun r => (vectorNorm x)⁻¹ * x r)
      (fun r => (vectorNorm y)⁻¹ * y r) =
    (vectorNorm x)⁻¹ * (vectorNorm y)⁻¹ * inner x y
  simpa using
    inner_smul_smul
      (Coord := Coord) (vectorNorm x)⁻¹ (vectorNorm y)⁻¹ x y

theorem vectorCorrelation_comm [Fintype Coord] (x y : Coord → ℝ) :
    vectorCorrelation x y = vectorCorrelation y x := by
  simp [vectorCorrelation, inner_comm]

theorem abs_vectorCorrelation_le_of_abs_inner_le_of_norm_product_ge
    [Fintype Coord] {x y : Coord → ℝ} {N D : ℝ}
    (hx : 0 < vectorNorm x) (hy : 0 < vectorNorm y)
    (hinner : |inner x y| ≤ N)
    (hdenom : D ≤ vectorNorm x * vectorNorm y) (hD : 0 < D) :
    |vectorCorrelation x y| ≤ N / D := by
  have hprod_pos : 0 < vectorNorm x * vectorNorm y := mul_pos hx hy
  have hN : 0 ≤ N := (abs_nonneg _).trans hinner
  have hcorr :
      |vectorCorrelation x y| =
        |inner x y| / (vectorNorm x * vectorNorm y) := by
    rw [vectorCorrelation_eq_inv_mul_inv_mul_inner]
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hx),
      abs_of_pos (inv_pos.mpr hy)]
    field_simp [ne_of_gt hx, ne_of_gt hy]
  rw [hcorr]
  calc
    |inner x y| / (vectorNorm x * vectorNorm y) ≤
        N / (vectorNorm x * vectorNorm y) := by
          exact div_le_div_of_nonneg_right hinner (le_of_lt hprod_pos)
    _ ≤ N / D := by
          exact div_le_div_of_nonneg_left hN hD hdenom

theorem vectorCorrelation_eq_inner_div_norm_mul_norm_of_pos
    [Fintype Coord] {x y : Coord → ℝ}
    (hx : 0 < vectorNorm x) (hy : 0 < vectorNorm y) :
    vectorCorrelation x y = inner x y / (vectorNorm x * vectorNorm y) := by
  rw [vectorCorrelation_eq_inv_mul_inv_mul_inner]
  field_simp [ne_of_gt hx, ne_of_gt hy]

theorem vectorCorrelation_ge_of_inner_ge_of_norm_product_le
    [Fintype Coord] {x y : Coord → ℝ} {N D : ℝ}
    (hx : 0 < vectorNorm x) (hy : 0 < vectorNorm y)
    (hinner : N ≤ inner x y) (hN : 0 ≤ N)
    (hdenom : vectorNorm x * vectorNorm y ≤ D) :
    N / D ≤ vectorCorrelation x y := by
  have hprod_pos : 0 < vectorNorm x * vectorNorm y := mul_pos hx hy
  rw [vectorCorrelation_eq_inner_div_norm_mul_norm_of_pos hx hy]
  calc
    N / D ≤ N / (vectorNorm x * vectorNorm y) := by
      exact div_le_div_of_nonneg_left hN hprod_pos hdenom
    _ ≤ inner x y / (vectorNorm x * vectorNorm y) := by
      exact div_le_div_of_nonneg_right hinner (le_of_lt hprod_pos)

theorem vectorNorm_normalizedVector_eq_one_of_pos [Fintype Coord]
    {x : Coord → ℝ} (hx : 0 < vectorNorm x) :
    vectorNorm (normalizedVector x) = 1 := by
  change vectorNorm (fun r => (vectorNorm x)⁻¹ * x r) = 1
  rw [vectorNorm, AppliedModelingLib.FiniteDimensionalNorms.normL2_smul]
  have hx' : 0 < AppliedModelingLib.FiniteDimensionalNorms.l2 x := by
    simpa [vectorNorm] using hx
  change |(AppliedModelingLib.FiniteDimensionalNorms.l2 x)⁻¹| *
      AppliedModelingLib.FiniteDimensionalNorms.l2 x = 1
  rw [abs_of_pos (inv_pos.mpr hx')]
  exact inv_mul_cancel₀ hx'.ne'

theorem inner_normalizedVector_self_eq_one_of_pos [Fintype Coord]
    {x : Coord → ℝ} (hx : 0 < vectorNorm x) :
    inner (normalizedVector x) (normalizedVector x) = 1 := by
  have hnorm := vectorNorm_normalizedVector_eq_one_of_pos (Coord := Coord) hx
  rw [inner_self_eq_l2Sq]
  have hsquare :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (normalizedVector x) =
        vectorNorm (normalizedVector x) ^ 2 := by
    rw [vectorNorm, AppliedModelingLib.FiniteDimensionalNorms.l2]
    exact (Real.sq_sqrt
      (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg (normalizedVector x))).symm
  rw [hsquare, hnorm]
  norm_num

/-- Matrix with columns indexed by features and rows indexed by coordinates. -/
def representationMatrix (A : Feature → Coord → ℝ) : Matrix Coord Feature ℝ :=
  fun r i => A i r

/-- Matrix whose rows are probe vectors. -/
def probeRowMatrix (B : Feature → Coord → ℝ) : Matrix Feature Coord ℝ :=
  fun i r => B i r

/-- The feature-by-feature matrix `B^T A`, with entries given by finite inner products. -/
noncomputable def crossInnerMatrix [Fintype Coord]
    (A B : Feature → Coord → ℝ) : Matrix Feature Feature ℝ :=
  probeRowMatrix B * representationMatrix A

@[simp] theorem crossInnerMatrix_apply [Fintype Coord]
    (A B : Feature → Coord → ℝ) (i j : Feature) :
    crossInnerMatrix A B i j = inner (B i) (A j) := by
  simp [crossInnerMatrix, probeRowMatrix, representationMatrix, inner, Matrix.mul_apply]

/-- The rank of `B^T A` is at most the representation dimension. -/
theorem crossInnerMatrix_rank_le_card_coord
    [Fintype Feature] [Fintype Coord] (A B : Feature → Coord → ℝ) :
    (crossInnerMatrix A B).rank ≤ Fintype.card Coord := by
  classical
  calc
    (crossInnerMatrix A B).rank =
        (probeRowMatrix B * representationMatrix A).rank := rfl
    _ ≤ (probeRowMatrix B).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card Coord := Matrix.rank_le_card_width _

/-- Principal submatrices of `B^T A` also have rank at most the representation dimension. -/
theorem crossInnerMatrix_principalSubmatrix_rank_le_card_coord
    [Fintype Feature] [Fintype Coord] {Sub : Type*} [Fintype Sub]
    (A B : Feature → Coord → ℝ) (select : Sub → Feature) :
    ((crossInnerMatrix A B).submatrix select select).rank ≤ Fintype.card Coord := by
  exact (Matrix.rank_submatrix_le (crossInnerMatrix A B) select select).trans
    (crossInnerMatrix_rank_le_card_coord A B)

/-- Nonzero support of a finite real vector. -/
noncomputable def support [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) : Finset Feature :=
  Finset.univ.filter fun i => z i ≠ 0

/-- A finite vector is `k`-sparse when its nonzero support has cardinality at most `k`. -/
def KSparse [Fintype Feature] [DecidableEq Feature]
    (k : ℕ) (z : Feature → ℝ) : Prop :=
  (support z).card ≤ k

/-- The linear measurement vector `Az` for a finite column family. -/
def measurement [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (z : Feature → ℝ) : Coord → ℝ :=
  fun r => ∑ i, z i * A i r

/-- The finite `l1` mass of a vector restricted to a finite set of coordinates. -/
noncomputable def l1On [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) : ℝ :=
  ∑ i ∈ S, |z i|

theorem l1On_nonneg
    [DecidableEq Feature] (S : Finset Feature) (z : Feature → ℝ) :
    0 ≤ l1On S z := by
  rw [l1On]
  exact Finset.sum_nonneg fun i _hi => abs_nonneg (z i)

theorem l1On_pos_of_exists_mem_ne_zero
    [DecidableEq Feature] {S : Finset Feature} {z : Feature → ℝ}
    (h : ∃ i, i ∈ S ∧ z i ≠ 0) :
    0 < l1On S z := by
  rcases h with ⟨i, hiS, hi_ne⟩
  rw [l1On]
  exact Finset.sum_pos'
    (fun j _hj => abs_nonneg (z j))
    ⟨i, hiS, abs_pos.mpr hi_ne⟩

theorem l1On_mono
    [DecidableEq Feature] {S T : Finset Feature} {z : Feature → ℝ}
    (hST : S ⊆ T) :
    l1On S z ≤ l1On T z := by
  rw [l1On, l1On]
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (by intro i _hiT _hiS; exact abs_nonneg (z i))

theorem l1On_eq_l1On_add_l1On_sdiff
    [DecidableEq Feature] {S T : Finset Feature} {z : Feature → ℝ}
    (hTS : T ⊆ S) :
    l1On S z = l1On T z + l1On (S \ T) z := by
  classical
  have hdisj : Disjoint T (S \ T) := by
    refine Finset.disjoint_left.mpr ?_
    intro i hiT hiST
    exact (Finset.mem_sdiff.mp hiST).2 hiT
  have hunion : T ∪ (S \ T) = S := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_union.mp hi with hiT | hiST
      · exact hTS hiT
      · exact (Finset.mem_sdiff.mp hiST).1
    · intro hiS
      by_cases hiT : i ∈ T
      · exact Finset.mem_union.mpr (Or.inl hiT)
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_sdiff.mpr ⟨hiS, hiT⟩))
  calc
    l1On S z = l1On (T ∪ (S \ T)) z := by rw [hunion]
    _ = l1On T z + l1On (S \ T) z := by
      rw [l1On, l1On, l1On]
      exact Finset.sum_union
        (s₁ := T) (s₂ := S \ T) (f := fun i : Feature => |z i|) hdisj

theorem sdiff_union_eq_sdiff_sdiff
    [DecidableEq Feature] (A B C : Finset Feature) :
    A \ (B ∪ C) = (A \ B) \ C := by
  ext i
  simp [and_assoc]

theorem sqrt_mul_le_half_add {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hsqrt_mul :
      Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
    rw [Real.sqrt_mul ha]
  rw [hsqrt_mul]
  have hsq : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have hsa : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsb : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  nlinarith

theorem delta_mul_sqrt_add_lt_one_sub_delta_mul_sum
    {δ a b : ℝ} (hδ_nonneg : 0 ≤ δ) (hδ : δ < 2 / 5)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hpos : 0 < a + b) :
    δ * (Real.sqrt (a * b) + b) < (1 - δ) * (a + b) := by
  have hsqrt : Real.sqrt (a * b) ≤ (a + b) / 2 :=
    sqrt_mul_le_half_add ha hb
  have hleft :
      δ * (Real.sqrt (a * b) + b) ≤ δ * (((a + b) / 2) + b) := by
    have hsum : Real.sqrt (a * b) + b ≤ (a + b) / 2 + b := by
      simpa [add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hsqrt b)
    exact mul_le_mul_of_nonneg_left hsum hδ_nonneg
  have hstrict :
      δ * (((a + b) / 2) + b) < (1 - δ) * (a + b) := by
    nlinarith
  exact lt_of_le_of_lt hleft hstrict

theorem sqrt_mul_ranked_residual_bound_le_sqrt_mul_add
    {w a b : ℝ} (hw : 0 < w) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt w * (Real.sqrt (b * (a / w)) + b / Real.sqrt w) ≤
      Real.sqrt (a * b) + b := by
  have hw_nonneg : 0 ≤ w := le_of_lt hw
  have hw_ne : w ≠ 0 := ne_of_gt hw
  have hsqrt_w_pos : 0 < Real.sqrt w := Real.sqrt_pos_of_pos hw
  have hsqrt_w_ne : Real.sqrt w ≠ 0 := ne_of_gt hsqrt_w_pos
  have hterm :
      Real.sqrt w * Real.sqrt (b * (a / w)) = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul hw_nonneg]
    congr 1
    field_simp [hw_ne]
  have hdiv : Real.sqrt w * (b / Real.sqrt w) = b := by
    field_simp [hsqrt_w_ne]
  rw [mul_add, hterm, hdiv]

/-- The squared finite `l2` mass of a vector restricted to a finite set. -/
noncomputable def l2SqOn [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) : ℝ :=
  ∑ i ∈ S, z i ^ 2

/-- Coordinate restriction of a finite vector to a set. -/
def restrictTo [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) : Feature → ℝ :=
  fun i => if i ∈ S then z i else 0

/-- Extend a vector indexed by a finite coordinate subset by zero. -/
def extendByZero [DecidableEq Feature]
    (S : Finset Feature) (x : {i : Feature // i ∈ S} → ℝ) : Feature → ℝ :=
  fun i => if hi : i ∈ S then x ⟨i, hi⟩ else 0

/-- Zero extension preserves the squared Euclidean mass. -/
theorem l2Sq_extendByZero [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (x : {i : Feature // i ∈ S} → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (extendByZero S x) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
  classical
  have hsum : (∑ i : Feature, extendByZero S x i ^ 2) =
      ∑ i ∈ S, extendByZero S x i ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _hi hnot
    simp [extendByZero, hnot]
  rw [hsum]
  symm
  calc
    (∑ i : {i : Feature // i ∈ S}, x i ^ 2) =
        ∑ i : {i : Feature // i ∈ S}, extendByZero S x i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp [extendByZero, i.property]
    _ = ∑ i ∈ S, extendByZero S x i ^ 2 := by
          rw [Finset.univ_eq_attach S]
          exact Finset.sum_attach S (fun i => extendByZero S x i ^ 2)

/-- A vector supported on `S` is recovered by zero extension of its restriction to `S`. -/
theorem extendByZero_subtype_eq_of_support_subset
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (x : Feature → ℝ) (hx : support x ⊆ S) :
    extendByZero S (fun i => x i) = x := by
  funext i
  by_cases hi : i ∈ S
  · simp [extendByZero, hi]
  · have hi_not_support : i ∉ support x := by
      intro hisupp
      exact hi (hx hisupp)
    have hxi : x i = 0 := by
      by_contra hne
      exact hi_not_support (by simp [support, hne])
    simp [extendByZero, hi, hxi]

/-- The coordinate submatrix with columns indexed by a finite subset. -/
def restrictedMatrix [DecidableEq Feature]
    (A : Feature → Coord → ℝ) (S : Finset Feature) :
    Matrix Coord {i : Feature // i ∈ S} ℝ :=
  fun r i => A i.1 r

/-- A restricted matrix acts as the original measurement after zero extension. -/
theorem restrictedMatrix_mulVec_eq_measurement_extendByZero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (x : {i : Feature // i ∈ S} → ℝ) (r : Coord) :
    (restrictedMatrix A S).mulVec x r =
      measurement A (extendByZero S x) r := by
  classical
  simp only [Matrix.mulVec, dotProduct, restrictedMatrix, measurement]
  calc
    (∑ j : {i : Feature // i ∈ S}, A j r * x j) =
        ∑ j : {i : Feature // i ∈ S},
          extendByZero S x (j : Feature) * A (j : Feature) r := by
            apply Finset.sum_congr rfl
            intro j _hj
            simp [extendByZero, j.property]
            ring
    _ = ∑ i ∈ S, extendByZero S x i * A i r := by
            rw [Finset.univ_eq_attach S]
            exact Finset.sum_attach S (fun i => extendByZero S x i * A i r)
    _ = ∑ i : Feature, extendByZero S x i * A i r := by
            apply Finset.sum_subset (Finset.subset_univ S)
            intro i _hi hnot
            simp [extendByZero, hnot]

/-- The continuous Euclidean measurement map on a finite coordinate subset. -/
noncomputable def restrictedEuclideanMeasurement
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature) :
    EuclideanSpace ℝ {i : Feature // i ∈ S} →L[ℝ] EuclideanSpace ℝ Coord :=
  (Matrix.toLpLin 2 2 (restrictedMatrix A S)).toContinuousLinearMap

/-- Pointwise form of the restricted Euclidean measurement map. -/
theorem restrictedEuclideanMeasurement_apply
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (v : EuclideanSpace ℝ {i : Feature // i ∈ S}) (r : Coord) :
    (restrictedEuclideanMeasurement A S v).ofLp r =
      measurement A (extendByZero S v.ofLp) r := by
  change ((Matrix.toLpLin 2 2 (restrictedMatrix A S) v).ofLp) r = _
  rw [Matrix.toLpLin_apply]
  exact restrictedMatrix_mulVec_eq_measurement_extendByZero A S v.ofLp r

/-- Squared Euclidean norm in a finite coordinate space is the explicit `l2Sq`. -/
theorem norm_sq_eq_l2Sq_ofEuclideanSpace
    {Index : Type*} [Fintype Index] (v : EuclideanSpace ℝ Index) :
    ‖v‖ ^ 2 = AppliedModelingLib.FiniteDimensionalNorms.l2Sq v.ofLp := by
  rw [EuclideanSpace.real_norm_sq_eq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq]

/-- The restricted Euclidean map has the same squared norm as zero-extended measurement. -/
theorem norm_sq_restrictedEuclideanMeasurement_eq_l2Sq_measurement_extendByZero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (v : EuclideanSpace ℝ {i : Feature // i ∈ S}) :
    ‖restrictedEuclideanMeasurement A S v‖ ^ 2 =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement A (extendByZero S v.ofLp)) := by
  rw [EuclideanSpace.real_norm_sq_eq,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [restrictedEuclideanMeasurement_apply]

theorem l1On_restrictTo_eq_of_subset
    [DecidableEq Feature] {S T : Finset Feature} {z : Feature → ℝ}
    (hST : S ⊆ T) :
    l1On S (restrictTo T z) = l1On S z := by
  rw [l1On, l1On]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [restrictTo, hST hi]

/--
Nullspace property for exact `l1` recovery: every nonzero kernel vector has
strictly smaller `l1` mass on any `k`-sized coordinate set than off that set.
-/
def NullspaceProperty [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (k : ℕ) : Prop :=
  ∀ h : Feature → ℝ, measurement A h = (fun _ => 0) → h ≠ (fun _ => 0) →
    ∀ S : Finset Feature, S.card ≤ k → l1On S h < l1On Sᶜ h

/--
Sparse-kernel exclusion: no nonzero vector of sparsity at most `s` lies in the
kernel of the measurement map.
-/
def SparseKernelFree
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (s : ℕ) : Prop :=
  ∀ x : Feature → ℝ, KSparse s x →
    measurement A x = (fun _ => 0) → x = fun _ => 0

/--
Basis-pursuit exact recovery for a finite measurement matrix: every `k`-sparse
vector is the unique `l1` minimizer among vectors with the same measurement.
-/
def BasisPursuitExactRecovery
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (k : ℕ) : Prop :=
  ∀ z : Feature → ℝ, KSparse k z →
    ∀ z' : Feature → ℝ,
      measurement A z' = measurement A z →
        AppliedModelingLib.FiniteDimensionalNorms.l1 z' ≤
          AppliedModelingLib.FiniteDimensionalNorms.l1 z →
        z' = z

/--
Finite restricted isometry property.  Every `s`-sparse vector keeps its
squared Euclidean norm after measurement, up to multiplicative error `δ`.
-/
def RestrictedIsometryProperty
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (s : ℕ) (δ : ℝ) : Prop :=
  ∀ x : Feature → ℝ, KSparse s x →
    (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ∧
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ≤
      (1 + δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x

/-- The finite family of all coordinate supports of cardinality at most `s`. -/
noncomputable def supportFinsetsCardLe
    [Fintype Feature] [DecidableEq Feature] (s : ℕ) :
    Finset (Finset Feature) := by
  classical
  exact (Finset.univ : Finset Feature).powerset.filter fun S => S.card ≤ s

@[simp] theorem mem_supportFinsetsCardLe
    [Fintype Feature] [DecidableEq Feature] {s : ℕ} {S : Finset Feature} :
    S ∈ supportFinsetsCardLe (Feature := Feature) s ↔ S.card ≤ s := by
  classical
  simp [supportFinsetsCardLe]

theorem support_mem_supportFinsetsCardLe_of_kSparse
    [Fintype Feature] [DecidableEq Feature] {s : ℕ} {x : Feature → ℝ}
    (hx : KSparse s x) :
    support x ∈ supportFinsetsCardLe (Feature := Feature) s :=
  mem_supportFinsetsCardLe.mpr hx

theorem supportFinsetsCardLe_card_le_sum_choose
    [Fintype Feature] [DecidableEq Feature] (s : ℕ) :
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
      ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r := by
  classical
  let U : Finset Feature := Finset.univ
  let supports := supportFinsetsCardLe (Feature := Feature) s
  let slices : Finset (Finset Feature) :=
    (Finset.range (s + 1)).biUnion fun r => U.powersetCard r
  have hsubset : supports ⊆ slices := by
    intro S hS
    have hcard : S.card ≤ s := mem_supportFinsetsCardLe.mp hS
    have hmem_range : S.card ∈ Finset.range (s + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hcard)
    have hmem_slice : S ∈ U.powersetCard S.card := by
      exact Finset.mem_powersetCard.mpr
        ⟨by intro i _hi; simp [U], rfl⟩
    exact Finset.mem_biUnion.mpr ⟨S.card, hmem_range, hmem_slice⟩
  calc
    supports.card ≤ slices.card := Finset.card_le_card hsubset
    _ ≤ ∑ r ∈ Finset.range (s + 1), (U.powersetCard r).card := by
      exact Finset.card_biUnion_le
    _ = ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      simp [U]

theorem choose_le_choose_of_le_of_le_half
    {n r s : ℕ} (hrs : r ≤ s) (hs_half : s ≤ n / 2) :
    Nat.choose n r ≤ Nat.choose n s := by
  refine
    Nat.le_induction
      (P := fun t _hrt => t ≤ s → Nat.choose n r ≤ Nat.choose n t)
      ?base ?step s hrs le_rfl
  · intro _h
    rfl
  · intro t _hrt ih ht_succ_le
    have ht_le_s : t ≤ s := Nat.le_trans (Nat.le_succ t) ht_succ_le
    have ht_lt_s : t < s := Nat.lt_of_succ_le ht_succ_le
    have ht_lt_half : t < n / 2 := lt_of_lt_of_le ht_lt_s hs_half
    exact (ih ht_le_s).trans (Nat.choose_le_succ_of_lt_half_left ht_lt_half)

theorem supportFinsetsCardLe_card_le_succ_mul_choose_of_le_half
    [Fintype Feature] [DecidableEq Feature] {s : ℕ}
    (hs_half : s ≤ Fintype.card Feature / 2) :
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
      (s + 1) * Nat.choose (Fintype.card Feature) s := by
  have hbase :=
    supportFinsetsCardLe_card_le_sum_choose
      (Feature := Feature) s
  have hsum :
      ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r ≤
        ∑ _r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) s := by
    exact Finset.sum_le_sum fun r hr => by
      have hr_le : r ≤ s :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      exact choose_le_choose_of_le_of_le_half hr_le hs_half
  calc
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
        ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r := hbase
    _ ≤ ∑ _r ∈ Finset.range (s + 1),
          Nat.choose (Fintype.card Feature) s := hsum
    _ = (s + 1) * Nat.choose (Fintype.card Feature) s := by
      simp

theorem supportFinsetsCardLe_card_le_sum_pow_card
    [Fintype Feature] [DecidableEq Feature] (s : ℕ) :
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
      ∑ r ∈ Finset.range (s + 1), Fintype.card Feature ^ r := by
  have hbase :=
    supportFinsetsCardLe_card_le_sum_choose
      (Feature := Feature) s
  exact hbase.trans
    (Finset.sum_le_sum fun r _hr => Nat.choose_le_pow (Fintype.card Feature) r)

theorem supportFinsetsCardLe_card_le_succ_mul_card_pow
    [Fintype Feature] [DecidableEq Feature] {s : ℕ}
    (hcard_pos : 0 < Fintype.card Feature) :
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
      (s + 1) * Fintype.card Feature ^ s := by
  have hbase :=
    supportFinsetsCardLe_card_le_sum_pow_card
      (Feature := Feature) s
  have hpow :
      ∑ r ∈ Finset.range (s + 1), Fintype.card Feature ^ r ≤
        ∑ _r ∈ Finset.range (s + 1), Fintype.card Feature ^ s := by
    exact Finset.sum_le_sum fun r hr => by
      have hr_le : r ≤ s :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      exact Nat.pow_le_pow_right hcard_pos hr_le
  calc
    (supportFinsetsCardLe (Feature := Feature) s).card ≤
        ∑ r ∈ Finset.range (s + 1), Fintype.card Feature ^ r := hbase
    _ ≤ ∑ _r ∈ Finset.range (s + 1), Fintype.card Feature ^ s := hpow
    _ = (s + 1) * Fintype.card Feature ^ s := by
      simp

/--
Restricted isometry on one fixed coordinate support.  This is the supportwise
form used by standard random-matrix RIP proofs: concentration is proved for
each fixed support and then union-bounded over all supports.
-/
def RestrictedIsometryOnSupport
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature) (δ : ℝ) : Prop :=
  ∀ x : Feature → ℝ, support x ⊆ S →
    (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ∧
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ≤
      (1 + δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x

/-- Restricted isometry is monotone in its distortion constant. -/
theorem restrictedIsometryOnSupport_mono_delta
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {S : Finset Feature} {δ₁ δ₂ : ℝ}
    (hδ : δ₁ ≤ δ₂) (hrip : RestrictedIsometryOnSupport A S δ₁) :
    RestrictedIsometryOnSupport A S δ₂ := by
  intro x hxsupp
  have hnonneg := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x
  rcases hrip x hxsupp with ⟨hlower, hupper⟩
  constructor
  · calc
      (1 - δ₂) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
          (1 - δ₁) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
            gcongr
      _ ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) := hlower
  · calc
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ≤
          (1 + δ₁) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := hupper
      _ ≤ (1 + δ₂) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
            gcongr

/--
A finite unit-sphere net with distortion at most `1/8` certifies restricted
isometry with constant `2/5` on that coordinate set.  The statement is
deterministic: random-matrix arguments supply the net condition separately.
-/
theorem restrictedIsometryOnSupport_of_unit_sphere_net_of_one_third_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (N : Finset (EuclideanSpace ℝ {i : Feature // i ∈ S}))
    (hnet : ∀ v, ‖v‖ = 1 → ∃ y ∈ N, ‖v - y‖ < (5 : ℝ) / 16)
    (hN_unit : ∀ y ∈ N, ‖y‖ = 1)
    (hN : ∀ y ∈ N,
      |AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement A (extendByZero S y.ofLp)) - 1| ≤ (1 : ℝ) / 8)
    {δ : ℝ} (hδ : (1 : ℝ) / 3 ≤ δ) :
    RestrictedIsometryOnSupport A S δ := by
  let L : EuclideanSpace ℝ {i : Feature // i ∈ S} →L[ℝ]
      EuclideanSpace ℝ Coord :=
    restrictedEuclideanMeasurement A S
  have hnetdist := AppliedModelingLib.Math.EuclideanNets.abs_norm_sq_sub_norm_sq_le_of_unit_sphere_net
      L N (5 / 16 : ℝ) (1 / 8 : ℝ) (by norm_num) (by norm_num) (by norm_num)
      hnet hN_unit (by
        intro y hy
        change |‖restrictedEuclideanMeasurement A S y‖ ^ 2 - 1| ≤ _
        rw [norm_sq_restrictedEuclideanMeasurement_eq_l2Sq_measurement_extendByZero]
        exact hN y hy)
  intro x hxsupp
  let v : EuclideanSpace ℝ {i : Feature // i ∈ S} :=
    WithLp.toLp 2 (fun i : {i : Feature // i ∈ S} => x i)
  have hvnorm : ‖v‖ ^ 2 = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
    calc
      ‖v‖ ^ 2 = AppliedModelingLib.FiniteDimensionalNorms.l2Sq v.ofLp :=
        norm_sq_eq_l2Sq_ofEuclideanSpace v
      _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i : {i : Feature // i ∈ S} => x i) := by
            simp [v]
      _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (extendByZero S (fun i : {i : Feature // i ∈ S} => x i)) := by
            exact (l2Sq_extendByZero S
              (fun i : {i : Feature // i ∈ S} => x i)).symm
      _ = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
            rw [extendByZero_subtype_eq_of_support_subset S x hxsupp]
  have hmeasure : ‖L v‖ ^ 2 =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) := by
    change ‖restrictedEuclideanMeasurement A S v‖ ^ 2 = _
    rw [norm_sq_restrictedEuclideanMeasurement_eq_l2Sq_measurement_extendByZero]
    change AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement A (extendByZero S
          (fun i : {i : Feature // i ∈ S} => x i))) = _
    rw [extendByZero_subtype_eq_of_support_subset S x hxsupp]
  have habs := hnetdist v
  change (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ∧
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) ≤
      (1 + δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x
  rw [hmeasure, hvnorm] at habs
  have hconstant : (1 / 8 : ℝ) / (1 - 2 * (5 / 16 : ℝ)) = 1 / 3 := by norm_num
  rw [hconstant] at habs
  constructor
  · have hnonneg := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x
    have hdelta_mul : (1 / 3 : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x :=
      mul_le_mul_of_nonneg_right hδ hnonneg
    rw [abs_le] at habs
    linarith
  · have hnonneg := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x
    have hdelta_mul : (1 / 3 : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x :=
      mul_le_mul_of_nonneg_right hδ hnonneg
    rw [abs_le] at habs
    linarith

/-- A `5/16` net with `1/8` distortion yields supportwise RIP with constant `3/8`. -/
theorem restrictedIsometryOnSupport_three_eighths_of_unit_sphere_net
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (N : Finset (EuclideanSpace ℝ {i : Feature // i ∈ S}))
    (hnet : ∀ v, ‖v‖ = 1 → ∃ y ∈ N, ‖v - y‖ < (5 : ℝ) / 16)
    (hN_unit : ∀ y ∈ N, ‖y‖ = 1)
    (hN : ∀ y ∈ N,
      |AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement A (extendByZero S y.ofLp)) - 1| ≤ (1 : ℝ) / 8) :
    RestrictedIsometryOnSupport A S (3 / 8 : ℝ) :=
  restrictedIsometryOnSupport_of_unit_sphere_net_of_one_third_le
    A S N hnet hN_unit hN (by norm_num)

/-- A `5/16` net with `1/8` distortion yields supportwise RIP with constant `2/5`. -/
theorem restrictedIsometryOnSupport_two_fifths_of_unit_sphere_net
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature)
    (N : Finset (EuclideanSpace ℝ {i : Feature // i ∈ S}))
    (hnet : ∀ v, ‖v‖ = 1 → ∃ y ∈ N, ‖v - y‖ < (5 : ℝ) / 16)
    (hN_unit : ∀ y ∈ N, ‖y‖ = 1)
    (hN : ∀ y ∈ N,
      |AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement A (extendByZero S y.ofLp)) - 1| ≤ (1 : ℝ) / 8) :
    RestrictedIsometryOnSupport A S (2 / 5 : ℝ) :=
  restrictedIsometryOnSupport_of_unit_sphere_net_of_one_third_le
    A S N hnet hN_unit hN (by norm_num)

theorem restrictedIsometryProperty_iff_forall_support_card_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ} :
    RestrictedIsometryProperty A s δ ↔
      ∀ S : Finset Feature, S.card ≤ s →
        RestrictedIsometryOnSupport A S δ := by
  constructor
  · intro hrip S hS x hx
    exact hrip x ((Finset.card_le_card hx).trans hS)
  · intro hsupport x hx
    exact hsupport (support x) hx x (by intro i hi; exact hi)

theorem restrictedIsometryProperty_of_forall_support_card_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ}
    (h :
      ∀ S : Finset Feature, S.card ≤ s →
        RestrictedIsometryOnSupport A S δ) :
    RestrictedIsometryProperty A s δ :=
  restrictedIsometryProperty_iff_forall_support_card_le.mpr h

theorem restrictedIsometryProperty_iff_forall_supportFinsetsCardLe
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ} :
    RestrictedIsometryProperty A s δ ↔
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        RestrictedIsometryOnSupport A S δ := by
  rw [restrictedIsometryProperty_iff_forall_support_card_le]
  constructor
  · intro h S hS
    exact h S (mem_supportFinsetsCardLe.mp hS)
  · intro h S hS
    exact h S (mem_supportFinsetsCardLe.mpr hS)

theorem restrictedIsometryProperty_of_forall_supportFinsetsCardLe
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ}
    (h :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        RestrictedIsometryOnSupport A S δ) :
    RestrictedIsometryProperty A s δ :=
  restrictedIsometryProperty_iff_forall_supportFinsetsCardLe.mpr h

theorem nullspaceProperty_mono
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) (hnsp : NullspaceProperty A k₂) :
    NullspaceProperty A k₁ := by
  intro h hker hnonzero S hS
  exact hnsp h hker hnonzero S (hS.trans hk)

theorem sparseKernelFree_mono
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s₁ s₂ : ℕ}
    (hs : s₁ ≤ s₂) (hfree : SparseKernelFree A s₂) :
    SparseKernelFree A s₁ := by
  intro x hx hker
  exact hfree x (hx.trans hs) hker

theorem basisPursuitExactRecovery_mono
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) (hbp : BasisPursuitExactRecovery A k₂) :
    BasisPursuitExactRecovery A k₁ := by
  intro z hz z' hmeas hl1
  exact hbp z (hz.trans hk) z' hmeas hl1

theorem restrictedIsometryProperty_mono
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s₁ s₂ : ℕ} {δ : ℝ}
    (hs : s₁ ≤ s₂) (hrip : RestrictedIsometryProperty A s₂ δ) :
    RestrictedIsometryProperty A s₁ δ := by
  intro x hx
  exact hrip x (hx.trans hs)

/-- Unit-box convention `z in [-1,1]^m`, stated as absolute-value bounds. -/
def InUnitBox (z : Feature → ℝ) : Prop :=
  ∀ i, |z i| ≤ 1

/-- Boolean feature vectors, represented over reals. -/
def InZeroOne (z : Feature → ℝ) : Prop :=
  ∀ i, z i = 0 ∨ z i = 1

/-- The `{0,1}` indicator vector of a finite feature set. -/
def finsetIndicator [DecidableEq Feature] (T : Finset Feature) : Feature → ℝ :=
  fun i => if i ∈ T then 1 else 0

/-- Coordinate `i` of `B^T A z`, written using representation and probe columns. -/
def linearProbe [Fintype Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (z : Feature → ℝ) (i : Feature) : ℝ :=
  ∑ j, z j * inner (B i) (A j)

/-- Paper-style coordinatewise `l_infty` recovery error. -/
def SupErrorLt [Fintype Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (z : Feature → ℝ) (ε : ℝ) : Prop :=
  ∀ i, |linearProbe A B z i - z i| < ε

/-- The exact identity representation, using the feature type as coordinates. -/
def featureIdentityMatrix [DecidableEq Feature] : Feature → Feature → ℝ :=
  fun i r => if r = i then 1 else 0

@[simp] theorem inner_featureIdentityMatrix
    [Fintype Feature] [DecidableEq Feature] (i j : Feature) :
    inner (featureIdentityMatrix i) (featureIdentityMatrix j) =
      if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp [inner, featureIdentityMatrix]
  · have hzero :
        (∑ r : Feature,
          featureIdentityMatrix i r * featureIdentityMatrix j r) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro r _hr
      by_cases hri : r = i
      · have hrj : r ≠ j := by
          intro h
          exact hij (hri.symm.trans h)
        simp [featureIdentityMatrix, hri, hij]
      · simp [featureIdentityMatrix, hri]
    simp [inner, hzero, hij]

@[simp] theorem linearProbe_featureIdentityMatrix
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) (i : Feature) :
    linearProbe featureIdentityMatrix featureIdentityMatrix z i = z i := by
  classical
  simp [linearProbe]

@[simp] theorem measurement_featureIdentityMatrix
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) :
    measurement featureIdentityMatrix z = z := by
  classical
  funext r
  simp [measurement, featureIdentityMatrix]

theorem basisPursuitExactRecovery_featureIdentityMatrix
    [Fintype Feature] [DecidableEq Feature] (k : ℕ) :
    BasisPursuitExactRecovery
      (featureIdentityMatrix : Feature → Feature → ℝ) k := by
  intro z _hz z' hmeas _hl1
  simpa using hmeas

theorem supErrorLt_featureIdentityMatrix
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    SupErrorLt featureIdentityMatrix featureIdentityMatrix z ε := by
  intro i
  simp [hε]

/--
Non-strict incoherence with unit columns.  The paper states strict
off-diagonal bounds; this closed version is the reusable deterministic lemma
target, and strict source bounds can feed it by weakening.
-/
structure MuIncoherentLE [Fintype Coord]
    (A : Feature → Coord → ℝ) (μ : ℝ) : Prop where
  self_inner : ∀ i, inner (A i) (A i) = 1
  offdiag_abs_le : ∀ ⦃i j⦄, i ≠ j → |inner (A i) (A j)| ≤ μ

@[simp] theorem mem_support [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {i : Feature} :
    i ∈ support z ↔ z i ≠ 0 := by
  simp [support]

theorem not_mem_support_iff [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {i : Feature} :
    i ∉ support z ↔ z i = 0 := by
  rw [mem_support, not_ne_iff]

/--
The `k` largest nonzero coordinates of `z` by absolute value, with
deterministic tie-breaking from `FiniteRanking.topRankFinset`.
-/
noncomputable def topAbsSupportFinset
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (k : ℕ) : Finset Feature :=
  AppliedModelingLib.FiniteRanking.topRankFinset (support z) (fun i => |z i|) k

theorem topAbsSupportFinset_subset_support
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (k : ℕ) :
    topAbsSupportFinset z k ⊆ support z := by
  classical
  exact AppliedModelingLib.FiniteRanking.topRankFinset_subset
    (support z) (fun i => |z i|) k

theorem topAbsSupportFinset_card_le
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (k : ℕ) :
    (topAbsSupportFinset z k).card ≤ k := by
  classical
  exact AppliedModelingLib.FiniteRanking.topRankFinset_card_le
    (support z) (fun i => |z i|) k

theorem outside_topAbsSupport_abs_le_inside_topAbsSupport_abs
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (k : ℕ) :
    ∀ high : Feature, high ∈ topAbsSupportFinset z k →
      ∀ low : Feature, low ∈ support z \ topAbsSupportFinset z k →
        |z low| ≤ |z high| := by
  classical
  exact AppliedModelingLib.FiniteRanking.outside_topRank_value_le_inside_topRank_value
    (support z) (fun i => |z i|) k

/--
Descending blocks of the nonzero support ordered by absolute coordinate size.
Block `0` is the largest `width` nonzero coordinates, block `1` is the next
`width`, and so on.
-/
noncomputable def absSupportRankBlockFinset
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) : Finset Feature :=
  AppliedModelingLib.FiniteRanking.descendingRankBlockFinset
    (support z) (fun i => |z i|) width block

theorem absSupportRankBlockFinset_subset_support
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) :
    absSupportRankBlockFinset z width block ⊆ support z := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_subset
    (support z) (fun i => |z i|) width block

theorem absSupportRankBlockFinset_card_le_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) :
    (absSupportRankBlockFinset z width block).card ≤ width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_card_le_width
    (support z) (fun i => |z i|) width block

theorem absSupportRankBlockFinset_card_eq_width_of_le
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) {width block : ℕ}
    (hblock : (block + 1) * width ≤ (support z).card) :
    (absSupportRankBlockFinset z width block).card = width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_card_eq_width_of_le
    (support z) (fun i => |z i|) hblock

theorem next_absSupportRankBlock_abs_le_current
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) :
    ∀ high : Feature, high ∈ absSupportRankBlockFinset z width block →
      ∀ low : Feature, low ∈ absSupportRankBlockFinset z width (block + 1) →
        |z low| ≤ |z high| := by
  classical
  exact AppliedModelingLib.FiniteRanking.next_descendingRankBlock_value_le_current
    (support z) (fun i => |z i|) width block

theorem disjoint_absSupportRankBlockFinset_next
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) :
    Disjoint (absSupportRankBlockFinset z width (block + 1))
      (absSupportRankBlockFinset z width block) := by
  classical
  simpa [absSupportRankBlockFinset,
    AppliedModelingLib.FiniteRanking.descendingRankBlockFinset, Nat.add_assoc] using
    AppliedModelingLib.FiniteRanking.disjoint_rankIntervalFinset_of_le
      (s := support z) (value := fun i => |z i|) (hcard := rfl)
      (lo₁ := (support z).card - (block + 2) * width)
      (hi₁ := (support z).card - (block + 1) * width)
      (lo₂ := (support z).card - (block + 1) * width)
      (hi₂ := (support z).card - block * width)
      (le_rfl)

theorem disjoint_absSupportRankBlockFinset_of_lt
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width : ℕ) {higher lower : ℕ}
    (hblock : higher < lower) :
    Disjoint (absSupportRankBlockFinset z width lower)
      (absSupportRankBlockFinset z width higher) := by
  classical
  exact AppliedModelingLib.FiniteRanking.disjoint_descendingRankBlockFinset_of_lt
    (support z) (fun i => |z i|) width hblock

theorem absSupportRankBlockFinset_zero_eq_topAbsSupportFinset
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width : ℕ) :
    absSupportRankBlockFinset z width 0 = topAbsSupportFinset z width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_zero_eq_topRankFinset
    (support z) (fun i => |z i|) width

theorem abs_le_l1On_absSupportRankBlock_div_of_mem_next
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {width block : ℕ} {low : Feature}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ (support z).card)
    (hlow : low ∈ absSupportRankBlockFinset z width (block + 1)) :
    |z low| ≤ l1On (absSupportRankBlockFinset z width block) z / (width : ℝ) := by
  classical
  let T := absSupportRankBlockFinset z width block
  have hcard : T.card = width := by
    simpa [T] using
      absSupportRankBlockFinset_card_eq_width_of_le (z := z) hblock
  have hle_each : ∀ high ∈ T, |z low| ≤ |z high| := by
    intro high hhigh
    exact next_absSupportRankBlock_abs_le_current z width block
      high (by simpa [T] using hhigh) low hlow
  have hsum :
      (∑ high ∈ T, |z low|) ≤ ∑ high ∈ T, |z high| := by
    exact Finset.sum_le_sum hle_each
  have hleft : (∑ high ∈ T, |z low|) = (width : ℝ) * |z low| := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [hcard]
  have hmul : (width : ℝ) * |z low| ≤ l1On T z := by
    rw [l1On]
    simpa [hleft] using hsum
  have hwidth_real : 0 < (width : ℝ) := by exact_mod_cast hwidth
  rw [le_div_iff₀ hwidth_real]
  simpa [T, mul_comm] using hmul

theorem l2SqOn_absSupportRankBlock_next_le_l1On_mul_current_avg
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {width block : ℕ}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ (support z).card) :
    l2SqOn (absSupportRankBlockFinset z width (block + 1)) z ≤
      l1On (absSupportRankBlockFinset z width (block + 1)) z *
        (l1On (absSupportRankBlockFinset z width block) z / (width : ℝ)) := by
  classical
  let avg := l1On (absSupportRankBlockFinset z width block) z / (width : ℝ)
  calc
    l2SqOn (absSupportRankBlockFinset z width (block + 1)) z =
        ∑ i ∈ absSupportRankBlockFinset z width (block + 1), z i ^ 2 := rfl
    _ ≤ ∑ i ∈ absSupportRankBlockFinset z width (block + 1), |z i| * avg := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hbound : |z i| ≤ avg := by
          simpa [avg] using
            abs_le_l1On_absSupportRankBlock_div_of_mem_next
              (z := z) (width := width) (block := block) (low := i)
              hwidth hblock hi
        calc
          z i ^ 2 = |z i| * |z i| := by
            rw [← sq_abs]
            ring
          _ ≤ |z i| * avg :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg (z i))
    _ = l1On (absSupportRankBlockFinset z width (block + 1)) z * avg := by
        rw [l1On, Finset.sum_mul]

theorem abs_le_l1On_topAbsSupport_div_of_mem_support_sdiff
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {k : ℕ} {low : Feature}
    (hk : 0 < k)
    (hcard : (topAbsSupportFinset z k).card = k)
    (hlow : low ∈ support z \ topAbsSupportFinset z k) :
    |z low| ≤ l1On (topAbsSupportFinset z k) z / (k : ℝ) := by
  classical
  let T := topAbsSupportFinset z k
  have hle_each : ∀ high ∈ T, |z low| ≤ |z high| := by
    intro high hhigh
    exact outside_topAbsSupport_abs_le_inside_topAbsSupport_abs z k
      high (by simpa [T] using hhigh)
      low (by simpa [T] using hlow)
  have hsum :
      (∑ high ∈ T, |z low|) ≤ ∑ high ∈ T, |z high| := by
    exact Finset.sum_le_sum hle_each
  have hleft : (∑ high ∈ T, |z low|) = (k : ℝ) * |z low| := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [T, hcard]
  have hmul : (k : ℝ) * |z low| ≤ l1On T z := by
    rw [l1On]
    simpa [hleft] using hsum
  have hk_real : 0 < (k : ℝ) := by
    exact_mod_cast hk
  rw [le_div_iff₀ hk_real]
  simpa [T, mul_comm] using hmul

theorem l2SqOn_le_l1On_mul_l1On_topAbsSupport_div_of_subset_support_sdiff
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {k : ℕ} {R : Finset Feature}
    (hk : 0 < k)
    (hcard : (topAbsSupportFinset z k).card = k)
    (hR : R ⊆ support z \ topAbsSupportFinset z k) :
    l2SqOn R z ≤
      l1On R z * (l1On (topAbsSupportFinset z k) z / (k : ℝ)) := by
  classical
  let avg := l1On (topAbsSupportFinset z k) z / (k : ℝ)
  calc
    l2SqOn R z = ∑ i ∈ R, z i ^ 2 := rfl
    _ ≤ ∑ i ∈ R, |z i| * avg := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have htail : i ∈ support z \ topAbsSupportFinset z k := hR hi
        have hbound : |z i| ≤ avg := by
          simpa [avg] using
            abs_le_l1On_topAbsSupport_div_of_mem_support_sdiff
              (z := z) (k := k) (low := i) hk hcard htail
        calc
          z i ^ 2 = |z i| * |z i| := by
            rw [← sq_abs]
            ring
          _ ≤ |z i| * avg :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg (z i))
    _ = l1On R z * avg := by
        rw [l1On, Finset.sum_mul]

/--
Descending fixed-width rank blocks of an arbitrary finite carrier, ordered by
absolute coordinate size.  This is the reusable tail-block primitive needed for
nullspace proofs, where the tail carrier is usually `support h \ S` for an
arbitrary `k`-set `S`.
-/
noncomputable def absRankBlockFinset
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width block : ℕ) :
    Finset Feature :=
  AppliedModelingLib.FiniteRanking.descendingRankBlockFinset
    carrier (fun i => |z i|) width block

theorem absRankBlockFinset_subset
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width block : ℕ) :
    absRankBlockFinset carrier z width block ⊆ carrier := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_subset
    carrier (fun i => |z i|) width block

theorem absRankBlockFinset_card_le_width
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width block : ℕ) :
    (absRankBlockFinset carrier z width block).card ≤ width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_card_le_width
    carrier (fun i => |z i|) width block

theorem absRankBlockFinset_card_eq_width_of_le
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) {width block : ℕ}
    (hblock : (block + 1) * width ≤ carrier.card) :
    (absRankBlockFinset carrier z width block).card = width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_card_eq_width_of_le
    carrier (fun i => |z i|) hblock

theorem exists_mem_absRankBlockFinset
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) {i : Feature} (hi : i ∈ carrier) :
    ∃ block : ℕ, i ∈ absRankBlockFinset carrier z width block := by
  classical
  exact AppliedModelingLib.FiniteRanking.exists_mem_descendingRankBlockFinset
    carrier (fun i => |z i|) hwidth hi

theorem exists_mem_absRankBlockFinset_lt_card
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) {i : Feature} (hi : i ∈ carrier) :
    ∃ block : ℕ, block < carrier.card ∧
      i ∈ absRankBlockFinset carrier z width block := by
  classical
  exact AppliedModelingLib.FiniteRanking.exists_mem_descendingRankBlockFinset_lt_card
    carrier (fun i => |z i|) hwidth hi

theorem pairwiseDisjoint_absRankBlockFinset_range_card
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width : ℕ) :
    (↑(Finset.range carrier.card) : Set ℕ).PairwiseDisjoint
      (fun block => absRankBlockFinset carrier z width block) := by
  classical
  intro a _ha b _hb hne
  by_cases hab : a < b
  · exact (by
      simpa [absRankBlockFinset] using
        (AppliedModelingLib.FiniteRanking.disjoint_descendingRankBlockFinset_of_lt
          carrier (fun i => |z i|) width
          (higher := a) (lower := b) hab).symm)
  · have hba : b < a := by
      exact Nat.lt_of_le_of_ne (le_of_not_gt hab) hne.symm
    simpa [absRankBlockFinset] using
      AppliedModelingLib.FiniteRanking.disjoint_descendingRankBlockFinset_of_lt
        carrier (fun i => |z i|) width
        (higher := b) (lower := a) hba

theorem biUnion_absRankBlockFinset_range_card_eq
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    (Finset.range carrier.card).biUnion
        (fun block => absRankBlockFinset carrier z width block) =
      carrier := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_biUnion.mp hi with ⟨block, _hblock, hi_block⟩
    exact absRankBlockFinset_subset carrier z width block hi_block
  · intro hi
    rcases exists_mem_absRankBlockFinset_lt_card
        (carrier := carrier) (z := z) (width := width) hwidth hi with
      ⟨block, hblock_lt, hi_block⟩
    exact Finset.mem_biUnion.mpr
      ⟨block, Finset.mem_range.mpr hblock_lt, hi_block⟩

theorem l1On_eq_sum_l1On_absRankBlockFinset_range_card
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    l1On carrier z =
      ∑ block ∈ Finset.range carrier.card,
        l1On (absRankBlockFinset carrier z width block) z := by
  classical
  let blocks := fun block => absRankBlockFinset carrier z width block
  have hdisj :
      (↑(Finset.range carrier.card) : Set ℕ).PairwiseDisjoint blocks := by
    simpa [blocks] using
      pairwiseDisjoint_absRankBlockFinset_range_card carrier z width
  have hunion :
      (Finset.range carrier.card).biUnion blocks = carrier := by
    simpa [blocks] using
      biUnion_absRankBlockFinset_range_card_eq
        (carrier := carrier) (z := z) (width := width) hwidth
  calc
    l1On carrier z =
        ∑ i ∈ (Finset.range carrier.card).biUnion blocks, |z i| := by
          rw [hunion]
          rfl
    _ = ∑ block ∈ Finset.range carrier.card, ∑ i ∈ blocks block, |z i| := by
          exact Finset.sum_biUnion hdisj
    _ = ∑ block ∈ Finset.range carrier.card,
          l1On (absRankBlockFinset carrier z width block) z := by
          rfl

theorem restrictTo_eq_sum_restrictTo_absRankBlockFinset_range_card
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    restrictTo carrier z =
      fun i => ∑ block ∈ Finset.range carrier.card,
        restrictTo (absRankBlockFinset carrier z width block) z i := by
  classical
  funext i
  by_cases hicarrier : i ∈ carrier
  · rcases exists_mem_absRankBlockFinset_lt_card
        (carrier := carrier) (z := z) (width := width) hwidth hicarrier with
      ⟨block, hblock_lt, hiblock⟩
    have hblock_mem : block ∈ Finset.range carrier.card :=
      Finset.mem_range.mpr hblock_lt
    have hsum :
        (∑ b ∈ Finset.range carrier.card,
          restrictTo (absRankBlockFinset carrier z width b) z i) =
        restrictTo (absRankBlockFinset carrier z width block) z i := by
      refine Finset.sum_eq_single_of_mem block hblock_mem ?_
      intro b hb hne
      have hdisj :
          Disjoint (absRankBlockFinset carrier z width b)
            (absRankBlockFinset carrier z width block) :=
        pairwiseDisjoint_absRankBlockFinset_range_card carrier z width
          hb hblock_mem hne
      have hi_not : i ∉ absRankBlockFinset carrier z width b := by
        intro hib
        exact (Finset.disjoint_left.mp hdisj) hib hiblock
      simp [restrictTo, hi_not]
    rw [hsum]
    simp [restrictTo, hicarrier, hiblock]
  · have hsum_zero :
        (∑ b ∈ Finset.range carrier.card,
          restrictTo (absRankBlockFinset carrier z width b) z i) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro b _hb
      have hi_not_block : i ∉ absRankBlockFinset carrier z width b := by
        intro hib
        exact hicarrier (absRankBlockFinset_subset carrier z width b hib)
      simp [restrictTo, hi_not_block]
    rw [hsum_zero]
    simp [restrictTo, hicarrier]

theorem measurement_restrictTo_eq_sum_measurement_absRankBlockFinset_range_card
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {carrier : Finset Feature}
    {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    measurement A (restrictTo carrier z) =
      fun r => ∑ block ∈ Finset.range carrier.card,
        measurement A (restrictTo (absRankBlockFinset carrier z width block) z) r := by
  classical
  funext r
  have hvec :=
    restrictTo_eq_sum_restrictTo_absRankBlockFinset_range_card
      (carrier := carrier) (z := z) (width := width) hwidth
  rw [measurement]
  calc
    ∑ i : Feature, restrictTo carrier z i * A i r =
        ∑ i : Feature,
          (∑ block ∈ Finset.range carrier.card,
            restrictTo (absRankBlockFinset carrier z width block) z i) * A i r := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [congrFun hvec i]
    _ = ∑ i : Feature, ∑ block ∈ Finset.range carrier.card,
          restrictTo (absRankBlockFinset carrier z width block) z i * A i r := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.sum_mul]
    _ = ∑ block ∈ Finset.range carrier.card, ∑ i : Feature,
          restrictTo (absRankBlockFinset carrier z width block) z i * A i r := by
          rw [Finset.sum_comm]
    _ = ∑ block ∈ Finset.range carrier.card,
          measurement A (restrictTo (absRankBlockFinset carrier z width block) z) r := by
          rfl

theorem inner_measurement_restrictTo_eq_sum_inner_measurement_absRankBlockFinset_range_card
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {S carrier : Finset Feature}
    {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    inner (measurement A (restrictTo S z)) (measurement A (restrictTo carrier z)) =
      ∑ block ∈ Finset.range carrier.card,
        inner (measurement A (restrictTo S z))
          (measurement A (restrictTo (absRankBlockFinset carrier z width block) z)) := by
  classical
  let head := measurement A (restrictTo S z)
  have htail :=
    measurement_restrictTo_eq_sum_measurement_absRankBlockFinset_range_card
      (A := A) (carrier := carrier) (z := z) (width := width) hwidth
  unfold inner
  calc
    ∑ r : Coord, head r * measurement A (restrictTo carrier z) r =
        ∑ r : Coord, head r *
          (∑ block ∈ Finset.range carrier.card,
            measurement A
              (restrictTo (absRankBlockFinset carrier z width block) z) r) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [congrFun htail r]
    _ = ∑ r : Coord, ∑ block ∈ Finset.range carrier.card,
          head r *
            measurement A
              (restrictTo (absRankBlockFinset carrier z width block) z) r := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [Finset.mul_sum]
    _ = ∑ block ∈ Finset.range carrier.card, ∑ r : Coord,
          head r *
            measurement A
              (restrictTo (absRankBlockFinset carrier z width block) z) r := by
          rw [Finset.sum_comm]
    _ = ∑ block ∈ Finset.range carrier.card,
        inner (measurement A (restrictTo S z))
          (measurement A (restrictTo (absRankBlockFinset carrier z width block) z)) := by
          rfl

theorem abs_inner_measurement_restrictTo_tail_le_sum_abs_inner_blocks
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {S carrier : Finset Feature}
    {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    |inner (measurement A (restrictTo S z)) (measurement A (restrictTo carrier z))| ≤
      ∑ block ∈ Finset.range carrier.card,
        |inner (measurement A (restrictTo S z))
          (measurement A (restrictTo (absRankBlockFinset carrier z width block) z))| := by
  classical
  rw [
    inner_measurement_restrictTo_eq_sum_inner_measurement_absRankBlockFinset_range_card
      (A := A) (S := S) (carrier := carrier) (z := z) (width := width) hwidth]
  exact Finset.abs_sum_le_sum_abs _ _

theorem absRankBlockFinset_zero_eq_topRankFinset
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width : ℕ) :
    absRankBlockFinset carrier z width 0 =
      AppliedModelingLib.FiniteRanking.topRankFinset carrier (fun i => |z i|) width := by
  classical
  exact AppliedModelingLib.FiniteRanking.descendingRankBlockFinset_zero_eq_topRankFinset
    carrier (fun i => |z i|) width

theorem outside_absRankBlock_zero_abs_le_inside_absRankBlock_zero_abs
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width : ℕ) :
    ∀ high : Feature, high ∈ absRankBlockFinset carrier z width 0 →
      ∀ low : Feature, low ∈ carrier \ absRankBlockFinset carrier z width 0 →
        |z low| ≤ |z high| := by
  classical
  simpa [absRankBlockFinset_zero_eq_topRankFinset] using
    AppliedModelingLib.FiniteRanking.outside_topRank_value_le_inside_topRank_value
      carrier (fun i => |z i|) width

theorem abs_le_l1On_absRankBlock_zero_div_of_mem_carrier_sdiff
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ} {low : Feature}
    (hwidth : 0 < width)
    (hcard : (absRankBlockFinset carrier z width 0).card = width)
    (hlow : low ∈ carrier \ absRankBlockFinset carrier z width 0) :
    |z low| ≤ l1On (absRankBlockFinset carrier z width 0) z / (width : ℝ) := by
  classical
  let T := absRankBlockFinset carrier z width 0
  have hle_each : ∀ high ∈ T, |z low| ≤ |z high| := by
    intro high hhigh
    exact outside_absRankBlock_zero_abs_le_inside_absRankBlock_zero_abs
      carrier z width high (by simpa [T] using hhigh)
      low (by simpa [T] using hlow)
  have hsum :
      (∑ high ∈ T, |z low|) ≤ ∑ high ∈ T, |z high| := by
    exact Finset.sum_le_sum hle_each
  have hleft : (∑ high ∈ T, |z low|) = (width : ℝ) * |z low| := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [T, hcard]
  have hmul : (width : ℝ) * |z low| ≤ l1On T z := by
    rw [l1On]
    simpa [hleft] using hsum
  have hwidth_real : 0 < (width : ℝ) := by
    exact_mod_cast hwidth
  rw [le_div_iff₀ hwidth_real]
  simpa [T, mul_comm] using hmul

theorem l2SqOn_le_l1On_mul_l1On_absRankBlock_zero_div_of_subset_carrier_sdiff
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    {R : Finset Feature}
    (hwidth : 0 < width)
    (hcard : (absRankBlockFinset carrier z width 0).card = width)
    (hR : R ⊆ carrier \ absRankBlockFinset carrier z width 0) :
    l2SqOn R z ≤
      l1On R z *
        (l1On (absRankBlockFinset carrier z width 0) z / (width : ℝ)) := by
  classical
  let avg := l1On (absRankBlockFinset carrier z width 0) z / (width : ℝ)
  calc
    l2SqOn R z = ∑ i ∈ R, z i ^ 2 := rfl
    _ ≤ ∑ i ∈ R, |z i| * avg := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have htail : i ∈ carrier \ absRankBlockFinset carrier z width 0 :=
          hR hi
        have hbound : |z i| ≤ avg := by
          simpa [avg] using
            abs_le_l1On_absRankBlock_zero_div_of_mem_carrier_sdiff
              (carrier := carrier) (z := z) (width := width) (low := i)
              hwidth hcard htail
        calc
          z i ^ 2 = |z i| * |z i| := by
            rw [← sq_abs]
            ring
          _ ≤ |z i| * avg :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg (z i))
    _ = l1On R z * avg := by
        rw [l1On, Finset.sum_mul]

theorem disjoint_left_of_subset_compl
    [Fintype Feature] [DecidableEq Feature] {S T : Finset Feature}
    (hT : T ⊆ Sᶜ) :
    Disjoint S T := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro i hiS hiT
  have hi_notS : i ∉ S := by
    simpa using hT hiT
  exact hi_notS hiS

theorem disjoint_absRankBlockFinset_of_subset_compl
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {S carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hcarrier : carrier ⊆ Sᶜ) :
    Disjoint S (absRankBlockFinset carrier z width block) := by
  exact disjoint_left_of_subset_compl
    ((absRankBlockFinset_subset carrier z width block).trans hcarrier)

theorem disjoint_absRankBlockFinset_of_lt
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width : ℕ)
    {higher lower : ℕ} (hblock : higher < lower) :
    Disjoint (absRankBlockFinset carrier z width lower)
      (absRankBlockFinset carrier z width higher) := by
  classical
  exact AppliedModelingLib.FiniteRanking.disjoint_descendingRankBlockFinset_of_lt
    carrier (fun i => |z i|) width hblock

theorem next_absRankBlock_abs_le_current
    [LinearOrder Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width block : ℕ) :
    ∀ high : Feature, high ∈ absRankBlockFinset carrier z width block →
      ∀ low : Feature, low ∈ absRankBlockFinset carrier z width (block + 1) →
        |z low| ≤ |z high| := by
  classical
  exact AppliedModelingLib.FiniteRanking.next_descendingRankBlock_value_le_current
    carrier (fun i => |z i|) width block

theorem abs_le_l1On_absRankBlock_div_of_mem_next
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ} {low : Feature}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ carrier.card)
    (hlow : low ∈ absRankBlockFinset carrier z width (block + 1)) :
    |z low| ≤ l1On (absRankBlockFinset carrier z width block) z / (width : ℝ) := by
  classical
  let T := absRankBlockFinset carrier z width block
  have hcard : T.card = width := by
    simpa [T] using
      absRankBlockFinset_card_eq_width_of_le
        (carrier := carrier) (z := z) hblock
  have hle_each : ∀ high ∈ T, |z low| ≤ |z high| := by
    intro high hhigh
    exact next_absRankBlock_abs_le_current carrier z width block
      high (by simpa [T] using hhigh) low hlow
  have hsum :
      (∑ high ∈ T, |z low|) ≤ ∑ high ∈ T, |z high| := by
    exact Finset.sum_le_sum hle_each
  have hleft : (∑ high ∈ T, |z low|) = (width : ℝ) * |z low| := by
    rw [Finset.sum_const, nsmul_eq_mul]
    simp [hcard]
  have hmul : (width : ℝ) * |z low| ≤ l1On T z := by
    rw [l1On]
    simpa [hleft] using hsum
  have hwidth_real : 0 < (width : ℝ) := by exact_mod_cast hwidth
  rw [le_div_iff₀ hwidth_real]
  simpa [T, mul_comm] using hmul

theorem l2SqOn_absRankBlock_next_le_l1On_mul_current_avg
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ carrier.card) :
    l2SqOn (absRankBlockFinset carrier z width (block + 1)) z ≤
      l1On (absRankBlockFinset carrier z width (block + 1)) z *
        (l1On (absRankBlockFinset carrier z width block) z / (width : ℝ)) := by
  classical
  let avg := l1On (absRankBlockFinset carrier z width block) z / (width : ℝ)
  calc
    l2SqOn (absRankBlockFinset carrier z width (block + 1)) z =
        ∑ i ∈ absRankBlockFinset carrier z width (block + 1), z i ^ 2 := rfl
    _ ≤ ∑ i ∈ absRankBlockFinset carrier z width (block + 1), |z i| * avg := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hbound : |z i| ≤ avg := by
          simpa [avg] using
            abs_le_l1On_absRankBlock_div_of_mem_next
              (carrier := carrier) (z := z) (width := width) (block := block)
              (low := i) hwidth hblock hi
        calc
          z i ^ 2 = |z i| * |z i| := by
            rw [← sq_abs]
            ring
          _ ≤ |z i| * avg :=
            mul_le_mul_of_nonneg_left hbound (abs_nonneg (z i))
    _ = l1On (absRankBlockFinset carrier z width (block + 1)) z * avg := by
        rw [l1On, Finset.sum_mul]

theorem l1On_absRankBlock_next_le_l1On_current
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ carrier.card) :
    l1On (absRankBlockFinset carrier z width (block + 1)) z ≤
      l1On (absRankBlockFinset carrier z width block) z := by
  classical
  let current := absRankBlockFinset carrier z width block
  let next := absRankBlockFinset carrier z width (block + 1)
  let avg := l1On current z / (width : ℝ)
  have hbound : ∀ i ∈ next, |z i| ≤ avg := by
    intro i hi
    simpa [current, next, avg] using
      abs_le_l1On_absRankBlock_div_of_mem_next
        (carrier := carrier) (z := z) (width := width) (block := block)
        (low := i) hwidth hblock (by simpa [next] using hi)
  have hsum :
      l1On next z ≤ (next.card : ℝ) * avg := by
    rw [l1On]
    calc
      (∑ i ∈ next, |z i|) ≤ ∑ _i ∈ next, avg := by
        exact Finset.sum_le_sum hbound
      _ = (next.card : ℝ) * avg := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (next.card : ℝ) ≤ (width : ℝ) := by
    exact_mod_cast absRankBlockFinset_card_le_width carrier z width (block + 1)
  have havg_nonneg : 0 ≤ avg := by
    dsimp [avg]
    exact div_nonneg (l1On_nonneg current z) (by exact_mod_cast Nat.zero_le width)
  have hmul :
      (next.card : ℝ) * avg ≤ (width : ℝ) * avg :=
    mul_le_mul_of_nonneg_right hcard havg_nonneg
  have hwidth_ne : (width : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwidth)
  calc
    l1On next z ≤ (next.card : ℝ) * avg := hsum
    _ ≤ (width : ℝ) * avg := hmul
    _ = l1On current z := by
      change (width : ℝ) * (l1On current z / (width : ℝ)) = l1On current z
      exact mul_div_cancel₀ (l1On current z) hwidth_ne

theorem l2SqOn_absRankBlock_next_le_l1On_current_sq_div
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hwidth : 0 < width)
    (hblock : (block + 1) * width ≤ carrier.card) :
    l2SqOn (absRankBlockFinset carrier z width (block + 1)) z ≤
      l1On (absRankBlockFinset carrier z width block) z ^ 2 / (width : ℝ) := by
  classical
  let current := absRankBlockFinset carrier z width block
  let next := absRankBlockFinset carrier z width (block + 1)
  let avg := l1On current z / (width : ℝ)
  have hbase :
      l2SqOn next z ≤ l1On next z * avg := by
    simpa [current, next, avg] using
      l2SqOn_absRankBlock_next_le_l1On_mul_current_avg
        (carrier := carrier) (z := z) (width := width) (block := block)
        hwidth hblock
  have hl1 :
      l1On next z ≤ l1On current z := by
    simpa [current, next] using
      l1On_absRankBlock_next_le_l1On_current
        (carrier := carrier) (z := z) (width := width) (block := block)
        hwidth hblock
  have havg_nonneg : 0 ≤ avg := by
    dsimp [avg]
    exact div_nonneg (l1On_nonneg current z) (by exact_mod_cast Nat.zero_le width)
  have hmul :
      l1On next z * avg ≤ l1On current z * avg :=
    mul_le_mul_of_nonneg_right hl1 havg_nonneg
  have hwidth_ne : (width : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hwidth)
  calc
    l2SqOn next z ≤ l1On next z * avg := hbase
    _ ≤ l1On current z * avg := hmul
    _ = l1On current z ^ 2 / (width : ℝ) := by
      ring

@[simp] theorem restrictTo_apply_mem [DecidableEq Feature]
    {S : Finset Feature} {z : Feature → ℝ} {i : Feature} (hi : i ∈ S) :
    restrictTo S z i = z i := by
  simp [restrictTo, hi]

@[simp] theorem restrictTo_apply_not_mem [DecidableEq Feature]
    {S : Finset Feature} {z : Feature → ℝ} {i : Feature} (hi : i ∉ S) :
    restrictTo S z i = 0 := by
  simp [restrictTo, hi]

theorem support_restrictTo_subset
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    support (restrictTo S z) ⊆ S := by
  intro i hi
  by_contra hnot
  have hz : restrictTo S z i = 0 := restrictTo_apply_not_mem hnot
  exact (mem_support.mp hi) hz

theorem kSparse_restrictTo_of_card_le
    [Fintype Feature] [DecidableEq Feature]
    {S : Finset Feature} {z : Feature → ℝ} {k : ℕ}
    (hS : S.card ≤ k) :
    KSparse k (restrictTo S z) := by
  dsimp [KSparse]
  exact (Finset.card_le_card (support_restrictTo_subset S z)).trans hS

theorem kSparse_restrictTo_absRankBlockFinset
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (carrier : Finset Feature) (z : Feature → ℝ) (width block : ℕ) :
    KSparse width (restrictTo (absRankBlockFinset carrier z width block) z) :=
  kSparse_restrictTo_of_card_le
    (absRankBlockFinset_card_le_width carrier z width block)

theorem kSparse_restrictTo_absSupportRankBlockFinset
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) (width block : ℕ) :
    KSparse width (restrictTo (absSupportRankBlockFinset z width block) z) :=
  kSparse_restrictTo_of_card_le
    (absSupportRankBlockFinset_card_le_width z width block)

theorem kSparse_of_card_le_and_tail_card_le
    [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {S : Finset Feature} {k : ℕ}
    (hS : S.card ≤ k) (htail : (support z \ S).card ≤ k) :
    KSparse (2 * k) z := by
  classical
  dsimp [KSparse]
  have hsubset : support z ⊆ S ∪ (support z \ S) := by
    intro i hi
    by_cases hiS : i ∈ S
    · exact Finset.mem_union.mpr (Or.inl hiS)
    · exact Finset.mem_union.mpr
        (Or.inr (Finset.mem_sdiff.mpr ⟨hi, hiS⟩))
  have hcard_union :
      (S ∪ (support z \ S)).card ≤ S.card + (support z \ S).card :=
    Finset.card_union_le S (support z \ S)
  calc
    (support z).card ≤ (S ∪ (support z \ S)).card :=
      Finset.card_le_card hsubset
    _ ≤ S.card + (support z \ S).card := hcard_union
    _ ≤ k + k := Nat.add_le_add hS htail
    _ = 2 * k := by omega

theorem disjoint_support_restrictTo_of_disjoint
    [Fintype Feature] [DecidableEq Feature]
    {S T : Finset Feature} {z : Feature → ℝ}
    (hdisj : Disjoint S T) :
    Disjoint (support (restrictTo S z)) (support (restrictTo T z)) := by
  rw [Finset.disjoint_left]
  intro i hiS hiT
  exact (Finset.disjoint_left.mp hdisj)
    (support_restrictTo_subset S z hiS)
    (support_restrictTo_subset T z hiT)

theorem support_union_restrictTo_card_le_add
    [Fintype Feature] [DecidableEq Feature]
    {S T : Finset Feature} {z : Feature → ℝ} {s t : ℕ}
    (hS : S.card ≤ s) (hT : T.card ≤ t) :
    (support (restrictTo S z) ∪ support (restrictTo T z)).card ≤ s + t := by
  have hsubset :
      support (restrictTo S z) ∪ support (restrictTo T z) ⊆ S ∪ T :=
    Finset.union_subset_union
      (support_restrictTo_subset S z) (support_restrictTo_subset T z)
  have hcard_subset :
      (support (restrictTo S z) ∪ support (restrictTo T z)).card ≤
        (S ∪ T).card :=
    Finset.card_le_card hsubset
  have hunion : (S ∪ T).card ≤ S.card + T.card :=
    Finset.card_union_le S T
  exact hcard_subset.trans (hunion.trans (by omega))

theorem restrictTo_add_compl
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    (fun i => restrictTo S z i + restrictTo Sᶜ z i) = z := by
  funext i
  by_cases hi : i ∈ S
  · have hic : i ∉ Sᶜ := by simpa using hi
    simp [hi, hic]
  · have hic : i ∈ Sᶜ := by simpa using hi
    simp [hi, hic]

theorem restrictTo_compl_eq_restrictTo_support_sdiff
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    restrictTo Sᶜ z = restrictTo (support z \ S) z := by
  classical
  funext i
  by_cases hiS : i ∈ S
  · have hiSc : i ∉ Sᶜ := by simpa using hiS
    have hiTail : i ∉ support z \ S := by
      intro hi
      exact (Finset.mem_sdiff.mp hi).2 hiS
    simp [restrictTo, hiSc, hiTail]
  · have hiSc : i ∈ Sᶜ := by simpa using hiS
    by_cases hisupp : i ∈ support z
    · have hiTail : i ∈ support z \ S := Finset.mem_sdiff.mpr ⟨hisupp, hiS⟩
      simp [restrictTo, hiSc, hiTail]
    · have hiTail : i ∉ support z \ S := by
        intro hi
        exact hisupp (Finset.mem_sdiff.mp hi).1
      have hz : z i = 0 := not_mem_support_iff.mp hisupp
      simp [restrictTo, hiSc, hiTail, hz]

theorem restrictTo_sub
    [DecidableEq Feature] (S : Finset Feature)
    (x y : Feature → ℝ) :
    restrictTo S (fun i => x i - y i) =
      fun i => restrictTo S x i - restrictTo S y i := by
  funext i
  by_cases hi : i ∈ S <;> simp [restrictTo, hi]

theorem support_add_subset_union
    [Fintype Feature] [DecidableEq Feature]
    (x y : Feature → ℝ) :
    support (fun i => x i + y i) ⊆ support x ∪ support y := by
  intro i hi
  by_contra hnot
  have hnotx : i ∉ support x := by
    intro hx
    exact hnot (Finset.mem_union_left _ hx)
  have hnoty : i ∉ support y := by
    intro hy
    exact hnot (Finset.mem_union_right _ hy)
  have hx_zero : x i = 0 := not_mem_support_iff.mp hnotx
  have hy_zero : y i = 0 := not_mem_support_iff.mp hnoty
  have hzero : (fun i => x i + y i) i = 0 := by
    simp [hx_zero, hy_zero]
  exact (mem_support.mp hi) hzero

theorem support_smul_subset
    [Fintype Feature] [DecidableEq Feature]
    (a : ℝ) (x : Feature → ℝ) :
    support (fun i => a * x i) ⊆ support x := by
  intro i hi
  by_contra hnot
  have hx : x i = 0 := not_mem_support_iff.mp hnot
  have hzero : (fun i => a * x i) i = 0 := by simp [hx]
  exact (mem_support.mp hi) hzero

theorem support_sub_subset_union
    [Fintype Feature] [DecidableEq Feature]
    (x y : Feature → ℝ) :
    support (fun i => x i - y i) ⊆ support x ∪ support y := by
  intro i hi
  by_contra hnot
  have hnotx : i ∉ support x := by
    intro hx
    exact hnot (Finset.mem_union_left _ hx)
  have hnoty : i ∉ support y := by
    intro hy
    exact hnot (Finset.mem_union_right _ hy)
  have hx_zero : x i = 0 := not_mem_support_iff.mp hnotx
  have hy_zero : y i = 0 := not_mem_support_iff.mp hnoty
  have hzero : (fun i => x i - y i) i = 0 := by
    simp [hx_zero, hy_zero]
  exact (mem_support.mp hi) hzero

theorem kSparse_sub_of_kSparse
    [Fintype Feature] [DecidableEq Feature]
    {k : ℕ} {x y : Feature → ℝ}
    (hx : KSparse k x) (hy : KSparse k y) :
    KSparse (2 * k) (fun i => x i - y i) := by
  dsimp [KSparse] at hx hy ⊢
  have hsubset := support_sub_subset_union x y
  have hcard_subset :
      (support (fun i => x i - y i)).card ≤ (support x ∪ support y).card :=
    Finset.card_le_card hsubset
  have hunion :
      (support x ∪ support y).card ≤ (support x).card + (support y).card :=
    Finset.card_union_le (support x) (support y)
  calc
    (support (fun i => x i - y i)).card ≤ (support x ∪ support y).card :=
      hcard_subset
    _ ≤ (support x).card + (support y).card := hunion
    _ ≤ 2 * k := by omega

theorem kSparse_add_of_support_union_card_le
    [Fintype Feature] [DecidableEq Feature]
    {s : ℕ} {x y : Feature → ℝ}
    (hcard : (support x ∪ support y).card ≤ s) :
    KSparse s (fun i => x i + y i) := by
  dsimp [KSparse]
  exact (Finset.card_le_card (support_add_subset_union x y)).trans hcard

theorem kSparse_sub_of_support_union_card_le
    [Fintype Feature] [DecidableEq Feature]
    {s : ℕ} {x y : Feature → ℝ}
    (hcard : (support x ∪ support y).card ≤ s) :
    KSparse s (fun i => x i - y i) := by
  dsimp [KSparse]
  exact (Finset.card_le_card (support_sub_subset_union x y)).trans hcard

theorem inner_eq_zero_of_disjoint_support
    [Fintype Feature] [DecidableEq Feature]
    {x y : Feature → ℝ}
    (hdisj : Disjoint (support x) (support y)) :
    inner x y = 0 := by
  classical
  rw [inner]
  refine Finset.sum_eq_zero ?_
  intro i _hi
  by_cases hx : x i = 0
  · simp [hx]
  · have hxi : i ∈ support x := mem_support.mpr hx
    have hy_not : i ∉ support y := (Finset.disjoint_left.mp hdisj) hxi
    have hy : y i = 0 := not_mem_support_iff.mp hy_not
    simp [hy]

theorem disjoint_support_smul_smul
    [Fintype Feature] [DecidableEq Feature]
    {x y : Feature → ℝ} (a b : ℝ)
    (hdisj : Disjoint (support x) (support y)) :
    Disjoint (support (fun i => a * x i)) (support (fun i => b * y i)) := by
  rw [Finset.disjoint_left]
  intro i hxi hyi
  have hxi' : i ∈ support x := support_smul_subset a x hxi
  have hyi' : i ∈ support y := support_smul_subset b y hyi
  exact (Finset.disjoint_left.mp hdisj) hxi' hyi'

theorem l2Sq_add_eq_of_disjoint_support
    [Fintype Feature] [DecidableEq Feature]
    {x y : Feature → ℝ}
    (hdisj : Disjoint (support x) (support y)) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun i => x i + y i) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq y := by
  rw [l2Sq_add_eq, inner_eq_zero_of_disjoint_support hdisj]
  ring

theorem l2Sq_sub_eq_of_disjoint_support
    [Fintype Feature] [DecidableEq Feature]
    {x y : Feature → ℝ}
    (hdisj : Disjoint (support x) (support y)) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun i => x i - y i) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq y := by
  rw [l2Sq_sub_eq, inner_eq_zero_of_disjoint_support hdisj]
  ring

theorem l2SqOn_nonneg
    [DecidableEq Feature] (S : Finset Feature) (z : Feature → ℝ) :
    0 ≤ l2SqOn S z := by
  rw [l2SqOn]
  exact Finset.sum_nonneg fun i _hi => sq_nonneg (z i)

theorem l2SqOn_le_l2Sq
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    l2SqOn S z ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq z := by
  rw [l2SqOn, AppliedModelingLib.FiniteDimensionalNorms.l2Sq]
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (by intro i hi; exact Finset.mem_univ i)
    (by intro i _hi_univ hi_not; exact sq_nonneg (z i))

theorem l2Sq_eq_l2SqOn_add_l2SqOn_compl
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq z =
      l2SqOn S z + l2SqOn Sᶜ z := by
  classical
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq, l2SqOn, l2SqOn]
  have hsplit :
      (∑ i : Feature, z i ^ 2) =
        (∑ i ∈ S, z i ^ 2) +
          ∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S), z i ^ 2 := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Feature))
        (p := fun i : Feature => i ∈ S)
        (f := fun i : Feature => z i ^ 2)).symm
  have hcompl :
      (Finset.univ.filter fun i : Feature => i ∉ S) = Sᶜ := by
    ext i
    simp
  rw [hsplit, hcompl]

theorem l2SqOn_compl_support_eq_zero
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) :
    l2SqOn (support z)ᶜ z = 0 := by
  classical
  rw [l2SqOn]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi_not : i ∉ support z := by
    simpa using hi
  have hz : z i = 0 := (not_mem_support_iff.mp hi_not)
  simp [hz]

theorem l2Sq_eq_l2SqOn_support
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq z = l2SqOn (support z) z := by
  rw [l2Sq_eq_l2SqOn_add_l2SqOn_compl (S := support z) z,
    l2SqOn_compl_support_eq_zero]
  ring

theorem l2SqOn_compl_eq_l2SqOn_support_sdiff
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    l2SqOn Sᶜ z = l2SqOn (support z \ S) z := by
  classical
  rw [l2SqOn, l2SqOn]
  have hsubset : support z \ S ⊆ Sᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
  have hsum :
      (∑ i ∈ support z \ S, z i ^ 2) =
        ∑ i ∈ Sᶜ, z i ^ 2 := by
    refine Finset.sum_subset hsubset ?_
    intro i hiSc hiTail
    have hi_notS : i ∉ S := by
      simpa using hiSc
    have hi_not_support : i ∉ support z := by
      intro hisupp
      exact hiTail (Finset.mem_sdiff.mpr ⟨hisupp, hi_notS⟩)
    have hz : z i = 0 := not_mem_support_iff.mp hi_not_support
    simp [hz]
  exact hsum.symm

/--
If every set of at most `q` coordinates has `l1` mass at most `L`, then the
whole vector has a finite `l2`-squared bound.  The proof keeps the `q` largest
coordinates in the head and bounds every remaining coordinate by the head
average.  This is useful when a combinatorial condition controls all small
subsets but the ambient vector need not be sparse.
-/
theorem l2Sq_le_sq_add_card_mul_sq_div_of_forall_l1On_card_le
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (z : Feature → ℝ) {q : ℕ} {L : ℝ}
    (hq : 0 < q) (hL : 0 ≤ L)
    (hsub : ∀ T : Finset Feature, T.card ≤ q → l1On T z ≤ L) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq z ≤
      L ^ 2 + (Fintype.card Feature : ℝ) * (L / (q : ℝ)) ^ 2 := by
  classical
  let S := support z
  by_cases hcard : S.card ≤ q
  · have hl1 : l1On S z ≤ L := hsub S hcard
    have hsq : l2SqOn S z ≤ (l1On S z) ^ 2 := by
      rw [l2SqOn, l1On]
      simpa [sq_abs] using
        (Finset.sum_sq_le_sq_sum_of_nonneg
          (s := S) (f := fun i => |z i|)
          (fun i _hi => abs_nonneg (z i)))
    have hLsq : (l1On S z) ^ 2 ≤ L ^ 2 := by
      exact sq_le_sq' (by
        have hnonneg := l1On_nonneg S z
        nlinarith) hl1
    have htail_nonneg :
        0 ≤ (Fintype.card Feature : ℝ) * (L / (q : ℝ)) ^ 2 :=
      mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [l2Sq_eq_l2SqOn_support]
    exact (hsq.trans hLsq).trans (by linarith)
  · have hqcard : q ≤ S.card := Nat.le_of_not_ge hcard
    let T := topAbsSupportFinset z q
    have hTcard : T.card = q := by
      simpa [T] using
        AppliedModelingLib.FiniteRanking.topRankFinset_card_eq_of_le
          (support z) (fun i => |z i|) hqcard
    have hl1T : l1On T z ≤ L := hsub T (by simpa [hTcard])
    have htop_sq : l2SqOn T z ≤ L ^ 2 := by
      have hsq : l2SqOn T z ≤ (l1On T z) ^ 2 := by
        rw [l2SqOn, l1On]
        simpa [sq_abs] using
          (Finset.sum_sq_le_sq_sum_of_nonneg
            (s := T) (f := fun i => |z i|)
            (fun i _hi => abs_nonneg (z i)))
      have hLsq : (l1On T z) ^ 2 ≤ L ^ 2 := by
        exact sq_le_sq' (by
          have hnonneg := l1On_nonneg T z
          nlinarith) hl1T
      exact hsq.trans hLsq
    have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
    have htail_point : ∀ i ∈ support z \ T, |z i| ≤ L / (q : ℝ) := by
      intro i hi
      have hbase :=
        abs_le_l1On_topAbsSupport_div_of_mem_support_sdiff
          (z := z) (k := q) (low := i) hq (by simpa [T] using hTcard)
          (by simpa [T] using hi)
      exact hbase.trans (div_le_div_of_nonneg_right hl1T hqreal.le)
    have htail_sq :
        l2SqOn (support z \ T) z ≤
          (Fintype.card Feature : ℝ) * (L / (q : ℝ)) ^ 2 := by
      rw [l2SqOn]
      calc
        (∑ i ∈ support z \ T, z i ^ 2) ≤
            ∑ _i ∈ support z \ T, (L / (q : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro i hi
          rw [← sq_abs]
          exact sq_le_sq' (by
            have hnonneg := abs_nonneg (z i)
            have hbound := htail_point i hi
            nlinarith) (htail_point i hi)
        _ = ((support z \ T).card : ℝ) * (L / (q : ℝ)) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (Fintype.card Feature : ℝ) * (L / (q : ℝ)) ^ 2 := by
          exact mul_le_mul_of_nonneg_right
            (by exact_mod_cast (Finset.card_le_univ (support z \ T)))
            (sq_nonneg _)
    rw [l2Sq_eq_l2SqOn_add_l2SqOn_compl (S := T) z,
      l2SqOn_compl_eq_l2SqOn_support_sdiff T z]
    exact add_le_add htop_sq htail_sq

theorem l2Sq_eq_l2SqOn_of_support_subset
    [Fintype Feature] [DecidableEq Feature]
    {S : Finset Feature} {z : Feature → ℝ}
    (hsubset : support z ⊆ S) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq z = l2SqOn S z := by
  classical
  rw [l2Sq_eq_l2SqOn_add_l2SqOn_compl (S := S) z]
  have hcompl_zero : l2SqOn Sᶜ z = 0 := by
    rw [l2SqOn]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_not : i ∉ S := by
      simpa using hi
    have hi_not_support : i ∉ support z := by
      intro hisupp
      exact hi_not (hsubset hisupp)
    have hz : z i = 0 := not_mem_support_iff.mp hi_not_support
    simp [hz]
  rw [hcompl_zero]
  ring

theorem l1On_le_sqrt_card_mul_sqrt_l2SqOn
    [DecidableEq Feature] (S : Finset Feature) (z : Feature → ℝ) :
    l1On S z ≤
      Real.sqrt (S.card : ℝ) * Real.sqrt (l2SqOn S z) := by
  rw [l1On, l2SqOn]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (s := S) (f := fun _i : Feature => 1)
    (g := fun i : Feature => |z i|)
  simpa [pow_two] using hcs

theorem l1On_le_sqrt_card_mul_l2
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    l1On S z ≤
      Real.sqrt (S.card : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l2 z := by
  have hbase := l1On_le_sqrt_card_mul_sqrt_l2SqOn S z
  have hsqrt :
      Real.sqrt (l2SqOn S z) ≤ AppliedModelingLib.FiniteDimensionalNorms.l2 z := by
    rw [AppliedModelingLib.FiniteDimensionalNorms.l2]
    exact Real.sqrt_le_sqrt (l2SqOn_le_l2Sq S z)
  have hcard_nonneg : 0 ≤ Real.sqrt (S.card : ℝ) := Real.sqrt_nonneg _
  exact hbase.trans
    (mul_le_mul_of_nonneg_left hsqrt hcard_nonneg)

theorem l1On_le_sqrt_card_mul_l2_restrictTo_of_subset
    [Fintype Feature] [DecidableEq Feature]
    {S T : Finset Feature} {z : Feature → ℝ}
    (hST : S ⊆ T) :
    l1On S z ≤
      Real.sqrt (S.card : ℝ) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo T z) := by
  calc
    l1On S z = l1On S (restrictTo T z) := by
      exact (l1On_restrictTo_eq_of_subset hST).symm
    _ ≤ Real.sqrt (S.card : ℝ) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo T z) :=
      l1On_le_sqrt_card_mul_l2 S (restrictTo T z)

theorem l1_restrictTo_eq_l1On
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l1 (restrictTo S z) = l1On S z := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l1, l1On]
  have hsplit :
      (∑ i : Feature, |restrictTo S z i|) =
        (∑ i ∈ S, |restrictTo S z i|) +
          ∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S),
            |restrictTo S z i| := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Feature))
        (p := fun i : Feature => i ∈ S)
        (f := fun i : Feature => |restrictTo S z i|)).symm
  have houtside :
      (∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S),
          |restrictTo S z i|) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_not : i ∉ S := by simpa using hi
    simp [restrictTo, hi_not]
  rw [hsplit, houtside, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [restrictTo, hi]

theorem l2Sq_restrictTo_eq_l2SqOn
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo S z) = l2SqOn S z := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2Sq, l2SqOn]
  have hsplit :
      (∑ i : Feature, restrictTo S z i ^ 2) =
        (∑ i ∈ S, restrictTo S z i ^ 2) +
          ∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S),
            restrictTo S z i ^ 2 := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Feature))
        (p := fun i : Feature => i ∈ S)
        (f := fun i : Feature => restrictTo S z i ^ 2)).symm
  have houtside :
      (∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S),
          restrictTo S z i ^ 2) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_not : i ∉ S := by simpa using hi
    simp [restrictTo, hi_not]
  rw [hsplit, houtside, add_zero]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp [restrictTo, hi]

theorem absRankBlockFinset_eq_empty_of_card_le_block_mul
    [LinearOrder Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hblock : carrier.card ≤ block * width) :
    absRankBlockFinset carrier z width block = ∅ := by
  classical
  ext a
  constructor
  · intro ha
    rw [absRankBlockFinset, AppliedModelingLib.FiniteRanking.descendingRankBlockFinset,
      AppliedModelingLib.FiniteRanking.rankIntervalFinset] at ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, _hia⟩
    have hbounds := (Finset.mem_filter.mp hi).2
    have hhi : carrier.card - block * width = 0 := Nat.sub_eq_zero_of_le hblock
    omega
  · intro ha
    simp at ha

theorem l2_restrictTo_absRankBlock_succ_le_l1On_current_div_sqrt_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width block : ℕ}
    (hwidth : 0 < width) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset carrier z width (block + 1)) z) ≤
      l1On (absRankBlockFinset carrier z width block) z /
        Real.sqrt (width : ℝ) := by
  classical
  by_cases hblock : (block + 1) * width ≤ carrier.card
  · let current := absRankBlockFinset carrier z width block
    let next := absRankBlockFinset carrier z width (block + 1)
    have hsq :
        l2SqOn next z ≤ l1On current z ^ 2 / (width : ℝ) := by
      simpa [current, next] using
        l2SqOn_absRankBlock_next_le_l1On_current_sq_div
          (carrier := carrier) (z := z) (width := width) (block := block)
          hwidth hblock
    have hsqrt := Real.sqrt_le_sqrt hsq
    have hcurrent_nonneg : 0 ≤ l1On current z := l1On_nonneg current z
    calc
      AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo next z) =
          Real.sqrt (l2SqOn next z) := by
          rw [AppliedModelingLib.FiniteDimensionalNorms.l2,
            l2Sq_restrictTo_eq_l2SqOn]
      _ ≤ Real.sqrt (l1On current z ^ 2 / (width : ℝ)) := hsqrt
      _ = l1On current z / Real.sqrt (width : ℝ) := by
          rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hcurrent_nonneg]
  · have hempty :
        absRankBlockFinset carrier z width (block + 1) = ∅ := by
      exact absRankBlockFinset_eq_empty_of_card_le_block_mul
        (carrier := carrier) (z := z) (width := width) (block := block + 1)
        (le_of_not_ge hblock)
    have hzero :
        restrictTo (absRankBlockFinset carrier z width (block + 1)) z =
          fun _ => 0 := by
      rw [hempty]
      funext i
      simp [restrictTo]
    have hright_nonneg :
        0 ≤ l1On (absRankBlockFinset carrier z width block) z /
          Real.sqrt (width : ℝ) := by
      exact div_nonneg
        (l1On_nonneg (absRankBlockFinset carrier z width block) z)
        (Real.sqrt_nonneg _)
    calc
      AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width (block + 1)) z) = 0 := by
          rw [hzero]
          exact AppliedModelingLib.FiniteDimensionalNorms.normL2_zero
      _ ≤ l1On (absRankBlockFinset carrier z width block) z /
          Real.sqrt (width : ℝ) := hright_nonneg

theorem sum_l2_restrictTo_absRankBlock_succ_le_l1On_div_sqrt_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    (∑ block ∈ Finset.range carrier.card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width (block + 1)) z)) ≤
      l1On carrier z / Real.sqrt (width : ℝ) := by
  classical
  have hterm :
      (∑ block ∈ Finset.range carrier.card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width (block + 1)) z)) ≤
        ∑ block ∈ Finset.range carrier.card,
          l1On (absRankBlockFinset carrier z width block) z /
            Real.sqrt (width : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro block _hblock
    exact
      l2_restrictTo_absRankBlock_succ_le_l1On_current_div_sqrt_width
        (carrier := carrier) (z := z) (width := width) (block := block) hwidth
  have hsum_eq :
      (∑ block ∈ Finset.range carrier.card,
          l1On (absRankBlockFinset carrier z width block) z /
            Real.sqrt (width : ℝ)) =
        l1On carrier z / Real.sqrt (width : ℝ) := by
    rw [← Finset.sum_div]
    rw [← l1On_eq_sum_l1On_absRankBlockFinset_range_card
      (carrier := carrier) (z := z) (width := width) hwidth]
  exact hterm.trans_eq hsum_eq

theorem sum_range_le_head_add_sum_succ
    {f : ℕ → ℝ} {n : ℕ} (hnonneg : ∀ i, 0 ≤ f i) :
    (∑ i ∈ Finset.range n, f i) ≤
      f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
  classical
  have hsubset : Finset.range n ⊆ Finset.range (n + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))
  have hle :
      (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range (n + 1), f i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by intro i _hi_large _hi_not_small; exact hnonneg i)
  calc
    (∑ i ∈ Finset.range n, f i) ≤ ∑ i ∈ Finset.range (n + 1), f i := hle
    _ = f 0 + ∑ i ∈ Finset.range n, f (i + 1) := by
      rw [Finset.sum_range_succ']
      ring

theorem sum_l2_restrictTo_absRankBlock_le_top_l2_add_l1On_div_sqrt_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width) :
    (∑ block ∈ Finset.range carrier.card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width block) z)) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset carrier z width 0) z) +
        l1On carrier z / Real.sqrt (width : ℝ) := by
  classical
  let f : ℕ → ℝ := fun block =>
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (restrictTo (absRankBlockFinset carrier z width block) z)
  have hnonneg : ∀ i, 0 ≤ f i := by
    intro i
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _
  have hsplit :
      (∑ block ∈ Finset.range carrier.card, f block) ≤
        f 0 + ∑ block ∈ Finset.range carrier.card, f (block + 1) :=
    sum_range_le_head_add_sum_succ (f := f) hnonneg
  have hsucc :
      (∑ block ∈ Finset.range carrier.card, f (block + 1)) ≤
        l1On carrier z / Real.sqrt (width : ℝ) := by
    simpa [f] using
      sum_l2_restrictTo_absRankBlock_succ_le_l1On_div_sqrt_width
        (carrier := carrier) (z := z) (width := width) hwidth
  calc
    (∑ block ∈ Finset.range carrier.card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width block) z)) =
        ∑ block ∈ Finset.range carrier.card, f block := rfl
    _ ≤ f 0 + ∑ block ∈ Finset.range carrier.card, f (block + 1) := hsplit
    _ ≤ f 0 + l1On carrier z / Real.sqrt (width : ℝ) :=
        (by
          have h := add_le_add_left hsucc (f 0)
          simpa [add_comm, add_left_comm, add_assoc] using h)
    _ = AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset carrier z width 0) z) +
        l1On carrier z / Real.sqrt (width : ℝ) := rfl

theorem l2_restrictTo_absRankBlock_zero_le_sqrt_l1On_mul_top_div_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {parent carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width)
    (htop_card : (absRankBlockFinset parent z width 0).card = width)
    (hcarrier : carrier ⊆ parent \ absRankBlockFinset parent z width 0) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset carrier z width 0) z) ≤
      Real.sqrt
        (l1On carrier z *
          (l1On (absRankBlockFinset parent z width 0) z / (width : ℝ))) := by
  classical
  let B := absRankBlockFinset carrier z width 0
  let T := absRankBlockFinset parent z width 0
  have hB_subset_parent_tail : B ⊆ parent \ T := by
    intro i hi
    exact hcarrier (absRankBlockFinset_subset carrier z width 0 hi)
  have hsq :
      l2SqOn B z ≤ l1On B z * (l1On T z / (width : ℝ)) := by
    simpa [B, T] using
      l2SqOn_le_l1On_mul_l1On_absRankBlock_zero_div_of_subset_carrier_sdiff
        (carrier := parent) (z := z) (width := width) (R := B)
        hwidth (by simpa [T] using htop_card) hB_subset_parent_tail
  have hB_l1_le : l1On B z ≤ l1On carrier z :=
    l1On_mono (absRankBlockFinset_subset carrier z width 0)
  have havg_nonneg : 0 ≤ l1On T z / (width : ℝ) := by
    exact div_nonneg (l1On_nonneg T z) (by exact_mod_cast Nat.zero_le width)
  have hsq' :
      l2SqOn B z ≤ l1On carrier z * (l1On T z / (width : ℝ)) := by
    exact hsq.trans (mul_le_mul_of_nonneg_right hB_l1_le havg_nonneg)
  have hsqrt := Real.sqrt_le_sqrt hsq'
  calc
    AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo B z) =
        Real.sqrt (l2SqOn B z) := by
        rw [AppliedModelingLib.FiniteDimensionalNorms.l2,
          l2Sq_restrictTo_eq_l2SqOn]
    _ ≤ Real.sqrt (l1On carrier z * (l1On T z / (width : ℝ))) := hsqrt

theorem sum_l2_restrictTo_absRankBlock_le_sqrt_l1On_mul_top_div_width_add_l1On_div_sqrt_width
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    {parent carrier : Finset Feature} {z : Feature → ℝ} {width : ℕ}
    (hwidth : 0 < width)
    (htop_card : (absRankBlockFinset parent z width 0).card = width)
    (hcarrier : carrier ⊆ parent \ absRankBlockFinset parent z width 0) :
    (∑ block ∈ Finset.range carrier.card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width block) z)) ≤
      Real.sqrt
        (l1On carrier z *
          (l1On (absRankBlockFinset parent z width 0) z / (width : ℝ))) +
        l1On carrier z / Real.sqrt (width : ℝ) := by
  classical
  have hsum :=
    sum_l2_restrictTo_absRankBlock_le_top_l2_add_l1On_div_sqrt_width
      (carrier := carrier) (z := z) (width := width) hwidth
  have htop :=
    l2_restrictTo_absRankBlock_zero_le_sqrt_l1On_mul_top_div_width
      (parent := parent) (carrier := carrier) (z := z) (width := width)
      hwidth htop_card hcarrier
  exact hsum.trans
    (by
      have h := add_le_add_right htop
        (l1On carrier z / Real.sqrt (width : ℝ))
      simpa [add_comm, add_left_comm, add_assoc] using h)

theorem support_sdiff_union_absRankBlock_subset_tail_sdiff_top
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) (width : ℕ) :
    support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0) ⊆
      (support z \ S) \ absRankBlockFinset (support z \ S) z width 0 := by
  intro i hi
  rcases Finset.mem_sdiff.mp hi with ⟨hisupp, hi_not_union⟩
  have hi_notS : i ∉ S := by
    intro hiS
    exact hi_not_union (Finset.mem_union.mpr (Or.inl hiS))
  have hi_not_top :
      i ∉ absRankBlockFinset (support z \ S) z width 0 := by
    intro hitop
    exact hi_not_union (Finset.mem_union.mpr (Or.inr hitop))
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hisupp, hi_notS⟩, hi_not_top⟩

theorem sum_l2_restrictTo_support_sdiff_union_absRankBlock_zero_le
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) {width : ℕ}
    (hwidth : 0 < width)
    (htop_card :
      (absRankBlockFinset (support z \ S) z width 0).card = width) :
    (∑ block ∈
        Finset.range
          (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0)).card,
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo
            (absRankBlockFinset
              (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0))
              z width block) z)) ≤
      Real.sqrt
        (l1On
          (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0)) z *
          (l1On (absRankBlockFinset (support z \ S) z width 0) z /
            (width : ℝ))) +
        l1On
          (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0)) z /
          Real.sqrt (width : ℝ) := by
  exact
    sum_l2_restrictTo_absRankBlock_le_sqrt_l1On_mul_top_div_width_add_l1On_div_sqrt_width
      (parent := support z \ S)
      (carrier :=
        support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0))
      (z := z) (width := width) hwidth htop_card
      (support_sdiff_union_absRankBlock_subset_tail_sdiff_top S z width)

theorem l1_eq_l1On_add_l1On_compl
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l1 z =
      l1On S z + l1On Sᶜ z := by
  classical
  rw [AppliedModelingLib.FiniteDimensionalNorms.l1, l1On, l1On]
  have hsplit :
      (∑ i : Feature, |z i|) =
        (∑ i ∈ S, |z i|) +
          ∑ i ∈ (Finset.univ.filter fun i : Feature => i ∉ S), |z i| := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset Feature))
        (p := fun i : Feature => i ∈ S)
        (f := fun i : Feature => |z i|)).symm
  have hcompl :
      (Finset.univ.filter fun i : Feature => i ∉ S) = Sᶜ := by
    ext i
    simp
  rw [hsplit, hcompl]

theorem l1On_compl_support_eq_zero
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) :
    l1On (support z)ᶜ z = 0 := by
  classical
  rw [l1On]
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hi_not : i ∉ support z := by
    simpa using hi
  have hz : z i = 0 := (not_mem_support_iff.mp hi_not)
  simp [hz]

theorem l1_eq_l1On_support
    [Fintype Feature] [DecidableEq Feature] (z : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l1 z = l1On (support z) z := by
  rw [l1_eq_l1On_add_l1On_compl (S := support z) z,
    l1On_compl_support_eq_zero]
  ring

theorem l1On_compl_eq_l1On_support_sdiff
    [Fintype Feature] [DecidableEq Feature]
    (S : Finset Feature) (z : Feature → ℝ) :
    l1On Sᶜ z = l1On (support z \ S) z := by
  classical
  rw [l1On, l1On]
  have hsubset : support z \ S ⊆ Sᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
  have hsum :
      (∑ i ∈ support z \ S, |z i|) =
        ∑ i ∈ Sᶜ, |z i| := by
    refine Finset.sum_subset hsubset ?_
    intro i hiSc hiTail
    have hi_notS : i ∉ S := by
      simpa using hiSc
    have hi_not_support : i ∉ support z := by
      intro hisupp
      exact hiTail (Finset.mem_sdiff.mpr ⟨hisupp, hi_notS⟩)
    have hz : z i = 0 := not_mem_support_iff.mp hi_not_support
    simp [hz]
  exact hsum.symm

theorem l1_eq_l1On_of_support_subset
    [Fintype Feature] [DecidableEq Feature]
    {S : Finset Feature} {z : Feature → ℝ}
    (hsubset : support z ⊆ S) :
    AppliedModelingLib.FiniteDimensionalNorms.l1 z = l1On S z := by
  classical
  rw [l1_eq_l1On_add_l1On_compl (S := S) z]
  have hcompl_zero : l1On Sᶜ z = 0 := by
    rw [l1On]
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_not : i ∉ S := by
      simpa using hi
    have hi_not_support : i ∉ support z := by
      intro hisupp
      exact hi_not (hsubset hisupp)
    have hz : z i = 0 := not_mem_support_iff.mp hi_not_support
    simp [hz]
  rw [hcompl_zero]
  ring

theorem l1On_sub_le_l1On_add_l1On_sub
    [DecidableEq Feature] (S : Finset Feature)
    (z z' : Feature → ℝ) :
    l1On S z ≤ l1On S z' + l1On S (fun i => z' i - z i) := by
  classical
  rw [l1On, l1On, l1On]
  calc
    (∑ i ∈ S, |z i|) ≤
        ∑ i ∈ S, (|z' i| + |z' i - z i|) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          calc
            |z i| = |z' i + -(z' i - z i)| := by
              congr
              ring
            _ ≤ |z' i| + |-(z' i - z i)| :=
              abs_add_le (z' i) (-(z' i - z i))
            _ = |z' i| + |z' i - z i| := by
              rw [abs_neg]
    _ = (∑ i ∈ S, |z' i|) + ∑ i ∈ S, |z' i - z i| := by
          simp [Finset.sum_add_distrib]

theorem l1On_compl_support_sub_eq
    [Fintype Feature] [DecidableEq Feature]
    (z z' : Feature → ℝ) :
    l1On (support z)ᶜ (fun i => z' i - z i) =
      l1On (support z)ᶜ z' := by
  classical
  rw [l1On, l1On]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi_not : i ∉ support z := by
    simpa using hi
  have hz : z i = 0 := (not_mem_support_iff.mp hi_not)
  simp [hz]

theorem measurement_sub_eq_zero_of_measurement_eq
    [Fintype Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z z' : Feature → ℝ}
    (hmeas : measurement A z' = measurement A z) :
    measurement A (fun i => z' i - z i) = (fun _ => 0) := by
  classical
  funext r
  have hr := congrFun hmeas r
  dsimp [measurement] at hr ⊢
  calc
    (∑ i : Feature, (z' i - z i) * A i r) =
        (∑ i : Feature, z' i * A i r) -
          ∑ i : Feature, z i * A i r := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = 0 := sub_eq_zero.mpr hr

theorem measurement_add
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x y : Feature → ℝ) :
    measurement A (fun i => x i + y i) =
      fun r => measurement A x r + measurement A y r := by
  classical
  funext r
  dsimp [measurement]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem measurement_sub
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x y : Feature → ℝ) :
    measurement A (fun i => x i - y i) =
      fun r => measurement A x r - measurement A y r := by
  classical
  funext r
  dsimp [measurement]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem measurement_neg
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x : Feature → ℝ) :
    measurement A (fun i => -x i) = fun r => -measurement A x r := by
  classical
  funext r
  dsimp [measurement]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem measurement_smul
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (a : ℝ) (x : Feature → ℝ) :
    measurement A (fun i => a * x i) = fun r => a * measurement A x r := by
  classical
  funext r
  dsimp [measurement]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  ring

theorem measurement_restrictTo_add_compl
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (S : Finset Feature) (z : Feature → ℝ) :
    (fun r => measurement A (restrictTo S z) r +
      measurement A (restrictTo Sᶜ z) r) = measurement A z := by
  have hvec := restrictTo_add_compl S z
  have hmeas := congrArg (measurement A) hvec
  simpa [measurement_add] using hmeas

theorem measurement_restrictTo_eq_neg_restrictTo_compl_of_measurement_eq_zero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ}
    (S : Finset Feature) (hker : measurement A z = fun _ => 0) :
    measurement A (restrictTo S z) =
      fun r => -measurement A (restrictTo Sᶜ z) r := by
  funext r
  have hsplit := congrFun (measurement_restrictTo_add_compl A S z) r
  have hzero := congrFun hker r
  linarith

theorem measurement_restrictTo_eq_neg_restrictTo_support_sdiff_of_measurement_eq_zero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ}
    (S : Finset Feature) (hker : measurement A z = fun _ => 0) :
    measurement A (restrictTo S z) =
      fun r => -measurement A (restrictTo (support z \ S) z) r := by
  rw [← restrictTo_compl_eq_restrictTo_support_sdiff (S := S) (z := z)]
  exact measurement_restrictTo_eq_neg_restrictTo_compl_of_measurement_eq_zero
    (A := A) (z := z) S hker

theorem l2Sq_measurement_restrictTo_le_abs_inner_tail_of_measurement_eq_zero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ}
    (S : Finset Feature) (hker : measurement A z = fun _ => 0) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A (restrictTo S z)) ≤
      |inner (measurement A (restrictTo S z))
        (measurement A (restrictTo (support z \ S) z))| := by
  classical
  let head := measurement A (restrictTo S z)
  let tail := measurement A (restrictTo (support z \ S) z)
  have hhead_tail : head = fun r => -tail r := by
    simpa [head, tail] using
      measurement_restrictTo_eq_neg_restrictTo_support_sdiff_of_measurement_eq_zero
        (A := A) (z := z) S hker
  have hinner :
      inner head head = -inner head tail := by
    calc
      inner head head = inner head (fun r => -tail r) := by
        rw [hhead_tail]
      _ = -inner head tail := inner_neg_right head tail
  have hl2 : AppliedModelingLib.FiniteDimensionalNorms.l2Sq head = -inner head tail := by
    rw [← inner_self_eq_l2Sq head]
    exact hinner
  calc
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A (restrictTo S z)) =
        -inner head tail := by simpa [head] using hl2
    _ ≤ |inner head tail| := neg_le_abs _
    _ = |inner (measurement A (restrictTo S z))
        (measurement A (restrictTo (support z \ S) z))| := by
          simp [head, tail]

theorem one_sub_delta_mul_l2Sq_restrictTo_le_abs_inner_tail_of_kernel_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ}
    {S : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hS : S.card ≤ s) (hker : measurement A z = fun _ => 0) :
    (1 - δ) *
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo S z) ≤
      |inner (measurement A (restrictTo S z))
        (measurement A (restrictTo (support z \ S) z))| := by
  have hsparse : KSparse s (restrictTo S z) :=
    kSparse_restrictTo_of_card_le hS
  exact (hrip (restrictTo S z) hsparse).1.trans
    (l2Sq_measurement_restrictTo_le_abs_inner_tail_of_measurement_eq_zero
      (A := A) (z := z) S hker)

theorem l2Sq_measurement_add_eq
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x y : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement A (fun i => x i + y i)) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A y) +
          2 * inner (measurement A x) (measurement A y) := by
  rw [measurement_add]
  exact l2Sq_add_eq (measurement A x) (measurement A y)

theorem l2Sq_measurement_sub_eq
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x y : Feature → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
        (measurement A (fun i => x i - y i)) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) +
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A y) -
          2 * inner (measurement A x) (measurement A y) := by
  rw [measurement_sub]
  exact l2Sq_sub_eq (measurement A x) (measurement A y)

theorem four_mul_inner_measurement_eq_l2Sq_measurement_add_sub_l2Sq_measurement_sub
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (x y : Feature → ℝ) :
    4 * inner (measurement A x) (measurement A y) =
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement A (fun i => x i + y i)) -
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (measurement A (fun i => x i - y i)) := by
  rw [l2Sq_measurement_add_eq, l2Sq_measurement_sub_eq]
  ring

theorem linearProbe_self_eq_inner_measurement
    [Fintype Feature] [Fintype Coord]
    (A : Feature → Coord → ℝ) (z : Feature → ℝ) (i : Feature) :
    linearProbe A A z i = inner (A i) (measurement A z) := by
  classical
  unfold linearProbe inner measurement
  calc
    (∑ j : Feature, z j * ∑ r : Coord, A i r * A j r) =
        ∑ j : Feature, ∑ r : Coord, z j * (A i r * A j r) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          rw [Finset.mul_sum]
    _ = ∑ r : Coord, ∑ j : Feature, z j * (A i r * A j r) := by
          rw [Finset.sum_comm]
    _ = ∑ r : Coord, A i r * ∑ j : Feature, z j * A j r := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro j _hj
          ring

theorem eq_of_sub_eq_zero_fun {z z' : Feature → ℝ}
    (h : (fun i => z' i - z i) = (fun _ => 0)) :
    z' = z := by
  funext i
  have hi := congrFun h i
  change z' i - z i = 0 at hi
  linarith

theorem eq_zero_of_l2Sq_eq_zero
    [Fintype Feature] {x : Feature → ℝ}
    (h : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 0) :
    x = fun _ => 0 := by
  by_contra hne
  have hexists : ∃ i, x i ≠ 0 := by
    by_contra hnone
    apply hne
    funext i
    by_contra hxi
    exact hnone ⟨i, hxi⟩
  have hpos := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_pos_of_exists_ne_zero
    (x := x) hexists
  linarith

/--
RIP with constant strictly below one rules out nonzero sparse kernel vectors.
This is the sparse-kernel version of the deterministic injectivity layer.
-/
theorem sparseKernelFree_of_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ}
    (hδ : δ < 1) (hrip : RestrictedIsometryProperty A s δ) :
    SparseKernelFree A s := by
  intro x hx hker
  have hlower := (hrip x hx).1
  have hmeas_l2 :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A x) = 0 := by
    rw [hker]
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_zero
  have hcoef_pos : 0 < 1 - δ := by linarith
  have hx_nonneg : 0 ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq x :=
    AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x
  have hlower_zero :
      (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq x ≤ 0 := by
    simpa [hmeas_l2] using hlower
  have hx_l2_zero : AppliedModelingLib.FiniteDimensionalNorms.l2Sq x = 0 := by
    nlinarith
  exact eq_zero_of_l2Sq_eq_zero hx_l2_zero

theorem eq_zero_of_kernel_of_tail_card_le_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {δ : ℝ}
    {z : Feature → ℝ} {S : Finset Feature}
    (hδ : δ < 1) (hrip : RestrictedIsometryProperty A (2 * k) δ)
    (hS : S.card ≤ k) (htail : (support z \ S).card ≤ k)
    (hker : measurement A z = fun _ => 0) :
    z = fun _ => 0 := by
  have hsparse : KSparse (2 * k) z :=
    kSparse_of_card_le_and_tail_card_le (S := S) hS htail
  exact
    sparseKernelFree_of_restrictedIsometry
      (A := A) (s := 2 * k) hδ hrip z hsparse hker

/--
RIP with constant strictly below one gives uniqueness among sparse vectors.
This is the deterministic injectivity layer behind compressed-sensing recovery;
the stronger basis-pursuit theorem still needs the usual nullspace-property
or RIP tail-decomposition argument.
-/
theorem eq_of_measurement_eq_of_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {δ : ℝ}
    (hδ : δ < 1) (hrip : RestrictedIsometryProperty A (2 * k) δ)
    {x y : Feature → ℝ}
    (hx : KSparse k x) (hy : KSparse k y)
    (hmeas : measurement A x = measurement A y) :
    x = y := by
  classical
  let h : Feature → ℝ := fun i => x i - y i
  have hsparse : KSparse (2 * k) h := by
    simpa [h] using kSparse_sub_of_kSparse hx hy
  have hmeas_zero : measurement A h = (fun _ => 0) := by
    simpa [h] using
      measurement_sub_eq_zero_of_measurement_eq
        (A := A) (z := y) (z' := x) hmeas
  have hlower := (hrip h hsparse).1
  have hmeas_l2 :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (measurement A h) = 0 := by
    rw [hmeas_zero]
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_zero
  have hcoef_pos : 0 < 1 - δ := by linarith
  have hh_nonneg : 0 ≤ AppliedModelingLib.FiniteDimensionalNorms.l2Sq h :=
    AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg h
  have hlower_zero :
      (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq h ≤ 0 := by
    simpa [hmeas_l2] using hlower
  have hh_l2_zero : AppliedModelingLib.FiniteDimensionalNorms.l2Sq h = 0 := by
    nlinarith
  have hzero : h = fun _ => 0 :=
    eq_zero_of_l2Sq_eq_zero hh_l2_zero
  funext i
  have hi := congrFun hzero i
  change x i - y i = 0 at hi
  linarith

/--
First restricted-orthogonality consequence of RIP.  If two vectors have
disjoint supports whose union is within the RIP order, then the measurement
cross-inner-product is controlled by the RIP error times their combined
squared mass.  The sharper `δ * ||x||₂ * ||y||₂` form used in full
compressed-sensing proofs follows by the usual scaling/optimization argument;
this finite polarization form is the reusable algebraic core.
-/
theorem abs_inner_measurement_le_delta_half_mul_l2Sq_add_l2Sq_of_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ} {x y : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hdisj : Disjoint (support x) (support y))
    (hcard : (support x ∪ support y).card ≤ s) :
    |inner (measurement A x) (measurement A y)| ≤
      (δ / 2) *
        (AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq y) := by
  classical
  let mass :=
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq x +
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq y
  let addMeas :=
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement A (fun i => x i + y i))
  let subMeas :=
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (measurement A (fun i => x i - y i))
  let cross := inner (measurement A x) (measurement A y)
  have hsparse_add : KSparse s (fun i => x i + y i) :=
    kSparse_add_of_support_union_card_le hcard
  have hsparse_sub : KSparse s (fun i => x i - y i) :=
    kSparse_sub_of_support_union_card_le hcard
  have hnorm_add :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun i => x i + y i) = mass := by
    dsimp [mass]
    exact l2Sq_add_eq_of_disjoint_support hdisj
  have hnorm_sub :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (fun i => x i - y i) = mass := by
    dsimp [mass]
    exact l2Sq_sub_eq_of_disjoint_support hdisj
  have hadd_lower : (1 - δ) * mass ≤ addMeas := by
    simpa [addMeas, hnorm_add] using (hrip (fun i => x i + y i) hsparse_add).1
  have hadd_upper : addMeas ≤ (1 + δ) * mass := by
    simpa [addMeas, hnorm_add] using (hrip (fun i => x i + y i) hsparse_add).2
  have hsub_lower : (1 - δ) * mass ≤ subMeas := by
    simpa [subMeas, hnorm_sub] using (hrip (fun i => x i - y i) hsparse_sub).1
  have hsub_upper : subMeas ≤ (1 + δ) * mass := by
    simpa [subMeas, hnorm_sub] using (hrip (fun i => x i - y i) hsparse_sub).2
  have hpolar : 4 * cross = addMeas - subMeas := by
    simpa [cross, addMeas, subMeas] using
      four_mul_inner_measurement_eq_l2Sq_measurement_add_sub_l2Sq_measurement_sub
        (A := A) x y
  have hcross_upper : cross ≤ (δ / 2) * mass := by
    have h4 : 4 * cross ≤ 2 * δ * mass := by
      rw [hpolar]
      nlinarith
    nlinarith
  have hcross_lower : -((δ / 2) * mass) ≤ cross := by
    have h4 : -(2 * δ * mass) ≤ 4 * cross := by
      rw [hpolar]
      nlinarith
    nlinarith
  simpa [mass, cross] using abs_le.mpr ⟨hcross_lower, hcross_upper⟩

/--
Scaled restricted-orthogonality consequence of RIP.  This is the standard
finite-dimensional form used by compressed-sensing nullspace proofs: disjoint
vectors whose union support is within the RIP order have measurement
cross-inner-product at most `δ ||x||₂ ||y||₂`.
-/
theorem abs_inner_measurement_le_delta_mul_l2_mul_l2_of_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ} {x y : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hdisj : Disjoint (support x) (support y))
    (hcard : (support x ∪ support y).card ≤ s) :
    |inner (measurement A x) (measurement A y)| ≤
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 x *
        AppliedModelingLib.FiniteDimensionalNorms.l2 y := by
  classical
  let nx := AppliedModelingLib.FiniteDimensionalNorms.l2Sq x
  let ny := AppliedModelingLib.FiniteDimensionalNorms.l2Sq y
  let cross := inner (measurement A x) (measurement A y)
  by_cases hnx_zero : nx = 0
  · have hx_zero : x = fun _ => 0 := by
      exact eq_zero_of_l2Sq_eq_zero (x := x) (by simpa [nx] using hnx_zero)
    have hmeas_x : measurement A x = fun _ => 0 := by
      rw [hx_zero]
      funext r
      simp [measurement]
    have hcross : cross = 0 := by
      simp [cross, hmeas_x, inner]
    simpa [cross, hcross, AppliedModelingLib.FiniteDimensionalNorms.l2, nx, hnx_zero]
  by_cases hny_zero : ny = 0
  · have hy_zero : y = fun _ => 0 := by
      exact eq_zero_of_l2Sq_eq_zero (x := y) (by simpa [ny] using hny_zero)
    have hmeas_y : measurement A y = fun _ => 0 := by
      rw [hy_zero]
      funext r
      simp [measurement]
    have hcross : cross = 0 := by
      simp [cross, hmeas_y, inner]
    simpa [cross, hcross, AppliedModelingLib.FiniteDimensionalNorms.l2, ny, hny_zero]
  have hnx_nonneg : 0 ≤ nx := by
    dsimp [nx]
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x
  have hny_nonneg : 0 ≤ ny := by
    dsimp [ny]
    exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg y
  have hnx_pos : 0 < nx := lt_of_le_of_ne hnx_nonneg (Ne.symm hnx_zero)
  have hny_pos : 0 < ny := lt_of_le_of_ne hny_nonneg (Ne.symm hny_zero)
  let ax := Real.sqrt ny
  let ay := Real.sqrt nx
  have hax_pos : 0 < ax := by
    dsimp [ax]
    exact Real.sqrt_pos_of_pos hny_pos
  have hay_pos : 0 < ay := by
    dsimp [ay]
    exact Real.sqrt_pos_of_pos hnx_pos
  have hax_sq : ax ^ 2 = ny := by
    dsimp [ax]
    exact Real.sq_sqrt hny_nonneg
  have hay_sq : ay ^ 2 = nx := by
    dsimp [ay]
    exact Real.sq_sqrt hnx_nonneg
  have hcard_scaled :
      (support (fun i => ax * x i) ∪ support (fun i => ay * y i)).card ≤ s := by
    have hsubset :
        support (fun i => ax * x i) ∪ support (fun i => ay * y i) ⊆
          support x ∪ support y :=
      Finset.union_subset_union (support_smul_subset ax x) (support_smul_subset ay y)
    exact (Finset.card_le_card hsubset).trans hcard
  have hscaled :=
    abs_inner_measurement_le_delta_half_mul_l2Sq_add_l2Sq_of_restrictedIsometry
      (A := A) (s := s) (δ := δ)
      (x := fun i => ax * x i) (y := fun i => ay * y i)
      hrip (disjoint_support_smul_smul ax ay hdisj) hcard_scaled
  have hscaled' :
      |ax * ay * cross| ≤
        (δ / 2) * (ax ^ 2 * nx + ay ^ 2 * ny) := by
    simpa [cross, nx, ny, measurement_smul, inner_smul_smul, l2Sq_smul,
      mul_assoc, mul_left_comm] using hscaled
  have hscaled'' : (ax * ay) * |cross| ≤ δ * (nx * ny) := by
    rw [abs_mul, abs_of_pos (mul_pos hax_pos hay_pos)] at hscaled'
    calc
      (ax * ay) * |cross| ≤
          (δ / 2) * (ax ^ 2 * nx + ay ^ 2 * ny) := hscaled'
      _ = δ * (nx * ny) := by
          rw [hax_sq, hay_sq]
          ring
  have hp_pos : 0 < ax * ay := mul_pos hax_pos hay_pos
  have hp_sq : (ax * ay) ^ 2 = nx * ny := by
    nlinarith [hax_sq, hay_sq]
  have hmain : |cross| ≤ δ * (ax * ay) := by
    have hscaled_p :
        (ax * ay) * |cross| ≤ (ax * ay) * (δ * (ax * ay)) := by
      calc
        (ax * ay) * |cross| ≤ δ * (nx * ny) := hscaled''
        _ = (ax * ay) * (δ * (ax * ay)) := by
            rw [← hp_sq]
            ring
    exact le_of_mul_le_mul_left hscaled_p hp_pos
  simpa [cross, ax, ay, nx, ny, AppliedModelingLib.FiniteDimensionalNorms.l2,
    mul_assoc, mul_left_comm, mul_comm] using hmain

theorem abs_inner_measurement_restrictTo_le_delta_mul_l2_mul_l2_of_restrictedIsometry
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s : ℕ} {δ : ℝ}
    {S T : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hdisj : Disjoint S T) (hcard : S.card + T.card ≤ s) :
    |inner (measurement A (restrictTo S z)) (measurement A (restrictTo T z))| ≤
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
        AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo T z) := by
  classical
  have hsupport_disj :
      Disjoint (support (restrictTo S z)) (support (restrictTo T z)) :=
    disjoint_support_restrictTo_of_disjoint hdisj
  have hsupport_card :
      (support (restrictTo S z) ∪ support (restrictTo T z)).card ≤ s := by
    exact
      (support_union_restrictTo_card_le_add
        (S := S) (T := T) (z := z)
        (s := S.card) (t := T.card) le_rfl le_rfl).trans hcard
  exact
    abs_inner_measurement_le_delta_mul_l2_mul_l2_of_restrictedIsometry
      (A := A) (s := s) (δ := δ)
      (x := restrictTo S z) (y := restrictTo T z)
      hrip hsupport_disj hsupport_card

theorem abs_inner_measurement_restrictTo_carrier_le_delta_mul_l2_mul_sum_l2_blocks
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {S carrier : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hcarrier : carrier ⊆ Sᶜ) (horder : S.card + width ≤ s)
    (hwidth : 0 < width) :
    |inner (measurement A (restrictTo S z)) (measurement A (restrictTo carrier z))| ≤
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
        (∑ block ∈ Finset.range carrier.card,
          AppliedModelingLib.FiniteDimensionalNorms.l2
            (restrictTo (absRankBlockFinset carrier z width block) z)) := by
  classical
  have htail :=
    abs_inner_measurement_restrictTo_tail_le_sum_abs_inner_blocks
      (A := A) (S := S) (carrier := carrier) (z := z)
      (width := width) hwidth
  calc
    |inner (measurement A (restrictTo S z)) (measurement A (restrictTo carrier z))|
        ≤ ∑ block ∈ Finset.range carrier.card,
            |inner (measurement A (restrictTo S z))
              (measurement A
                (restrictTo (absRankBlockFinset carrier z width block) z))| := htail
    _ ≤ ∑ block ∈ Finset.range carrier.card,
          δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
            AppliedModelingLib.FiniteDimensionalNorms.l2
              (restrictTo (absRankBlockFinset carrier z width block) z) := by
          refine Finset.sum_le_sum ?_
          intro block _hblock
          have hdisj : Disjoint S (absRankBlockFinset carrier z width block) :=
            disjoint_absRankBlockFinset_of_subset_compl
              (carrier := carrier) (z := z) (width := width)
              (block := block) hcarrier
          have hblock_card :
              (absRankBlockFinset carrier z width block).card ≤ width :=
            absRankBlockFinset_card_le_width carrier z width block
          have hcard : S.card + (absRankBlockFinset carrier z width block).card ≤ s := by
            omega
          exact
            abs_inner_measurement_restrictTo_le_delta_mul_l2_mul_l2_of_restrictedIsometry
              (A := A) (s := s) (δ := δ) (S := S)
              (T := absRankBlockFinset carrier z width block) (z := z)
              hrip hdisj hcard
    _ = δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
        (∑ block ∈ Finset.range carrier.card,
          AppliedModelingLib.FiniteDimensionalNorms.l2
            (restrictTo (absRankBlockFinset carrier z width block) z)) := by
          rw [← Finset.mul_sum]

theorem one_sub_delta_mul_l2Sq_restrictTo_le_delta_mul_l2_mul_sum_l2_tail_blocks
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {S : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hS : S.card ≤ s) (horder : S.card + width ≤ s)
    (hwidth : 0 < width) (hker : measurement A z = fun _ => 0) :
    (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo S z) ≤
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
        (∑ block ∈ Finset.range (support z \ S).card,
          AppliedModelingLib.FiniteDimensionalNorms.l2
            (restrictTo (absRankBlockFinset (support z \ S) z width block) z)) := by
  classical
  have hlower :=
    one_sub_delta_mul_l2Sq_restrictTo_le_abs_inner_tail_of_kernel_restrictedIsometry
      (A := A) (s := s) (δ := δ) (S := S) (z := z)
      hrip hS hker
  have hcarrier : support z \ S ⊆ Sᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hi).2
  have hinner :=
    abs_inner_measurement_restrictTo_carrier_le_delta_mul_l2_mul_sum_l2_blocks
      (A := A) (s := s) (width := width) (δ := δ)
      (S := S) (carrier := support z \ S) (z := z)
      hrip hcarrier horder hwidth
  exact hlower.trans hinner

theorem one_sub_delta_mul_l2Sq_restrictTo_le_delta_mul_l2_mul_top_l2_add_tail_l1_div_sqrt
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {S : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hδ_nonneg : 0 ≤ δ)
    (hS : S.card ≤ s) (horder : S.card + width ≤ s)
    (hwidth : 0 < width) (hker : measurement A z = fun _ => 0) :
    (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo S z) ≤
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) *
        (AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset (support z \ S) z width 0) z) +
          l1On (support z \ S) z / Real.sqrt (width : ℝ)) := by
  classical
  let tail := support z \ S
  let blockSum :=
    ∑ block ∈ Finset.range tail.card,
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset tail z width block) z)
  let topTail :=
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (restrictTo (absRankBlockFinset tail z width 0) z) +
      l1On tail z / Real.sqrt (width : ℝ)
  have hbase :
      (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo S z) ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) * blockSum := by
    simpa [tail, blockSum] using
      one_sub_delta_mul_l2Sq_restrictTo_le_delta_mul_l2_mul_sum_l2_tail_blocks
        (A := A) (s := s) (width := width) (δ := δ)
        (S := S) (z := z) hrip hS horder hwidth hker
  have hsum : blockSum ≤ topTail := by
    simpa [tail, blockSum, topTail] using
      sum_l2_restrictTo_absRankBlock_le_top_l2_add_l1On_div_sqrt_width
        (carrier := tail) (z := z) (width := width) hwidth
  have hcoef_nonneg :
      0 ≤ δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) := by
    exact mul_nonneg hδ_nonneg
      (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _)
  have hmul :
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) * blockSum ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo S z) * topTail := by
    exact mul_le_mul_of_nonneg_left hsum hcoef_nonneg
  exact hbase.trans (by simpa [tail, blockSum, topTail, mul_assoc] using hmul)

theorem one_sub_delta_mul_l2Sq_restrictTo_union_absRankBlock_zero_le
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {S : Finset Feature} {z : Feature → ℝ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hδ_nonneg : 0 ≤ δ)
    (hU :
      (S ∪ absRankBlockFinset (support z \ S) z width 0).card ≤ s)
    (horder :
      (S ∪ absRankBlockFinset (support z \ S) z width 0).card + width ≤ s)
    (hwidth : 0 < width)
    (htop_card :
      (absRankBlockFinset (support z \ S) z width 0).card = width)
    (hker : measurement A z = fun _ => 0) :
    (1 - δ) *
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (restrictTo
            (S ∪ absRankBlockFinset (support z \ S) z width 0) z) ≤
      δ *
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo
            (S ∪ absRankBlockFinset (support z \ S) z width 0) z) *
        (Real.sqrt
          (l1On
            (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0)) z *
            (l1On (absRankBlockFinset (support z \ S) z width 0) z /
              (width : ℝ))) +
          l1On
            (support z \ (S ∪ absRankBlockFinset (support z \ S) z width 0)) z /
            Real.sqrt (width : ℝ)) := by
  classical
  let U := S ∪ absRankBlockFinset (support z \ S) z width 0
  let R := support z \ U
  let blockSum :=
    ∑ block ∈ Finset.range R.card,
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (restrictTo (absRankBlockFinset R z width block) z)
  let rhs :=
    Real.sqrt
      (l1On R z *
        (l1On (absRankBlockFinset (support z \ S) z width 0) z /
          (width : ℝ))) +
      l1On R z / Real.sqrt (width : ℝ)
  have hbase :
      (1 - δ) *
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo U z) ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo U z) * blockSum := by
    simpa [U, R, blockSum] using
      one_sub_delta_mul_l2Sq_restrictTo_le_delta_mul_l2_mul_sum_l2_tail_blocks
        (A := A) (s := s) (width := width) (δ := δ)
        (S := U) (z := z) hrip (by simpa [U] using hU)
        (by simpa [U] using horder) hwidth hker
  have hsum : blockSum ≤ rhs := by
    simpa [U, R, blockSum, rhs] using
      sum_l2_restrictTo_support_sdiff_union_absRankBlock_zero_le
        (S := S) (z := z) hwidth htop_card
  have hcoef_nonneg :
      0 ≤ δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo U z) := by
    exact mul_nonneg hδ_nonneg
      (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _)
  have hmul :
      δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo U z) * blockSum ≤
        δ * AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo U z) * rhs := by
    exact mul_le_mul_of_nonneg_left hsum hcoef_nonneg
  exact hbase.trans
    (by simpa [U, R, blockSum, rhs, mul_assoc] using hmul)

theorem nullspaceProperty_of_restrictedIsometry_three_mul
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {δ : ℝ}
    (hk : 0 < k) (hδ_nonneg : 0 ≤ δ) (hδ : δ < 2 / 5)
    (hrip : RestrictedIsometryProperty A (3 * k) δ) :
    NullspaceProperty A k := by
  classical
  intro h hker hne S hS
  let tail := support h \ S
  have htail_compl : l1On Sᶜ h = l1On tail h := by
    simpa [tail] using l1On_compl_eq_l1On_support_sdiff S h
  have hδ_lt_one : δ < 1 := by linarith
  by_cases htail_small : tail.card ≤ k
  · have hrip_two : RestrictedIsometryProperty A (2 * k) δ :=
      restrictedIsometryProperty_mono (A := A) (δ := δ)
        (s₁ := 2 * k) (s₂ := 3 * k) (by omega) hrip
    have hzero :
        h = fun _ => 0 :=
      eq_zero_of_kernel_of_tail_card_le_restrictedIsometry
        (A := A) (k := k) (δ := δ) (z := h) (S := S)
        hδ_lt_one hrip_two hS (by simpa [tail] using htail_small) hker
    exact False.elim (hne hzero)
  · have htail_gt : k < tail.card := Nat.lt_of_not_ge htail_small
    let T0 := absRankBlockFinset tail h k 0
    let U := S ∪ T0
    let R := support h \ U
    let headNorm := AppliedModelingLib.FiniteDimensionalNorms.l2 (restrictTo U h)
    let a := l1On T0 h
    let b := l1On R h
    have htop_card : T0.card = k := by
      have hle : (0 + 1) * k ≤ tail.card := by
        simpa using (Nat.le_of_lt htail_gt)
      simpa [T0] using
        absRankBlockFinset_card_eq_width_of_le
          (carrier := tail) (z := h) (width := k) (block := 0) hle
    have hT0_subset_tail : T0 ⊆ tail := by
      simpa [T0] using absRankBlockFinset_subset tail h k 0
    have hU_card : U.card ≤ 2 * k := by
      have hcard_union : U.card ≤ S.card + T0.card := by
        simpa [U] using Finset.card_union_le S T0
      calc
        U.card ≤ S.card + T0.card := hcard_union
        _ ≤ k + k := Nat.add_le_add hS (by simpa [htop_card])
        _ = 2 * k := by omega
    have hU_card_three : U.card ≤ 3 * k := by
      exact hU_card.trans (by omega)
    have hU_order : U.card + k ≤ 3 * k := by
      omega
    have hkernel_bound :
        (1 - δ) * AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo U h) ≤
          δ * headNorm *
            (Real.sqrt (b * (a / (k : ℝ))) + b / Real.sqrt (k : ℝ)) := by
      simpa [tail, T0, U, R, headNorm, a, b] using
        one_sub_delta_mul_l2Sq_restrictTo_union_absRankBlock_zero_le
          (A := A) (s := 3 * k) (width := k) (δ := δ)
          (S := S) (z := h) hrip hδ_nonneg
          (by simpa [tail, T0, U] using hU_card_three)
          (by simpa [tail, T0, U] using hU_order)
          hk (by simpa [tail, T0] using htop_card) hker
    have hR_eq : R = tail \ T0 := by
      simp [R, U, tail, T0, sdiff_union_eq_sdiff_sdiff]
    have htail_split : l1On tail h = a + b := by
      have hsplit :=
        l1On_eq_l1On_add_l1On_sdiff
          (S := tail) (T := T0) (z := h) hT0_subset_tail
      simpa [a, b, hR_eq] using hsplit
    have htail_pos : 0 < l1On tail h := by
      have htail_card_pos : 0 < tail.card :=
        lt_of_le_of_lt (Nat.zero_le k) htail_gt
      rcases Finset.card_pos.mp htail_card_pos with ⟨i, hi_tail⟩
      exact l1On_pos_of_exists_mem_ne_zero
        ⟨i, hi_tail, mem_support.mp (Finset.mem_sdiff.mp hi_tail).1⟩
    have ha_nonneg : 0 ≤ a := by
      exact l1On_nonneg T0 h
    have hb_nonneg : 0 ≤ b := by
      exact l1On_nonneg R h
    have hab_pos : 0 < a + b := by
      simpa [htail_split] using htail_pos
    have hcoef_pos : 0 < 1 - δ := by linarith
    have hhead_sq :
        headNorm ^ 2 =
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq (restrictTo U h) := by
      dsimp [headNorm, AppliedModelingLib.FiniteDimensionalNorms.l2]
      exact
        Real.sq_sqrt
          (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg (restrictTo U h))
    by_cases hhead_zero : headNorm = 0
    · have hU_zero : restrictTo U h = fun _ => 0 := by
        apply eq_zero_of_l2Sq_eq_zero
        have hsquare :
            headNorm ^ 2 = 0 := by
          rw [hhead_zero]
          ring
        rw [← hhead_sq]
        exact hsquare
      have hS_subset_U : S ⊆ U := by
        intro i hi
        exact Finset.mem_union.mpr (Or.inl hi)
      have hS_zero : l1On S h = 0 := by
        have hzero_restrict : l1On S (restrictTo U h) = 0 := by
          rw [hU_zero]
          simp [l1On]
        simpa [l1On_restrictTo_eq_of_subset hS_subset_U] using hzero_restrict
      calc
        l1On S h = 0 := hS_zero
        _ < l1On Sᶜ h := by
          rw [htail_compl]
          exact htail_pos
    · have hhead_pos : 0 < headNorm := by
        exact lt_of_le_of_ne
          (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _)
          (Ne.symm hhead_zero)
      have hkernel_linear :
          (1 - δ) * headNorm ≤
            δ * (Real.sqrt (b * (a / (k : ℝ))) + b / Real.sqrt (k : ℝ)) := by
        have hnorm :
            (1 - δ) * headNorm ^ 2 ≤
              δ * headNorm *
                (Real.sqrt (b * (a / (k : ℝ))) + b / Real.sqrt (k : ℝ)) := by
          rw [hhead_sq]
          exact hkernel_bound
        have hmul :
            headNorm * ((1 - δ) * headNorm) ≤
              headNorm *
                (δ *
                  (Real.sqrt (b * (a / (k : ℝ))) +
                    b / Real.sqrt (k : ℝ))) := by
          nlinarith
        exact le_of_mul_le_mul_left hmul hhead_pos
      have hS_subset_U : S ⊆ U := by
        intro i hi
        exact Finset.mem_union.mpr (Or.inl hi)
      have hS_le_head :
          l1On S h ≤ Real.sqrt (k : ℝ) * headNorm := by
        have hbase :=
          l1On_le_sqrt_card_mul_l2_restrictTo_of_subset
            (S := S) (T := U) (z := h) hS_subset_U
        have hsqrt_card :
            Real.sqrt (S.card : ℝ) ≤ Real.sqrt (k : ℝ) := by
          exact Real.sqrt_le_sqrt (by exact_mod_cast hS)
        exact hbase.trans
          (mul_le_mul_of_nonneg_right hsqrt_card
            (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg _))
      have hsqrt_k_nonneg : 0 ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
      have hsqrt_k_bound :
          Real.sqrt (k : ℝ) *
              (Real.sqrt (b * (a / (k : ℝ))) + b / Real.sqrt (k : ℝ)) ≤
            Real.sqrt (a * b) + b := by
        exact sqrt_mul_ranked_residual_bound_le_sqrt_mul_add
          (w := (k : ℝ)) (a := a) (b := b)
          (by exact_mod_cast hk) ha_nonneg hb_nonneg
      have hscaled :
          (1 - δ) * l1On S h ≤ δ * (Real.sqrt (a * b) + b) := by
        have hleft :
            (1 - δ) * l1On S h ≤
              (1 - δ) * (Real.sqrt (k : ℝ) * headNorm) :=
          mul_le_mul_of_nonneg_left hS_le_head (le_of_lt hcoef_pos)
        have hmid :
            (1 - δ) * (Real.sqrt (k : ℝ) * headNorm) ≤
              δ *
                (Real.sqrt (k : ℝ) *
                  (Real.sqrt (b * (a / (k : ℝ))) +
                    b / Real.sqrt (k : ℝ))) := by
          have hmul :=
            mul_le_mul_of_nonneg_left hkernel_linear hsqrt_k_nonneg
          nlinarith
        have hright :
            δ *
                (Real.sqrt (k : ℝ) *
                  (Real.sqrt (b * (a / (k : ℝ))) +
                    b / Real.sqrt (k : ℝ))) ≤
              δ * (Real.sqrt (a * b) + b) :=
          mul_le_mul_of_nonneg_left hsqrt_k_bound hδ_nonneg
        exact hleft.trans (hmid.trans hright)
      have hstrict_rhs :
          δ * (Real.sqrt (a * b) + b) < (1 - δ) * (a + b) :=
        delta_mul_sqrt_add_lt_one_sub_delta_mul_sum
          hδ_nonneg hδ ha_nonneg hb_nonneg hab_pos
      have hscaled_strict :
          (1 - δ) * l1On S h < (1 - δ) * (a + b) :=
        lt_of_le_of_lt hscaled hstrict_rhs
      have hresult_tail : l1On S h < a + b := by
        by_contra hnot
        have hge : a + b ≤ l1On S h := le_of_not_gt hnot
        have hmul_ge :
            (1 - δ) * (a + b) ≤ (1 - δ) * l1On S h :=
          mul_le_mul_of_nonneg_left hge (le_of_lt hcoef_pos)
        exact not_lt_of_ge hmul_ge hscaled_strict
      rw [htail_compl, htail_split]
      exact hresult_tail

theorem abs_inner_measurement_absRankBlock_le_delta_mul_l2_mul_l2_of_restrictedIsometry
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {carrier : Finset Feature} {z : Feature → ℝ} {higher lower : ℕ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hblock : higher < lower) (horder : 2 * width ≤ s) :
    |inner
        (measurement A (restrictTo (absRankBlockFinset carrier z width higher) z))
        (measurement A (restrictTo (absRankBlockFinset carrier z width lower) z))| ≤
      δ *
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width higher) z) *
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absRankBlockFinset carrier z width lower) z) := by
  classical
  let H := absRankBlockFinset carrier z width higher
  let L := absRankBlockFinset carrier z width lower
  have hdisj_LH : Disjoint L H := by
    simpa [L, H] using
      disjoint_absRankBlockFinset_of_lt
        (carrier := carrier) (z := z) (width := width)
        (higher := higher) (lower := lower) hblock
  have hdisj_HL : Disjoint H L := hdisj_LH.symm
  have hH : H.card ≤ width := by
    simpa [H] using absRankBlockFinset_card_le_width carrier z width higher
  have hL : L.card ≤ width := by
    simpa [L] using absRankBlockFinset_card_le_width carrier z width lower
  have hcard : H.card + L.card ≤ s := by omega
  simpa [H, L] using
    abs_inner_measurement_restrictTo_le_delta_mul_l2_mul_l2_of_restrictedIsometry
      (A := A) (s := s) (δ := δ) (S := H) (T := L) (z := z)
      hrip hdisj_HL hcard

theorem abs_inner_measurement_absSupportRankBlock_le_delta_mul_l2_mul_l2_of_restrictedIsometry
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {s width : ℕ} {δ : ℝ}
    {z : Feature → ℝ} {higher lower : ℕ}
    (hrip : RestrictedIsometryProperty A s δ)
    (hblock : higher < lower) (horder : 2 * width ≤ s) :
    |inner
        (measurement A (restrictTo (absSupportRankBlockFinset z width higher) z))
        (measurement A (restrictTo (absSupportRankBlockFinset z width lower) z))| ≤
      δ *
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absSupportRankBlockFinset z width higher) z) *
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (restrictTo (absSupportRankBlockFinset z width lower) z) := by
  classical
  let H := absSupportRankBlockFinset z width higher
  let L := absSupportRankBlockFinset z width lower
  have hdisj_LH : Disjoint L H := by
    simpa [L, H] using
      disjoint_absSupportRankBlockFinset_of_lt
        (z := z) (width := width) (higher := higher) (lower := lower) hblock
  have hdisj_HL : Disjoint H L := hdisj_LH.symm
  have hH : H.card ≤ width := by
    simpa [H] using absSupportRankBlockFinset_card_le_width z width higher
  have hL : L.card ≤ width := by
    simpa [L] using absSupportRankBlockFinset_card_le_width z width lower
  have hcard : H.card + L.card ≤ s := by omega
  simpa [H, L] using
    abs_inner_measurement_restrictTo_le_delta_mul_l2_mul_l2_of_restrictedIsometry
      (A := A) (s := s) (δ := δ) (S := H) (T := L) (z := z)
      hrip hdisj_HL hcard

/--
The deterministic core of basis pursuit: the nullspace property implies exact
`l1` recovery.  The probabilistic/RIP step used in classical compressed sensing
can target `NullspaceProperty`; this theorem discharges the optimization
uniqueness step.
-/
theorem basisPursuitExactRecovery_of_nullspaceProperty
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ}
    (hnsp : NullspaceProperty A k) :
    BasisPursuitExactRecovery A k := by
  classical
  intro z hz_sparse z' hmeas hl1
  let h : Feature → ℝ := fun i => z' i - z i
  by_cases hzero : h = (fun _ => 0)
  · exact eq_of_sub_eq_zero_fun hzero
  · have hmeas_zero : measurement A h = (fun _ => 0) := by
      simpa [h] using
        measurement_sub_eq_zero_of_measurement_eq
          (A := A) (z := z) (z' := z') hmeas
    let S : Finset Feature := support z
    have hnsp_S : l1On S h < l1On Sᶜ h :=
      hnsp h hmeas_zero hzero S (by simpa [S] using hz_sparse)
    have htri :
        l1On S z ≤ l1On S z' + l1On S h := by
      simpa [h] using l1On_sub_le_l1On_add_l1On_sub (S := S) z z'
    have hout :
        l1On Sᶜ h = l1On Sᶜ z' := by
      simpa [S, h] using l1On_compl_support_sub_eq (z := z) (z' := z')
    have hsplit_z' :
        AppliedModelingLib.FiniteDimensionalNorms.l1 z' =
          l1On S z' + l1On Sᶜ z' :=
      l1_eq_l1On_add_l1On_compl (S := S) z'
    have hsplit_z :
        AppliedModelingLib.FiniteDimensionalNorms.l1 z = l1On S z := by
      simpa [S] using l1_eq_l1On_support z
    have hstrict : AppliedModelingLib.FiniteDimensionalNorms.l1 z <
        AppliedModelingLib.FiniteDimensionalNorms.l1 z' := by
      rw [hsplit_z, hsplit_z']
      nlinarith
    exact False.elim (not_lt_of_ge hl1 hstrict)

theorem basisPursuitExactRecovery_of_restrictedIsometry_three_mul
    [LinearOrder Feature] [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {δ : ℝ}
    (hk : 0 < k) (hδ_nonneg : 0 ≤ δ) (hδ : δ < 2 / 5)
    (hrip : RestrictedIsometryProperty A (3 * k) δ) :
    BasisPursuitExactRecovery A k :=
  basisPursuitExactRecovery_of_nullspaceProperty
    (nullspaceProperty_of_restrictedIsometry_three_mul
      (A := A) (k := k) (δ := δ) hk hδ_nonneg hδ hrip)

theorem abs_sum_univ_erase_inner_le_mu_l1
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {h : Feature → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ) (i : Feature) :
    |∑ j ∈ (Finset.univ : Finset Feature).erase i,
        h j * inner (A i) (A j)| ≤
      μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
  classical
  have hsum_abs :
      |∑ j ∈ (Finset.univ : Finset Feature).erase i,
          h j * inner (A i) (A j)| ≤
        ∑ j ∈ (Finset.univ : Finset Feature).erase i,
          |h j| * μ := by
    calc
      |∑ j ∈ (Finset.univ : Finset Feature).erase i,
          h j * inner (A i) (A j)| ≤
          ∑ j ∈ (Finset.univ : Finset Feature).erase i,
            |h j * inner (A i) (A j)| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ (Finset.univ : Finset Feature).erase i,
            |h j| * μ := by
            refine Finset.sum_le_sum ?_
            intro j hj
            have hji : j ≠ i := (Finset.mem_erase.mp hj).1
            have hinner_abs : |inner (A i) (A j)| ≤ μ :=
              hA.offdiag_abs_le (by exact hji.symm)
            calc
              |h j * inner (A i) (A j)| =
                  |h j| * |inner (A i) (A j)| := by rw [abs_mul]
              _ ≤ |h j| * μ :=
                  mul_le_mul_of_nonneg_left hinner_abs (abs_nonneg (h j))
  have herase_sum_le_univ :
      (∑ j ∈ (Finset.univ : Finset Feature).erase i, |h j|) ≤
        ∑ j : Feature, |h j| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (by intro j hj; exact Finset.mem_univ j)
      (by intro j _hj_univ hj_not; exact abs_nonneg (h j))
  calc
    |∑ j ∈ (Finset.univ : Finset Feature).erase i,
        h j * inner (A i) (A j)| ≤
        ∑ j ∈ (Finset.univ : Finset Feature).erase i, |h j| * μ := hsum_abs
    _ = μ * (∑ j ∈ (Finset.univ : Finset Feature).erase i, |h j|) := by
          rw [← Finset.sum_mul]
          ring
    _ ≤ μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
          rw [AppliedModelingLib.FiniteDimensionalNorms.l1]
          exact mul_le_mul_of_nonneg_left herase_sum_le_univ hμ

theorem abs_coord_le_mu_mul_l1_of_measurement_eq_zero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {h : Feature → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ)
    (hker : measurement A h = (fun _ => 0)) (i : Feature) :
    |h i| ≤ μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
  classical
  have hprobe_zero : linearProbe A A h i = 0 := by
    rw [linearProbe_self_eq_inner_measurement, hker]
    simp [inner]
  have hsum_eq :
      (∑ j ∈ (Finset.univ : Finset Feature).erase i,
        h j * inner (A i) (A j)) = -h i := by
    have hprobe_sum :
        (∑ j : Feature, h j * inner (A i) (A j)) = 0 := by
      simpa [linearProbe] using hprobe_zero
    rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
      (s := (Finset.univ : Finset Feature)) (i := i) (by simp)] at hprobe_sum
    have htail :
        (∑ x ∈ (Finset.univ : Finset Feature) \ {i},
          h x * inner (A i) (A x)) =
          ∑ x ∈ (Finset.univ : Finset Feature).erase i,
            h x * inner (A i) (A x) := by
      refine Finset.sum_congr ?_ ?_
      · ext x
        simp
      · intro x _hx
        rfl
    rw [htail, hA.self_inner i] at hprobe_sum
    linarith
  calc
    |h i| = |∑ j ∈ (Finset.univ : Finset Feature).erase i,
        h j * inner (A i) (A j)| := by
        rw [hsum_eq, abs_neg]
    _ ≤ μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h :=
        abs_sum_univ_erase_inner_le_mu_l1 (A := A) (h := h) hμ hA i

theorem l1On_le_card_mul_mu_mul_l1_of_measurement_eq_zero
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {h : Feature → ℝ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ)
    (hker : measurement A h = (fun _ => 0)) (S : Finset Feature) :
    l1On S h ≤ (S.card : ℝ) * μ *
      AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
  classical
  rw [l1On]
  calc
    (∑ i ∈ S, |h i|) ≤
        ∑ _i ∈ S, μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact abs_coord_le_mu_mul_l1_of_measurement_eq_zero hμ hA hker i
    _ = (S.card : ℝ) * μ * AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring

theorem nullspaceProperty_of_muIncoherentLE
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ)
    (hbound : (k : ℝ) * μ < 1 / 2) :
    NullspaceProperty A k := by
  classical
  intro h hker hne S hS
  have hexists : ∃ i, h i ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hne
    funext i
    exact hnone i
  have hl1_pos : 0 < AppliedModelingLib.FiniteDimensionalNorms.l1 h :=
    AppliedModelingLib.FiniteDimensionalNorms.normL1_pos_of_exists_ne_zero hexists
  have hsplit :
      AppliedModelingLib.FiniteDimensionalNorms.l1 h = l1On S h + l1On Sᶜ h :=
    l1_eq_l1On_add_l1On_compl S h
  have hS_nonneg : 0 ≤ l1On S h := by
    rw [l1On]
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (h i)
  have hSc_nonneg : 0 ≤ l1On Sᶜ h := by
    rw [l1On]
    exact Finset.sum_nonneg fun i _hi => abs_nonneg (h i)
  have hcoef_le : (S.card : ℝ) * μ ≤ (k : ℝ) * μ := by
    have hS_real : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hS
    exact mul_le_mul_of_nonneg_right hS_real hμ
  have hS_le :
      l1On S h ≤ (k : ℝ) * μ *
        AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
    have hraw :=
      l1On_le_card_mul_mu_mul_l1_of_measurement_eq_zero
        (A := A) (h := h) hμ hA hker S
    exact hraw.trans (mul_le_mul_of_nonneg_right hcoef_le
      (le_of_lt hl1_pos))
  by_contra hnot
  have hSc_le_S : l1On Sᶜ h ≤ l1On S h := le_of_not_gt hnot
  have hhalf_le :
      (1 / 2 : ℝ) * AppliedModelingLib.FiniteDimensionalNorms.l1 h ≤ l1On S h := by
    rw [hsplit]
    nlinarith
  have hlt :
      l1On S h < (1 / 2 : ℝ) *
        AppliedModelingLib.FiniteDimensionalNorms.l1 h := by
    exact lt_of_le_of_lt hS_le
      (mul_lt_mul_of_pos_right hbound hl1_pos)
  exact not_lt_of_ge hhalf_le hlt

theorem basisPursuitExactRecovery_of_muIncoherentLE
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {k : ℕ} {μ : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ)
    (hbound : (k : ℝ) * μ < 1 / 2) :
    BasisPursuitExactRecovery A k :=
  basisPursuitExactRecovery_of_nullspaceProperty
    (nullspaceProperty_of_muIncoherentLE hμ hA hbound)

@[simp] theorem finsetIndicator_apply_mem [DecidableEq Feature]
    {T : Finset Feature} {i : Feature} (hi : i ∈ T) :
    finsetIndicator T i = 1 := by
  simp [finsetIndicator, hi]

@[simp] theorem finsetIndicator_apply_not_mem [DecidableEq Feature]
    {T : Finset Feature} {i : Feature} (hi : i ∉ T) :
    finsetIndicator T i = 0 := by
  simp [finsetIndicator, hi]

theorem support_finsetIndicator_subset [Fintype Feature] [DecidableEq Feature]
    (T : Finset Feature) :
    support (finsetIndicator T) ⊆ T := by
  intro i hi
  by_contra hnot
  have hzero : finsetIndicator T i = 0 := finsetIndicator_apply_not_mem hnot
  exact (mem_support.mp hi) hzero

theorem kSparse_finsetIndicator_of_card_le
    [Fintype Feature] [DecidableEq Feature] {T : Finset Feature} {k : ℕ}
    (hT : T.card ≤ k) :
    KSparse k (finsetIndicator T) := by
  exact (Finset.card_le_card (support_finsetIndicator_subset T)).trans hT

theorem inUnitBox_finsetIndicator [DecidableEq Feature] (T : Finset Feature) :
    InUnitBox (finsetIndicator T : Feature → ℝ) := by
  intro i
  by_cases hi : i ∈ T <;> simp [finsetIndicator, hi]

theorem inZeroOne_finsetIndicator [DecidableEq Feature] (T : Finset Feature) :
    InZeroOne (finsetIndicator T : Feature → ℝ) := by
  intro i
  by_cases hi : i ∈ T
  · exact Or.inr (finsetIndicator_apply_mem hi)
  · exact Or.inl (finsetIndicator_apply_not_mem hi)

theorem linearProbe_finsetIndicator
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (T : Finset Feature) (i : Feature) :
    linearProbe A B (finsetIndicator T) i =
      ∑ j ∈ T, inner (B i) (A j) := by
  classical
  rw [linearProbe]
  calc
    (∑ j, finsetIndicator T j * inner (B i) (A j)) =
        ∑ j ∈ (Finset.univ.filter fun j : Feature => j ∈ T),
          inner (B i) (A j) := by
            simp [finsetIndicator]
    _ = ∑ j ∈ T, inner (B i) (A j) := by
          refine Finset.sum_congr ?_ ?_
          · ext j
            simp
          · intro j _hj
            rfl

theorem support_erase_card_le_of_ksparse [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} {k : ℕ} (hz : KSparse k z) (i : Feature) :
    ((support z).erase i).card ≤ k := by
  exact (Finset.card_erase_le (s := support z) (a := i)).trans hz

theorem sum_univ_erase_eq_support_erase [Fintype Feature] [DecidableEq Feature]
    {z : Feature → ℝ} (i : Feature) (f : Feature → ℝ) :
    (∑ j ∈ (Finset.univ : Finset Feature).erase i, z j * f j) =
      ∑ j ∈ (support z).erase i, z j * f j := by
  classical
  have hsubset :
      (support z).erase i ⊆ (Finset.univ : Finset Feature).erase i := by
    intro j hj
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ j⟩
  refine (Finset.sum_subset hsubset ?_).symm
  intro j hj_univ hj_support
  have hj_not_support : j ∉ support z := by
    intro hj
    exact hj_support (Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hj_univ).1, hj⟩)
  have hzj : z j = 0 := (not_mem_support_iff.mp hj_not_support)
  simp [hzj]

theorem linearProbe_self_sub_eq_offdiag_sum
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ} (i : Feature)
    (hself : inner (A i) (A i) = 1) :
    linearProbe A A z i - z i =
      ∑ j ∈ (Finset.univ : Finset Feature).erase i,
        z j * inner (A i) (A j) := by
  classical
  rw [linearProbe]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
    (s := (Finset.univ : Finset Feature)) (i := i) (by simp)]
  simp [hself]

theorem linearProbe_sub_eq_diag_error_add_offdiag_sum
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {z : Feature → ℝ} (i : Feature) :
    linearProbe A B z i - z i =
      z i * (inner (B i) (A i) - 1) +
        ∑ j ∈ (Finset.univ : Finset Feature).erase i,
          z j * inner (B i) (A j) := by
  classical
  rw [linearProbe]
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem
    (s := (Finset.univ : Finset Feature)) (i := i) (by simp)]
  have hsum :
      (∑ x ∈ (Finset.univ : Finset Feature) \ {i},
          z x * inner (B i) (A x)) =
        ∑ x ∈ (Finset.univ : Finset Feature).erase i,
          z x * inner (B i) (A x) := by
    refine Finset.sum_congr ?_ ?_
    · ext x
      simp
    · intro x _hx
      rfl
  rw [hsum]
  ring

theorem abs_sum_support_erase_inner_le_card_mul
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hbox : InUnitBox z) (hA : MuIncoherentLE A μ) (i : Feature) :
    |∑ j ∈ (support z).erase i, z j * inner (A i) (A j)| ≤
      (((support z).erase i).card : ℝ) * μ := by
  classical
  calc
    |∑ j ∈ (support z).erase i, z j * inner (A i) (A j)| ≤
        ∑ j ∈ (support z).erase i, |z j * inner (A i) (A j)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (support z).erase i, μ := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          have hz_abs : |z j| ≤ 1 := hbox j
          have hinner_abs : |inner (A i) (A j)| ≤ μ :=
            hA.offdiag_abs_le (by exact hji.symm)
          calc
            |z j * inner (A i) (A j)| =
                |z j| * |inner (A i) (A j)| := by rw [abs_mul]
            _ ≤ 1 * μ := by
                nlinarith [hz_abs, hinner_abs, abs_nonneg (z j),
                  abs_nonneg (inner (A i) (A j)), hμ]
            _ = μ := by ring
    _ = (((support z).erase i).card : ℝ) * μ := by
          rw [Finset.sum_const, nsmul_eq_mul]

theorem abs_sum_support_erase_crossInner_le_card_mul
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {z : Feature → ℝ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hbox : InUnitBox z)
    (hoffdiag : ∀ ⦃i j : Feature⦄, i ≠ j → |inner (B i) (A j)| ≤ μ)
    (i : Feature) :
    |∑ j ∈ (support z).erase i, z j * inner (B i) (A j)| ≤
      (((support z).erase i).card : ℝ) * μ := by
  classical
  calc
    |∑ j ∈ (support z).erase i, z j * inner (B i) (A j)| ≤
        ∑ j ∈ (support z).erase i, |z j * inner (B i) (A j)| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ (support z).erase i, μ := by
          refine Finset.sum_le_sum ?_
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          have hz_abs : |z j| ≤ 1 := hbox j
          have hinner_abs : |inner (B i) (A j)| ≤ μ :=
            hoffdiag (by exact hji.symm)
          calc
            |z j * inner (B i) (A j)| =
                |z j| * |inner (B i) (A j)| := by rw [abs_mul]
            _ ≤ 1 * μ := by
                nlinarith [hz_abs, hinner_abs, abs_nonneg (z j),
                  abs_nonneg (inner (B i) (A j)), hμ]
            _ = μ := by ring
    _ = (((support z).erase i).card : ℝ) * μ := by
          rw [Finset.sum_const, nsmul_eq_mul]

theorem supErrorLt_of_diag_abs_sub_one_le_offdiag_abs_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {z : Feature → ℝ}
    {k : ℕ} {ν μ ε : ℝ}
    (hν : 0 ≤ ν) (hμ : 0 ≤ μ)
    (hdiag : ∀ i : Feature, |inner (B i) (A i) - 1| ≤ ν)
    (hoffdiag : ∀ ⦃i j : Feature⦄, i ≠ j → |inner (B i) (A j)| ≤ μ)
    (hz_sparse : KSparse k z) (hz_box : InUnitBox z)
    (hbound : ν + (k : ℝ) * μ < ε) :
    SupErrorLt A B z ε := by
  classical
  intro i
  rw [linearProbe_sub_eq_diag_error_add_offdiag_sum (A := A) (B := B) (z := z) i]
  rw [sum_univ_erase_eq_support_erase i (fun j => inner (B i) (A j))]
  have hdiag_term :
      |z i * (inner (B i) (A i) - 1)| ≤ ν := by
    calc
      |z i * (inner (B i) (A i) - 1)| =
          |z i| * |inner (B i) (A i) - 1| := by rw [abs_mul]
      _ ≤ 1 * ν := by
          nlinarith [hz_box i, hdiag i, abs_nonneg (z i),
            abs_nonneg (inner (B i) (A i) - 1), hν]
      _ = ν := by ring
  have hsum :=
    abs_sum_support_erase_crossInner_le_card_mul
      (A := A) (B := B) (z := z) (μ := μ) hμ hz_box hoffdiag i
  have hcard : (((support z).erase i).card : ℝ) * μ ≤ (k : ℝ) * μ := by
    have hcard_nat := support_erase_card_le_of_ksparse hz_sparse i
    have hcard_real : (((support z).erase i).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hcard_nat
    exact mul_le_mul_of_nonneg_right hcard_real hμ
  calc
    |z i * (inner (B i) (A i) - 1) +
        ∑ j ∈ (support z).erase i, z j * inner (B i) (A j)| ≤
        |z i * (inner (B i) (A i) - 1)| +
          |∑ j ∈ (support z).erase i, z j * inner (B i) (A j)| := by
          exact abs_add_le _ _
    _ ≤ ν + (((support z).erase i).card : ℝ) * μ := by
          exact add_le_add hdiag_term hsum
    _ ≤ ν + (k : ℝ) * μ := by
          nlinarith
    _ < ε := hbound

/--
Deterministic upper-bound core: incoherent representation/probe columns with
`B = A` recover every `k`-sparse vector in the unit box up to `l_infty` error
`ε` whenever `k * μ < ε`.
-/
theorem supErrorLt_of_muIncoherentLE_self
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A : Feature → Coord → ℝ} {z : Feature → ℝ} {k : ℕ} {μ ε : ℝ}
    (hμ : 0 ≤ μ) (hA : MuIncoherentLE A μ) (hz_sparse : KSparse k z)
    (hz_box : InUnitBox z) (hbound : (k : ℝ) * μ < ε) :
    SupErrorLt A A z ε := by
  classical
  intro i
  have hdiff :
      linearProbe A A z i - z i =
        ∑ j ∈ (support z).erase i, z j * inner (A i) (A j) := by
    rw [linearProbe_self_sub_eq_offdiag_sum i (hA.self_inner i)]
    exact sum_univ_erase_eq_support_erase i (fun j => inner (A i) (A j))
  rw [hdiff]
  have hsum :=
    abs_sum_support_erase_inner_le_card_mul (A := A) (z := z)
      (μ := μ) hμ hz_box hA i
  have hcard : (((support z).erase i).card : ℝ) * μ ≤ (k : ℝ) * μ := by
    have hcard_nat := support_erase_card_le_of_ksparse hz_sparse i
    have hcard_real : (((support z).erase i).card : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast hcard_nat
    exact mul_le_mul_of_nonneg_right hcard_real hμ
  exact lt_of_le_of_lt (hsum.trans hcard) hbound

/--
Testing recovery on a singleton indicator gives the diagonal
observation: each diagonal entry of `B^T A` is within `ε` of `1`.
-/
theorem diag_abs_sub_one_lt_of_linearRecovery
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (i : Feature) :
    |inner (B i) (A i) - 1| < ε := by
  classical
  let T : Finset Feature := {i}
  have hTcard : T.card ≤ k := by simpa [T] using hk
  have h := hrec (finsetIndicator T)
    (kSparse_finsetIndicator_of_card_le (T := T) hTcard)
    (inUnitBox_finsetIndicator T) i
  have hprobe :
      linearProbe A B (finsetIndicator T) i = inner (B i) (A i) := by
    simp [linearProbe_finsetIndicator, T]
  have hzi : finsetIndicator T i = 1 := by simp [T]
  simpa [hprobe, hzi] using h

/-- Lower form of `diag_abs_sub_one_lt_of_linearRecovery`. -/
theorem one_sub_lt_diag_of_linearRecovery
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (i : Feature) :
    1 - ε < inner (B i) (A i) := by
  have hdiag := diag_abs_sub_one_lt_of_linearRecovery
    (A := A) (B := B) (k := k) (ε := ε) hk hrec i
  have hleft := (abs_lt.mp hdiag).1
  linarith

/--
Testing recovery on a `{0,1}` indicator set disjoint from row `i` gives the
row-sum observation.
-/
theorem abs_row_sum_lt_of_linearRecovery_finsetIndicator_not_mem
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {k : ℕ} {ε : ℝ}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    {T : Finset Feature} {i : Feature} (hT : T.card ≤ k) (hi : i ∉ T) :
    |∑ j ∈ T, inner (B i) (A j)| < ε := by
  classical
  have h := hrec (finsetIndicator T)
    (kSparse_finsetIndicator_of_card_le (T := T) hT)
    (inUnitBox_finsetIndicator T) i
  have hprobe :
      linearProbe A B (finsetIndicator T) i =
        ∑ j ∈ T, inner (B i) (A j) :=
    linearProbe_finsetIndicator A B T i
  have hzi : finsetIndicator T i = 0 := finsetIndicator_apply_not_mem hi
  simpa [hprobe, hzi] using h

theorem offdiag_abs_lt_of_linearRecovery
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {k : ℕ} {ε : ℝ}
    (hk : 1 ≤ k)
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    {i j : Feature} (hij : i ≠ j) :
    |inner (B i) (A j)| < ε := by
  classical
  let T : Finset Feature := {j}
  have hTcard : T.card ≤ k := by simpa [T] using hk
  have hi_not : i ∉ T := by
    simp [T, hij]
  have hrow :=
    abs_row_sum_lt_of_linearRecovery_finsetIndicator_not_mem
      (A := A) (B := B) (k := k) (ε := ε) hrec hTcard hi_not
  have hsum : (∑ x ∈ T, inner (B i) (A x)) = inner (B i) (A j) := by
    simp [T]
  simpa [hsum] using hrow

/--
Threshold separation for Boolean feature vectors: row `i` crosses threshold
exactly on `k`-sparse Boolean vectors with feature `i` present.
-/
def ThresholdSeparates [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (threshold : Feature → ℝ) (k : ℕ) : Prop :=
  ∀ i (z : Feature → ℝ), KSparse k z → InZeroOne z →
    (threshold i < linearProbe A B z i ↔ z i = 1)

/-- Row-wise positive rescaling of probe vectors by their diagonal response. -/
noncomputable def diagonalNormalizedProbes [Fintype Coord]
    (A B : Feature → Coord → ℝ) : Feature → Coord → ℝ :=
  fun i r => (inner (B i) (A i))⁻¹ * B i r

/-- Matching threshold rescaling for `diagonalNormalizedProbes`. -/
noncomputable def diagonalNormalizedThreshold [Fintype Coord]
    (A B : Feature → Coord → ℝ) (threshold : Feature → ℝ) : Feature → ℝ :=
  fun i => (inner (B i) (A i))⁻¹ * threshold i

theorem threshold_nonneg_of_thresholdSeparates
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ} {k : ℕ}
    (hsep : ThresholdSeparates A B threshold k) (i : Feature) :
    0 ≤ threshold i := by
  classical
  let z : Feature → ℝ := fun _ => 0
  have hsparse : KSparse k z := by
    unfold KSparse support z
    simp
  have hzeroone : InZeroOne z := by
    intro j
    exact Or.inl rfl
  have hiff := hsep i z hsparse hzeroone
  have hz : z i ≠ 1 := by simp [z]
  have hnot : ¬ threshold i < linearProbe A B z i := by
    intro hlt
    exact hz (hiff.mp hlt)
  have hprobe : linearProbe A B z i = 0 := by
    simp [linearProbe, z]
  exact not_lt.mp (by simpa [hprobe] using hnot)

theorem threshold_lt_diag_of_thresholdSeparates
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hsep : ThresholdSeparates A B threshold k) (i : Feature) :
    threshold i < inner (B i) (A i) := by
  classical
  let T : Finset Feature := {i}
  have hTcard : T.card ≤ k := by simpa [T] using hk
  have hiff := hsep i (finsetIndicator T)
    (kSparse_finsetIndicator_of_card_le (T := T) hTcard)
    (inZeroOne_finsetIndicator T)
  have hzi : finsetIndicator T i = 1 := by simp [T]
  have hprobe :
      linearProbe A B (finsetIndicator T) i = inner (B i) (A i) := by
    simp [linearProbe_finsetIndicator, T]
  exact (by simpa [hprobe] using hiff.mpr hzi)

theorem diag_pos_of_thresholdSeparates
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hsep : ThresholdSeparates A B threshold k) (i : Feature) :
    0 < inner (B i) (A i) := by
  have hnonneg :=
    threshold_nonneg_of_thresholdSeparates
      (A := A) (B := B) (threshold := threshold) (k := k) hsep i
  have hlt :=
    threshold_lt_diag_of_thresholdSeparates
      (A := A) (B := B) (threshold := threshold) (k := k) hk hsep i
  exact lt_of_le_of_lt hnonneg hlt

@[simp] theorem inner_diagonalNormalizedProbes_self
    [Fintype Coord] {A B : Feature → Coord → ℝ} {i : Feature}
    (hdiag : inner (B i) (A i) ≠ 0) :
    inner (diagonalNormalizedProbes A B i) (A i) = 1 := by
  classical
  calc
    inner (diagonalNormalizedProbes A B i) (A i)
        = ∑ r, (inner (B i) (A i))⁻¹ * (B i r * A i r) := by
            simp [diagonalNormalizedProbes, inner, mul_assoc]
    _ = (inner (B i) (A i))⁻¹ * ∑ r, B i r * A i r := by
          rw [Finset.mul_sum]
    _ = 1 := by
          have hsum_ne : (∑ r, B i r * A i r) ≠ 0 := by
            simpa [inner] using hdiag
          exact inv_mul_cancel₀ hsum_ne

theorem linearProbe_diagonalNormalizedProbes
    [Fintype Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (z : Feature → ℝ) (i : Feature) :
    linearProbe A (diagonalNormalizedProbes A B) z i =
      (inner (B i) (A i))⁻¹ * linearProbe A B z i := by
  classical
  simp [linearProbe, diagonalNormalizedProbes, inner, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm]

theorem thresholdSeparates_diagonalNormalized
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hsep : ThresholdSeparates A B threshold k) :
    ThresholdSeparates A (diagonalNormalizedProbes A B)
      (diagonalNormalizedThreshold A B threshold) k := by
  intro i z hz_sparse hz_zeroone
  have hdiag_pos : 0 < inner (B i) (A i) :=
    diag_pos_of_thresholdSeparates
      (A := A) (B := B) (threshold := threshold) (k := k) hk hsep i
  have hinv_pos : 0 < (inner (B i) (A i))⁻¹ := inv_pos.mpr hdiag_pos
  have hprobe :=
    linearProbe_diagonalNormalizedProbes (A := A) (B := B) z i
  have hiff := hsep i z hz_sparse hz_zeroone
  rw [diagonalNormalizedThreshold, hprobe]
  exact ⟨fun h => hiff.mp (lt_of_mul_lt_mul_left h hinv_pos.le),
    fun hz => mul_lt_mul_of_pos_left (hiff.mpr hz) hinv_pos⟩

theorem diagonalNormalizedProbes_diag_eq_one_of_thresholdSeparates
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hsep : ThresholdSeparates A B threshold k) (i : Feature) :
    inner (diagonalNormalizedProbes A B i) (A i) = 1 := by
  have hdiag_pos : 0 < inner (B i) (A i) :=
    diag_pos_of_thresholdSeparates
      (A := A) (B := B) (threshold := threshold) (k := k) hk hsep i
  exact inner_diagonalNormalizedProbes_self (A := A) (B := B) (i := i)
    (ne_of_gt hdiag_pos)

/-- Sparse Boolean supports available for negative examples of feature `i`. -/
noncomputable def negativeBooleanSupportFinset
    [Fintype Feature] [DecidableEq Feature] (i : Feature) (k : ℕ) :
    Finset (Finset Feature) :=
  (Finset.univ : Finset Feature).powerset.filter fun T => i ∉ T ∧ T.card ≤ k

theorem mem_negativeBooleanSupportFinset
    [Fintype Feature] [DecidableEq Feature] {i : Feature} {k : ℕ}
    {T : Finset Feature} :
    T ∈ negativeBooleanSupportFinset i k ↔ i ∉ T ∧ T.card ≤ k := by
  classical
  simp [negativeBooleanSupportFinset]

theorem negativeBooleanSupportFinset_nonempty
    [Fintype Feature] [DecidableEq Feature] (i : Feature) (k : ℕ) :
    (negativeBooleanSupportFinset i k).Nonempty := by
  classical
  refine ⟨∅, ?_⟩
  simp [negativeBooleanSupportFinset]

theorem finsetIndicator_support_eq_of_inZeroOne
    [Fintype Feature] [DecidableEq Feature] {z : Feature → ℝ}
    (hz : InZeroOne z) :
    finsetIndicator (support z) = z := by
  funext i
  by_cases hi : i ∈ support z
  · have hne : z i ≠ 0 := mem_support.mp hi
    rcases hz i with hzero | hone
    · exact False.elim (hne hzero)
    · simp [finsetIndicator, hi, hone]
  · have hzero : z i = 0 := (not_mem_support_iff.mp hi)
    simp [finsetIndicator, hi, hzero]

/-- Preactivation scores of all sparse Boolean negative examples for feature `i`. -/
noncomputable def activationNegativeScoreFinset
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A W : Feature → Coord → ℝ) (bias : Feature → ℝ) (k : ℕ)
    (i : Feature) : Finset ℝ :=
  (negativeBooleanSupportFinset i k).image
    (fun T => linearProbe A W (finsetIndicator T) i + bias i)

theorem activationNegativeScoreFinset_nonempty
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A W : Feature → Coord → ℝ) (bias : Feature → ℝ) (k : ℕ)
    (i : Feature) :
    (activationNegativeScoreFinset A W bias k i).Nonempty := by
  classical
  rcases negativeBooleanSupportFinset_nonempty (Feature := Feature) i k with ⟨T, hT⟩
  exact ⟨linearProbe A W (finsetIndicator T) i + bias i,
    Finset.mem_image.mpr ⟨T, hT, rfl⟩⟩

/--
Preactivation threshold extracted from a monotone activation separator.  It is
the maximum preactivation value on sparse Boolean vectors with feature `i`
absent, translated back to a threshold for the linear probe before adding the
bias.
-/
noncomputable def activationDerivedThreshold
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A W : Feature → Coord → ℝ) (bias : Feature → ℝ) (k : ℕ)
    (i : Feature) : ℝ :=
  (activationNegativeScoreFinset A W bias k i).max'
      (activationNegativeScoreFinset_nonempty A W bias k i) -
    bias i

/--
If a monotone activation separates positive and negative Boolean sparse
examples, then the underlying affine score has a source-compatible linear
threshold separator.
-/
theorem thresholdSeparates_of_monotone_activation
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A W : Feature → Coord → ℝ} {bias : Feature → ℝ} {σ : ℝ → ℝ} {k : ℕ}
    (hmono : Monotone σ)
    (hact : ∀ i (z : Feature → ℝ), KSparse k z → InZeroOne z →
      (0 < σ (linearProbe A W z i + bias i) ↔ z i = 1)) :
    ThresholdSeparates A W (activationDerivedThreshold A W bias k) k := by
  classical
  intro i z hz_sparse hz_zeroone
  constructor
  · intro hcross
    by_contra hz_ne
    have hzi_zero : z i = 0 := by
      rcases hz_zeroone i with h0 | h1
      · exact h0
      · exact False.elim (hz_ne h1)
    let T : Finset Feature := support z
    have hTmem : T ∈ negativeBooleanSupportFinset i k := by
      rw [mem_negativeBooleanSupportFinset]
      refine ⟨?_, hz_sparse⟩
      have hi_not : i ∉ support z := by
        rw [mem_support]
        intro hne
        exact hne hzi_zero
      simpa [T] using hi_not
    have hz_eq : finsetIndicator T = z := by
      simpa [T] using finsetIndicator_support_eq_of_inZeroOne hz_zeroone
    have hscore_mem :
        linearProbe A W (finsetIndicator T) i + bias i ∈
          activationNegativeScoreFinset A W bias k i := by
      exact Finset.mem_image.mpr ⟨T, hTmem, rfl⟩
    have hle_max :
        linearProbe A W (finsetIndicator T) i + bias i ≤
          (activationNegativeScoreFinset A W bias k i).max'
            (activationNegativeScoreFinset_nonempty A W bias k i) := by
      exact (activationNegativeScoreFinset A W bias k i).le_max'
        (linearProbe A W (finsetIndicator T) i + bias i) hscore_mem
    have hle_max_z :
        linearProbe A W z i + bias i ≤
          (activationNegativeScoreFinset A W bias k i).max'
            (activationNegativeScoreFinset_nonempty A W bias k i) := by
      simpa [hz_eq] using hle_max
    have hle_threshold :
        linearProbe A W z i ≤ activationDerivedThreshold A W bias k i := by
      dsimp [activationDerivedThreshold]
      nlinarith [hle_max_z]
    exact (not_lt.mpr hle_threshold) hcross
  · intro hzi_one
    have hz_pos :
        0 < σ (linearProbe A W z i + bias i) :=
      (hact i z hz_sparse hz_zeroone).mpr hzi_one
    have hmax_lt_score :
        (activationNegativeScoreFinset A W bias k i).max'
            (activationNegativeScoreFinset_nonempty A W bias k i) <
          linearProbe A W z i + bias i := by
      rw [Finset.max'_lt_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨U, hU, rfl⟩
      have hU_sparse : KSparse k (finsetIndicator U : Feature → ℝ) :=
        kSparse_finsetIndicator_of_card_le (T := U)
          (mem_negativeBooleanSupportFinset.mp hU).2
      have hU_zeroone : InZeroOne (finsetIndicator U : Feature → ℝ) :=
        inZeroOne_finsetIndicator U
      have hUi_zero : finsetIndicator U i = 0 :=
        finsetIndicator_apply_not_mem (mem_negativeBooleanSupportFinset.mp hU).1
      have hU_not_pos :
          ¬ 0 < σ (linearProbe A W (finsetIndicator U) i + bias i) := by
        intro hpos
        have hbad := (hact i (finsetIndicator U) hU_sparse hU_zeroone).mp hpos
        have hzero_ne_one : (0 : ℝ) ≠ 1 := by norm_num
        exact hzero_ne_one (by simpa [hUi_zero] using hbad)
      have hscore_lt :
          linearProbe A W (finsetIndicator U) i + bias i <
            linearProbe A W z i + bias i := by
        by_contra hnot_lt
        have hge :
            linearProbe A W z i + bias i ≤
              linearProbe A W (finsetIndicator U) i + bias i :=
          not_lt.mp hnot_lt
        have hsigma_le := hmono hge
        exact hU_not_pos (lt_of_lt_of_le hz_pos hsigma_le)
      exact hscore_lt
    have hthreshold_lt_score :
        activationDerivedThreshold A W bias k i < linearProbe A W z i := by
      dsimp [activationDerivedThreshold]
      nlinarith [hmax_lt_score]
    exact hthreshold_lt_score

/--
Finite sign pigeonhole: if more than `2k` entries have absolute value larger
than `η`, then some `k` of them have aligned signs and their sum has absolute
value larger than `k * η`.
-/
theorem exists_subset_card_eq_abs_sum_gt_of_two_mul_lt_card_large_abs
    [DecidableEq Feature] {S : Finset Feature} {f : Feature → ℝ} {η : ℝ} {k : ℕ}
    (hη : 0 ≤ η) (hk : 0 < k)
    (hlarge : ∀ j ∈ S, η < |f j|) (hcard : 2 * k < S.card) :
    ∃ T : Finset Feature,
      T ⊆ S ∧ T.card = k ∧ (k : ℝ) * η < |∑ j ∈ T, f j| := by
  classical
  let Pos : Finset Feature := S.filter fun j => 0 ≤ f j
  let Neg : Finset Feature := S.filter fun j => f j < 0
  have hPos_subset : Pos ⊆ S := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hNeg_subset : Neg ⊆ S := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hunion : Pos ∪ Neg = S := by
    ext j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hj | hj
      · exact hPos_subset hj
      · exact hNeg_subset hj
    · intro hjS
      by_cases hnonneg : 0 ≤ f j
      · exact Finset.mem_union.mpr
          (Or.inl (Finset.mem_filter.mpr ⟨hjS, hnonneg⟩))
      · have hneg : f j < 0 := lt_of_not_ge hnonneg
        exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_filter.mpr ⟨hjS, hneg⟩))
  have hcard_union : 2 * k < (Pos ∪ Neg).card := by
    simpa [hunion] using hcard
  rcases Finset.exists_subset_or_subset_of_two_mul_lt_card hcard_union with
    ⟨C, hCcard, hCsub | hCsub⟩
  · rcases Finset.exists_subset_card_eq (Nat.le_of_lt hCcard) with
      ⟨T, hTC, hTcard⟩
    have hTS : T ⊆ S := hTC.trans (hCsub.trans hPos_subset)
    have hT_nonempty : T.Nonempty := by
      exact Finset.card_pos.mp (by simpa [hTcard] using hk)
    have hterm : ∀ j ∈ T, η < f j := by
      intro j hjT
      have hjPos : j ∈ Pos := hCsub (hTC hjT)
      have hjS : j ∈ S := hTS hjT
      have hnonneg : 0 ≤ f j := (Finset.mem_filter.mp hjPos).2
      simpa [abs_of_nonneg hnonneg] using hlarge j hjS
    have hsum_gt : (∑ _j ∈ T, η) < ∑ j ∈ T, f j := by
      exact Finset.sum_lt_sum_of_nonempty hT_nonempty hterm
    have hsum_nonneg : 0 ≤ ∑ j ∈ T, f j := by
      refine Finset.sum_nonneg ?_
      intro j hjT
      have hjPos : j ∈ Pos := hCsub (hTC hjT)
      exact (Finset.mem_filter.mp hjPos).2
    refine ⟨T, hTS, hTcard, ?_⟩
    calc
      (k : ℝ) * η = ∑ _j ∈ T, η := by
        simp [Finset.sum_const, nsmul_eq_mul, hTcard]
      _ < ∑ j ∈ T, f j := hsum_gt
      _ = |∑ j ∈ T, f j| := (abs_of_nonneg hsum_nonneg).symm
  · rcases Finset.exists_subset_card_eq (Nat.le_of_lt hCcard) with
      ⟨T, hTC, hTcard⟩
    have hTS : T ⊆ S := hTC.trans (hCsub.trans hNeg_subset)
    have hT_nonempty : T.Nonempty := by
      exact Finset.card_pos.mp (by simpa [hTcard] using hk)
    have hterm : ∀ j ∈ T, η < -f j := by
      intro j hjT
      have hjNeg : j ∈ Neg := hCsub (hTC hjT)
      have hjS : j ∈ S := hTS hjT
      have hneg : f j < 0 := (Finset.mem_filter.mp hjNeg).2
      simpa [abs_of_neg hneg] using hlarge j hjS
    have hsum_gt : (∑ _j ∈ T, η) < ∑ j ∈ T, -f j := by
      exact Finset.sum_lt_sum_of_nonempty hT_nonempty hterm
    have hsum_nonpos : ∑ j ∈ T, f j ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro j hjT
      have hjNeg : j ∈ Neg := hCsub (hTC hjT)
      exact le_of_lt (Finset.mem_filter.mp hjNeg).2
    refine ⟨T, hTS, hTcard, ?_⟩
    calc
      (k : ℝ) * η = ∑ _j ∈ T, η := by
        simp [Finset.sum_const, nsmul_eq_mul, hTcard]
      _ < ∑ j ∈ T, -f j := hsum_gt
      _ = -∑ j ∈ T, f j := by rw [Finset.sum_neg_distrib]
      _ = |∑ j ∈ T, f j| := (abs_of_nonpos hsum_nonpos).symm

/--
Directed large off-diagonal relation for a representation/probe pair: row `i`
has large interference with column `j`, excluding the diagonal.
-/
def LargeOffdiag [Fintype Coord]
    (A B : Feature → Coord → ℝ) (η : ℝ) (i j : Feature) : Prop :=
  i ≠ j ∧ η < |inner (B i) (A j)|

/-- The undirected graph whose edges are pairs with a large off-diagonal entry in either direction. -/
noncomputable def largeOffdiagGraph
    [DecidableEq Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (η : ℝ) : SimpleGraph Feature :=
  by
    classical
    exact SimpleGraph.fromRel (LargeOffdiag A B η)

@[simp] theorem largeOffdiagGraph_adj
    [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {i j : Feature} :
    (largeOffdiagGraph A B η).Adj i j ↔
      i ≠ j ∧
        (η < |inner (B i) (A j)| ∨ η < |inner (B j) (A i)|) := by
  classical
  rw [largeOffdiagGraph]
  simp only [SimpleGraph.fromRel_adj, LargeOffdiag]
  constructor
  · intro h
    rcases h with ⟨hij, hdir⟩
    rcases hdir with ⟨_hij, hlarge⟩ | ⟨_hji, hlarge⟩
    · exact ⟨hij, Or.inl hlarge⟩
    · exact ⟨hij, Or.inr hlarge⟩
  · intro h
    rcases h with ⟨hij, hlarge | hlarge⟩
    · exact And.intro hij (Or.inl (And.intro hij hlarge))
    · exact And.intro hij (Or.inr (And.intro hij.symm hlarge))

/--
Convert the natural principal-submatrix output of an Alon/rank obstruction into
the graph hypothesis used by the Turán step.
-/
theorem forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {s : ℕ}
    (h : ∀ t : Finset Feature, t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧
          η < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y|) :
    ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j := by
  classical
  intro t ht
  rcases h t ht with ⟨x, y, hxy, hlarge⟩
  have hval_ne : (x : Feature) ≠ (y : Feature) := by
    intro hval
    exact hxy (Subtype.ext hval)
  have hlarge' : η < |inner (B (x : Feature)) (A (y : Feature))| := by
    simpa using hlarge
  refine ⟨x, x.property, y, y.property, hval_ne, ?_⟩
  exact largeOffdiagGraph_adj.mpr ⟨hval_ne, Or.inl hlarge'⟩

/-- All directed large off-diagonal entries. -/
noncomputable def largeOffdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (η : ℝ) : Finset (Feature × Feature) :=
  by
    classical
    exact FiniteRelation.directedPairFinset (LargeOffdiag A B η)

/-- Large off-diagonal entries in a fixed row. -/
noncomputable def largeOffdiagRowFinset
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (A B : Feature → Coord → ℝ) (η : ℝ) (i : Feature) : Finset Feature :=
  by
    classical
    exact FiniteRelation.rowFinset (LargeOffdiag A B η) i

@[simp] theorem mem_largeOffdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {p : Feature × Feature} :
    p ∈ largeOffdiagPairFinset A B η ↔
      p.1 ≠ p.2 ∧ η < |inner (B p.1) (A p.2)| := by
  classical
  simp [largeOffdiagPairFinset, LargeOffdiag]

@[simp] theorem mem_largeOffdiagRowFinset
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {i j : Feature} :
    j ∈ largeOffdiagRowFinset A B η i ↔
      i ≠ j ∧ η < |inner (B i) (A j)| := by
  classical
  simp [largeOffdiagRowFinset, LargeOffdiag]

/--
A row with more than `2k` large off-diagonal entries contains a `k`-element
off-diagonal subset whose row sum has absolute value larger than `k * η`.
-/
theorem exists_finset_card_eq_abs_row_sum_gt_of_two_mul_lt_largeOffdiagRow_card
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {k : ℕ} {i : Feature}
    (hη : 0 ≤ η) (hk : 0 < k)
    (hrow : 2 * k < (largeOffdiagRowFinset A B η i).card) :
    ∃ T : Finset Feature,
      T.card = k ∧ i ∉ T ∧ (k : ℝ) * η < |∑ j ∈ T, inner (B i) (A j)| := by
  classical
  have hlarge :
      ∀ j ∈ largeOffdiagRowFinset A B η i, η < |inner (B i) (A j)| := by
    intro j hj
    exact (mem_largeOffdiagRowFinset.mp hj).2
  rcases
    exists_subset_card_eq_abs_sum_gt_of_two_mul_lt_card_large_abs
      (Feature := Feature) (S := largeOffdiagRowFinset A B η i)
      (f := fun j => inner (B i) (A j)) hη hk hlarge hrow with
    ⟨T, hTsub, hTcard, hsum⟩
  have hi_not : i ∉ T := by
    intro hiT
    have hi_row := hTsub hiT
    exact (mem_largeOffdiagRowFinset.mp hi_row).1 rfl
  exact ⟨T, hTcard, hi_not, hsum⟩

/--
The source contradiction step for linear recovery: a row with more than `2k`
entries larger than `η` is impossible if recovery bounds all disjoint
`k`-sparse indicator row sums by `ε` and `ε <= k * η`.
-/
theorem false_of_linearRecovery_and_two_mul_lt_largeOffdiagRow_card
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η ε : ℝ} {k : ℕ} {i : Feature}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (hη : 0 ≤ η) (hk : 0 < k) (hε_le : ε ≤ (k : ℝ) * η)
    (hrow : 2 * k < (largeOffdiagRowFinset A B η i).card) :
    False := by
  classical
  rcases
    exists_finset_card_eq_abs_row_sum_gt_of_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (η := η) (k := k) (i := i) hη hk hrow with
    ⟨T, hTcard, hi_not, hsum_gt⟩
  have hTle : T.card ≤ k := by
    exact le_of_eq hTcard
  have hsum_lt :
      |∑ j ∈ T, inner (B i) (A j)| < ε :=
    abs_row_sum_lt_of_linearRecovery_finsetIndicator_not_mem
      (A := A) (B := B) (k := k) (ε := ε) hrec hTle hi_not
  linarith

/--
Pigeonhole form used after an extremal-graph lower bound: if the total number
of directed large off-diagonal entries exceeds `card Feature * q`, then some
row has more than `q` such entries.
-/
theorem exists_largeOffdiagRow_card_gt_of_card_mul_lt_pairFinset_card
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {q : ℕ}
    (h : Fintype.card Feature * q < (largeOffdiagPairFinset A B η).card) :
    ∃ i : Feature, q < (largeOffdiagRowFinset A B η i).card := by
  classical
  simpa [largeOffdiagPairFinset, largeOffdiagRowFinset] using
    FiniteRelation.exists_row_card_gt_of_card_mul_lt_directedPairFinset
      (V := Feature) (R := LargeOffdiag A B η) h

/--
Non-strict average form for directed large off-diagonal entries.
-/
theorem exists_largeOffdiagRow_card_ge_of_card_mul_le_pairFinset_card
    [Fintype Feature] [Nonempty Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {q : ℕ}
    (hq : 0 < q)
    (h : Fintype.card Feature * q ≤ (largeOffdiagPairFinset A B η).card) :
    ∃ i : Feature, q ≤ (largeOffdiagRowFinset A B η i).card := by
  classical
  simpa [largeOffdiagPairFinset, largeOffdiagRowFinset] using
    FiniteRelation.exists_row_card_ge_of_card_mul_le_directedPairFinset
      (V := Feature) (R := LargeOffdiag A B η) hq h

/--
Turán-counting form for large off-diagonal entries: if every `s`-element
feature set contains an edge of the large-off-diagonal graph, then the number
of directed large off-diagonal entries is at least the complement-Turán lower
bound.
-/
theorem largeOffdiagPairFinset_card_ge_choose_sub_turanBound_of_forall_finset_exists_graph_adj
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {s : ℕ}
    (hs : 0 < s)
    (h : ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j) :
    let n := Fintype.card Feature
    let r := s - 1
    n.choose 2 -
      ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2) ≤
        (largeOffdiagPairFinset A B η).card := by
  classical
  simpa [largeOffdiagPairFinset, largeOffdiagGraph] using
    FiniteRelation.card_directedPairFinset_ge_choose_sub_turanBound_of_forall_finset_exists_fromRel_adj
      (V := Feature) (R := LargeOffdiag A B η) hs h

/--
Pigeonhole consequence of the Turán-counting form: once the complement-Turán
lower bound beats `card Feature * q`, some row has more than `q` directed large
off-diagonal entries.
-/
theorem exists_largeOffdiagRow_card_gt_of_card_mul_lt_turanBound_of_forall_finset_exists_graph_adj
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {s q : ℕ}
    (hs : 0 < s)
    (hgraph : ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j)
    (havg :
      Fintype.card Feature * q <
        (let n := Fintype.card Feature
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2))) :
    ∃ i : Feature, q < (largeOffdiagRowFinset A B η i).card := by
  classical
  have hpair :
      (let n := Fintype.card Feature
       let r := s - 1
       n.choose 2 -
        ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2)) ≤
          (largeOffdiagPairFinset A B η).card :=
    largeOffdiagPairFinset_card_ge_choose_sub_turanBound_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) hs hgraph
  exact
    exists_largeOffdiagRow_card_gt_of_card_mul_lt_pairFinset_card
      (A := A) (B := B) (η := η) (q := q) (havg.trans_le hpair)

/--
Source-form coarse Turán-plus-pigeonhole consequence: if every `s`-feature set
has a large-off-diagonal edge and the coarse Turán lower bound beats
`card Feature * q`, then some row has more than `q` directed large entries.
-/
theorem exists_largeOffdiagRow_card_gt_of_real_card_mul_lt_coarse_turan_of_forall_finset_exists_graph_adj
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η : ℝ} {s q : ℕ}
    (hs : 1 < s)
    (hgraph : ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j)
    (havg :
      let n := Fintype.card Feature
      let r := s - 1
      (n : ℝ) * (q : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2) :
    ∃ i : Feature, q < (largeOffdiagRowFinset A B η i).card := by
  classical
  simpa [largeOffdiagGraph, largeOffdiagRowFinset] using
    FiniteRelation.exists_row_card_gt_of_real_card_mul_lt_coarse_turan_of_forall_finset_exists_fromRel_adj
      (V := Feature) (R := LargeOffdiag A B η) (s := s) (q := q)
      hs hgraph havg

/--
Full downstream lower-bound contradiction after the rank obstruction has
supplied the source hypothesis that every `s`-element feature set contains a
large-interference edge.
-/
theorem false_of_linearRecovery_and_card_mul_two_mul_lt_turanBound_of_forall_finset_exists_graph_adj
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η ε : ℝ} {s k : ℕ}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (hη : 0 ≤ η) (hk : 0 < k) (hε_le : ε ≤ (k : ℝ) * η)
    (hs : 0 < s)
    (hgraph : ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j)
    (havg :
      Fintype.card Feature * (2 * k) <
        (let n := Fintype.card Feature
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2))) :
    False := by
  classical
  rcases
    exists_largeOffdiagRow_card_gt_of_card_mul_lt_turanBound_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (s := s) (q := 2 * k) hs hgraph havg with
    ⟨i, hrow⟩
  exact
    false_of_linearRecovery_and_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (η := η) (ε := ε) (k := k) (i := i)
      hrec hη hk hε_le hrow

/--
Linear-recovery contradiction using the source-form coarse Turán average
estimate instead of the exact complement-Turán expression.
-/
theorem false_of_linearRecovery_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_finset_exists_graph_adj
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η ε : ℝ} {s k : ℕ}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (hη : 0 ≤ η) (hk : 0 < k) (hε_le : ε ≤ (k : ℝ) * η)
    (hs : 1 < s)
    (hgraph : ∀ t : Finset Feature, t.card = s →
      ∃ i ∈ t, ∃ j ∈ t, i ≠ j ∧ (largeOffdiagGraph A B η).Adj i j)
    (havg :
      let n := Fintype.card Feature
      let r := s - 1
      (n : ℝ) * ((2 * k : ℕ) : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2) :
    False := by
  classical
  rcases
    exists_largeOffdiagRow_card_gt_of_real_card_mul_lt_coarse_turan_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (s := s) (q := 2 * k)
      hs hgraph havg with
    ⟨i, hrow⟩
  exact
    false_of_linearRecovery_and_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (η := η) (ε := ε) (k := k) (i := i)
      hrec hη hk hε_le hrow

/--
Downstream lower-bound contradiction in the principal-submatrix form supplied
by the Alon/rank obstruction.
-/
theorem false_of_linearRecovery_and_card_mul_two_mul_lt_turanBound_of_forall_principalSubmatrix_exists_largeOffdiag
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η ε : ℝ} {s k : ℕ}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (hη : 0 ≤ η) (hk : 0 < k) (hε_le : ε ≤ (k : ℝ) * η)
    (hs : 0 < s)
    (hoffdiag : ∀ t : Finset Feature, t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧
          η < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      Fintype.card Feature * (2 * k) <
        (let n := Fintype.card Feature
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2))) :
    False := by
  classical
  have hgraph :=
    forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
      (A := A) (B := B) (η := η) (s := s) hoffdiag
  exact
    false_of_linearRecovery_and_card_mul_two_mul_lt_turanBound_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (ε := ε) (s := s) (k := k)
      hrec hη hk hε_le hs hgraph havg

/--
Principal-submatrix form of the source-coarse Turán linear-recovery
contradiction.
-/
theorem false_of_linearRecovery_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_principalSubmatrix_exists_largeOffdiag
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {η ε : ℝ} {s k : ℕ}
    (hrec : ∀ z : Feature → ℝ, KSparse k z → InUnitBox z → SupErrorLt A B z ε)
    (hη : 0 ≤ η) (hk : 0 < k) (hε_le : ε ≤ (k : ℝ) * η)
    (hs : 1 < s)
    (hoffdiag : ∀ t : Finset Feature, t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧
          η < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      let n := Fintype.card Feature
      let r := s - 1
      (n : ℝ) * ((2 * k : ℕ) : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2) :
    False := by
  classical
  have hgraph :=
    forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
      (A := A) (B := B) (η := η) (s := s) hoffdiag
  exact
    false_of_linearRecovery_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (ε := ε) (s := s) (k := k)
      hrec hη hk hε_le hs hgraph havg

/--
Corrected threshold-separation contradiction.  A row with more than `2q`
large off-diagonal entries contradicts threshold separation once `q + 1 ≤ k`:
positive aligned interference violates a negative example, while negative
aligned interference violates the positive example formed by adding feature
`i`.  This is the sign-sensitive version of the source proof.
-/
theorem false_of_thresholdSeparates_and_two_mul_lt_largeOffdiagRow_card
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ}
    {η : ℝ} {k q : ℕ} {i : Feature}
    (hsep : ThresholdSeparates A B threshold k)
    (hdiag : inner (B i) (A i) = 1)
    (hη : 0 ≤ η) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * η)
    (hrow : 2 * q < (largeOffdiagRowFinset A B η i).card) :
    False := by
  classical
  have ht_nonneg : 0 ≤ threshold i :=
    threshold_nonneg_of_thresholdSeparates (A := A) (B := B)
      (threshold := threshold) (k := k) hsep i
  have ht_lt_one : threshold i < 1 := by
    have hk_one : 1 ≤ k := Nat.le_trans (by omega : 1 ≤ q + 1) hqk
    have hlt :=
      threshold_lt_diag_of_thresholdSeparates
        (A := A) (B := B) (threshold := threshold) (k := k)
        hk_one hsep i
    simpa [hdiag] using hlt
  rcases
    exists_finset_card_eq_abs_row_sum_gt_of_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (η := η) (k := q) (i := i)
      hη hq hrow with
    ⟨T, hTcard, hi_not, hsum_abs⟩
  have hT_sparse : KSparse k (finsetIndicator T : Feature → ℝ) := by
    exact kSparse_finsetIndicator_of_card_le (T := T)
      (by
        have hq_le : q ≤ k := Nat.le_trans (Nat.le_succ q) hqk
        simpa [hTcard] using hq_le)
  have hT_zeroone : InZeroOne (finsetIndicator T : Feature → ℝ) :=
    inZeroOne_finsetIndicator T
  have hprobe_T :
      linearProbe A B (finsetIndicator T) i =
        ∑ j ∈ T, inner (B i) (A j) :=
    linearProbe_finsetIndicator A B T i
  have hzi_T : finsetIndicator T i = 0 := finsetIndicator_apply_not_mem hi_not
  have hsum_abs_gt_one : 1 < |∑ j ∈ T, inner (B i) (A j)| :=
    lt_of_le_of_lt hunit hsum_abs
  by_cases hsum_nonneg : 0 ≤ ∑ j ∈ T, inner (B i) (A j)
  · have hsum_gt_one : 1 < ∑ j ∈ T, inner (B i) (A j) := by
      simpa [abs_of_nonneg hsum_nonneg] using hsum_abs_gt_one
    have hcross : threshold i < linearProbe A B (finsetIndicator T) i := by
      rw [hprobe_T]
      exact lt_trans ht_lt_one hsum_gt_one
    have hiff := hsep i (finsetIndicator T) hT_sparse hT_zeroone
    have hbad : finsetIndicator T i = 1 := hiff.mp hcross
    simpa [hzi_T] using hbad
  · have hsum_neg : ∑ j ∈ T, inner (B i) (A j) < 0 :=
      lt_of_not_ge hsum_nonneg
    have hsum_lt_neg_one : ∑ j ∈ T, inner (B i) (A j) < -1 := by
      have hneg : 1 < -∑ j ∈ T, inner (B i) (A j) := by
        simpa [abs_of_neg hsum_neg] using hsum_abs_gt_one
      linarith
    let U : Finset Feature := insert i T
    have hUcard : U.card ≤ k := by
      have hcard : U.card = q + 1 := by
        simp [U, hi_not, hTcard]
      simpa [hcard] using hqk
    have hU_sparse : KSparse k (finsetIndicator U : Feature → ℝ) :=
      kSparse_finsetIndicator_of_card_le (T := U) hUcard
    have hU_zeroone : InZeroOne (finsetIndicator U : Feature → ℝ) :=
      inZeroOne_finsetIndicator U
    have hzi_U : finsetIndicator U i = 1 := by simp [U]
    have hprobe_U :
        linearProbe A B (finsetIndicator U) i =
          1 + ∑ j ∈ T, inner (B i) (A j) := by
      rw [linearProbe_finsetIndicator]
      have hsum_insert :
          (∑ j ∈ U, inner (B i) (A j)) =
            inner (B i) (A i) + ∑ j ∈ T, inner (B i) (A j) := by
        simp [U, hi_not]
      rw [hsum_insert, hdiag]
    have hnot_cross : ¬ threshold i < linearProbe A B (finsetIndicator U) i := by
      rw [hprobe_U]
      have hlt_zero : 1 + ∑ j ∈ T, inner (B i) (A j) < 0 := by
        linarith
      exact not_lt.mpr (le_trans (le_of_lt hlt_zero) ht_nonneg)
    have hiff := hsep i (finsetIndicator U) hU_sparse hU_zeroone
    exact hnot_cross (hiff.mpr hzi_U)

/--
Threshold-separation contradiction after the Alon/rank obstruction and Turán
step have supplied many large off-diagonal entries.
-/
theorem false_of_thresholdSeparates_and_card_mul_two_mul_lt_turanBound_of_forall_principalSubmatrix_exists_largeOffdiag
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ}
    {η : ℝ} {s k q : ℕ}
    (hsep : ThresholdSeparates A B threshold k)
    (hdiag : ∀ i, inner (B i) (A i) = 1)
    (hη : 0 ≤ η) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * η)
    (hs : 0 < s)
    (hoffdiag : ∀ t : Finset Feature, t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧
          η < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      Fintype.card Feature * (2 * q) <
        (let n := Fintype.card Feature
         let r := s - 1
         n.choose 2 -
          ((n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2))) :
    False := by
  classical
  have hgraph :=
    forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
      (A := A) (B := B) (η := η) (s := s) hoffdiag
  rcases
    exists_largeOffdiagRow_card_gt_of_card_mul_lt_turanBound_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (s := s) (q := 2 * q)
      hs hgraph havg with
    ⟨i, hrow⟩
  exact
    false_of_thresholdSeparates_and_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (threshold := threshold) (η := η)
      (k := k) (q := q) (i := i)
      hsep (hdiag i) hη hq hqk hunit hrow

/--
Threshold-separation contradiction using the source-form coarse Turán average
estimate instead of the exact complement-Turán expression.
-/
theorem false_of_thresholdSeparates_and_real_card_mul_two_mul_lt_coarse_turan_of_forall_principalSubmatrix_exists_largeOffdiag
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {A B : Feature → Coord → ℝ} {threshold : Feature → ℝ}
    {η : ℝ} {s k q : ℕ}
    (hsep : ThresholdSeparates A B threshold k)
    (hdiag : ∀ i, inner (B i) (A i) = 1)
    (hη : 0 ≤ η) (hq : 0 < q) (hqk : q + 1 ≤ k)
    (hunit : 1 ≤ (q : ℝ) * η)
    (hs : 1 < s)
    (hoffdiag : ∀ t : Finset Feature, t.card = s →
      ∃ x y : {j // j ∈ t},
        x ≠ y ∧
          η < |((crossInnerMatrix A B).submatrix Subtype.val Subtype.val) x y|)
    (havg :
      let n := Fintype.card Feature
      let r := s - 1
      (n : ℝ) * ((2 * q : ℕ) : ℝ) <
        (n : ℝ) ^ 2 / (2 * (r : ℝ)) - (n : ℝ) / 2) :
    False := by
  classical
  have hgraph :=
    forall_finset_exists_largeOffdiagGraph_adj_of_forall_principalSubmatrix_exists_largeOffdiag
      (A := A) (B := B) (η := η) (s := s) hoffdiag
  rcases
    exists_largeOffdiagRow_card_gt_of_real_card_mul_lt_coarse_turan_of_forall_finset_exists_graph_adj
      (A := A) (B := B) (η := η) (s := s) (q := 2 * q)
      hs hgraph havg with
    ⟨i, hrow⟩
  exact
    false_of_thresholdSeparates_and_two_mul_lt_largeOffdiagRow_card
      (A := A) (B := B) (threshold := threshold) (η := η)
      (k := k) (q := q) (i := i)
      hsep (hdiag i) hη hq hqk hunit hrow

end LinearCompressedSensing
end Math
end AppliedModelingLib
