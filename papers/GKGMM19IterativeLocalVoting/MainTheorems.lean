import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Order.Filter.Extr
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Moments.SubGaussian
import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNormsDerivative
import AppliedModelingLib.Foundations.Optimization.ProjectedStochasticConvergence
import AppliedModelingLib.Foundations.Probability.BoundedDensity
import AppliedModelingLib.Foundations.Probability.Weighted

/-!
# Paper-Facing Model: Iterative Local Voting in Continuous Spaces

This file starts the Lean vocabulary for Garg, Kamble, Goel, Marn, and
Munagala (JAIR 2019), "Iterative Local Voting for Collective Decision-making in
Continuous Spaces."

The current layer is intentionally abstract about finite-dimensional Euclidean
analysis, stochastic processes, and measure-theoretic convergence.  It exposes
the paper's source predicates and theorem-shaped statements without pretending
that the stochastic approximation proofs have already been mechanized.

## Main declarations

- `SourceNorm`: the paper's L1, L2, Linf, and finite Lp norm parameters.
- `VoterResponseModel`: Model A and Model B from the paper.
- `ILVEnvironment`: abstract data for one ILV instance.
- `ConditionsC123`: source assumptions C1, C2, and C3.
- `IsLpNormedUtilities`, `IsWeightedEuclideanUtilitiesWith`,
  `IsDecomposableUtilitiesWith`: source utility classes.
- `theorem1Statement`, `theorem2Statement`, `proposition1Statement`,
  `proposition2Statement`, `theorem3Statement`: paper-facing named-result
  formulas.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace GKGMM19IterativeLocalVoting

/-- Norm parameter appearing in the paper: L1, L2, Linf, or a finite real Lp. -/
inductive SourceNorm where
  | l1
  | l2
  | linfty
  | lp (p : ℝ)

/--
Concrete finite-coordinate interpretation of the paper's norm parameter.  This
is the entry point for replacing the abstract `normDistance` field with actual
finite-dimensional `L1`, `L2`, `L∞`, and finite-`Lp` formulas.
-/
noncomputable def finiteCoordinateNorm
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (p : SourceNorm) (x : Coord → ℝ) : ℝ :=
  match p with
  | SourceNorm.l1 => AppliedModelingLib.FiniteDimensionalNorms.l1 x
  | SourceNorm.l2 => AppliedModelingLib.FiniteDimensionalNorms.l2 x
  | SourceNorm.linfty => AppliedModelingLib.FiniteDimensionalNorms.linf x
  | SourceNorm.lp p => AppliedModelingLib.FiniteDimensionalNorms.lp p x

/-- Concrete finite-coordinate distance induced by `finiteCoordinateNorm`. -/
noncomputable def finiteCoordinateDistance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (p : SourceNorm) (x y : Coord → ℝ) : ℝ :=
  finiteCoordinateNorm p (fun m => x m - y m)

theorem finiteCoordinateNorm_l1
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.l1 x =
      AppliedModelingLib.FiniteDimensionalNorms.l1 x := rfl

theorem finiteCoordinateNorm_l2
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.l2 x =
      AppliedModelingLib.FiniteDimensionalNorms.l2 x := rfl

theorem finiteCoordinateNorm_linf
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.linfty x =
      AppliedModelingLib.FiniteDimensionalNorms.linf x := rfl

theorem finiteCoordinateNorm_lp
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (p : ℝ) (x : Coord → ℝ) :
    finiteCoordinateNorm (SourceNorm.lp p) x =
      AppliedModelingLib.FiniteDimensionalNorms.lp p x := rfl

theorem finiteCoordinateDistance_l1
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l1 x y =
      AppliedModelingLib.FiniteDimensionalNorms.l1 (fun m => x m - y m) := rfl

theorem finiteCoordinateDistance_l2
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l2 x y =
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun m => x m - y m) := rfl

theorem finiteDimensionalNorms_l2_eq_lp_two
    {Coord : Type*} [Fintype Coord] (x : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2 x =
      AppliedModelingLib.FiniteDimensionalNorms.lp 2 x := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l2,
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq,
    AppliedModelingLib.FiniteDimensionalNorms.lp,
    AppliedModelingLib.FiniteDimensionalNorms.lpPower]
  have hsum :
      (∑ i : Coord, |x i| ^ (2 : ℝ)) =
        ∑ i : Coord, x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Real.rpow_two, sq_abs]
  rw [hsum, Real.sqrt_eq_rpow]

theorem finiteCoordinateDistance_linf
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.linfty x y =
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun m => x m - y m) := rfl

theorem finiteCoordinateDistance_lp
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (p : ℝ) (x y : Coord → ℝ) :
    finiteCoordinateDistance (SourceNorm.lp p) x y =
      AppliedModelingLib.FiniteDimensionalNorms.lp p (fun m => x m - y m) := rfl

theorem finiteCoordinateDistance_l1_self
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l1 x x = 0 := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL1_sub_self x

theorem finiteCoordinateDistance_l2_self
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l2 x x = 0 := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_sub_self x

theorem finiteCoordinateDistance_linf_self
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.linfty x x = 0 := by
  exact AppliedModelingLib.FiniteDimensionalNorms.linf_sub_self x

theorem finiteCoordinateDistance_lp_self_of_pos
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 0 < p) (x : Coord → ℝ) :
    finiteCoordinateDistance (SourceNorm.lp p) x x = 0 := by
  exact AppliedModelingLib.FiniteDimensionalNorms.lp_sub_self_of_pos hp x

theorem finiteCoordinateDistance_l1_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    0 ≤ finiteCoordinateDistance SourceNorm.l1 x y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL1_nonneg (fun m => x m - y m)

theorem finiteCoordinateDistance_l2_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    0 ≤ finiteCoordinateDistance SourceNorm.l2 x y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg (fun m => x m - y m)

theorem finiteCoordinateNorm_l2_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    0 ≤ finiteCoordinateNorm SourceNorm.l2 x := by
  simpa [finiteCoordinateDistance] using
    (finiteCoordinateDistance_l2_nonneg x (fun _ : Coord => 0))

/-- A single coordinate displacement is bounded by finite-coordinate `L2` distance. -/
theorem finiteCoordinateDistance_l2_coord_abs_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) (i : Coord) :
    |x i - y i| ≤ finiteCoordinateDistance SourceNorm.l2 x y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_coord_abs_le
    (fun m => x m - y m) i

/-- A single coordinate displacement is bounded by finite-coordinate `L∞` distance. -/
theorem finiteCoordinateDistance_linf_coord_abs_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) (i : Coord) :
    |x i - y i| ≤ finiteCoordinateDistance SourceNorm.linfty x y := by
  rw [finiteCoordinateDistance_linf]
  exact Finset.le_sup'
    (s := (Finset.univ : Finset Coord))
    (f := fun j => |x j - y j|)
    (Finset.mem_univ i)

/-- A single coordinate displacement is bounded by finite-coordinate `L1` distance. -/
theorem finiteCoordinateDistance_l1_coord_abs_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) (i : Coord) :
    |x i - y i| ≤ finiteCoordinateDistance SourceNorm.l1 x y := by
  rw [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
  exact Finset.single_le_sum
    (fun j _hj => abs_nonneg (x j - y j))
    (Finset.mem_univ i)

/-- Finite-coordinate `L∞` distance is bounded by a uniform coordinate bound. -/
theorem finiteCoordinateDistance_linf_le_of_forall_coord_abs_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x y : Coord → ℝ} {r : ℝ}
    (h : ∀ i, |x i - y i| ≤ r) :
    finiteCoordinateDistance SourceNorm.linfty x y ≤ r := by
  rw [finiteCoordinateDistance_linf, AppliedModelingLib.FiniteDimensionalNorms.linf]
  exact Finset.sup'_le
    (s := (Finset.univ : Finset Coord))
    (H := Finset.univ_nonempty)
    (f := fun i => |x i - y i|)
    (a := r)
    (fun i _hi => h i)

theorem finiteCoordinateNorm_l2_smul
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : ℝ) (x : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.l2 (fun i => a * x i) =
      |a| * finiteCoordinateNorm SourceNorm.l2 x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_smul a x

theorem finiteCoordinateDistance_linf_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    0 ≤ finiteCoordinateDistance SourceNorm.linfty x y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.linf_nonneg (fun m => x m - y m)

theorem finiteCoordinateDistance_lp_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (p : ℝ) (x y : Coord → ℝ) :
    0 ≤ finiteCoordinateDistance (SourceNorm.lp p) x y := by
  exact AppliedModelingLib.FiniteDimensionalNorms.lp_nonneg p (fun m => x m - y m)

theorem finiteCoordinateNorm_l1_pos_of_exists_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x : Coord → ℝ} (hx : ∃ m, x m ≠ 0) :
    0 < finiteCoordinateNorm SourceNorm.l1 x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL1_pos_of_exists_ne_zero hx

theorem finiteCoordinateNorm_l2_pos_of_exists_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x : Coord → ℝ} (hx : ∃ m, x m ≠ 0) :
    0 < finiteCoordinateNorm SourceNorm.l2 x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero hx

theorem finiteCoordinateNorm_linf_pos_of_exists_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x : Coord → ℝ} (hx : ∃ m, x m ≠ 0) :
    0 < finiteCoordinateNorm SourceNorm.linfty x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.linf_pos_of_exists_ne_zero hx

theorem finiteCoordinateNorm_lp_pos_of_exists_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 0 < p) {x : Coord → ℝ} (hx : ∃ m, x m ≠ 0) :
    0 < finiteCoordinateNorm (SourceNorm.lp p) x := by
  exact AppliedModelingLib.FiniteDimensionalNorms.lp_pos_of_exists_ne_zero hp hx

theorem finiteCoordinateDistance_l1_pos_of_exists_ne
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x y : Coord → ℝ} (hxy : ∃ m, x m ≠ y m) :
    0 < finiteCoordinateDistance SourceNorm.l1 x y := by
  rcases hxy with ⟨m, hm⟩
  exact AppliedModelingLib.FiniteDimensionalNorms.normL1_pos_of_exists_ne_zero
    ⟨m, sub_ne_zero.mpr hm⟩

theorem finiteCoordinateDistance_l2_pos_of_exists_ne
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x y : Coord → ℝ} (hxy : ∃ m, x m ≠ y m) :
    0 < finiteCoordinateDistance SourceNorm.l2 x y := by
  rcases hxy with ⟨m, hm⟩
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero
    ⟨m, sub_ne_zero.mpr hm⟩

theorem finiteCoordinateDistance_l2_eq_zero_iff
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    finiteCoordinateDistance SourceNorm.l2 x y = 0 ↔ x = y := by
  constructor
  · intro hzero
    ext i
    by_contra hne
    have hpos :
        0 < finiteCoordinateDistance SourceNorm.l2 x y :=
      finiteCoordinateDistance_l2_pos_of_exists_ne ⟨i, hne⟩
    linarith
  · intro hxy
    rw [hxy]
    exact finiteCoordinateDistance_l2_self y

theorem finiteCoordinateDistance_linf_pos_of_exists_ne
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x y : Coord → ℝ} (hxy : ∃ m, x m ≠ y m) :
    0 < finiteCoordinateDistance SourceNorm.linfty x y := by
  rcases hxy with ⟨m, hm⟩
  exact AppliedModelingLib.FiniteDimensionalNorms.linf_pos_of_exists_ne_zero
    ⟨m, sub_ne_zero.mpr hm⟩

theorem finiteCoordinateDistance_lp_pos_of_exists_ne
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 0 < p) {x y : Coord → ℝ}
    (hxy : ∃ m, x m ≠ y m) :
    0 < finiteCoordinateDistance (SourceNorm.lp p) x y := by
  rcases hxy with ⟨m, hm⟩
  exact AppliedModelingLib.FiniteDimensionalNorms.lp_pos_of_exists_ne_zero hp
    ⟨m, sub_ne_zero.mpr hm⟩

/-- Voter behavior model in the source paper. -/
inductive VoterResponseModel where
  | modelA
  | modelB

/--
The three dual-norm cases in Theorem 1:
`(p,q) = (2,2)`, `(1,inf)`, or `(inf,1)`.
-/
def Theorem1NormPair (p q : SourceNorm) : Prop :=
  (p = SourceNorm.l2 ∧ q = SourceNorm.l2) ∨
    (p = SourceNorm.l1 ∧ q = SourceNorm.linfty) ∨
      (p = SourceNorm.linfty ∧ q = SourceNorm.l1)

theorem theorem1NormPair_l2_l2 :
    Theorem1NormPair SourceNorm.l2 SourceNorm.l2 := by
  exact Or.inl ⟨rfl, rfl⟩

theorem theorem1NormPair_l1_linf :
    Theorem1NormPair SourceNorm.l1 SourceNorm.linfty := by
  exact Or.inr (Or.inl ⟨rfl, rfl⟩)

theorem theorem1NormPair_linf_l1 :
    Theorem1NormPair SourceNorm.linfty SourceNorm.l1 := by
  exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Finite real Holder-dual condition used in Theorem 2. -/
def HolderDualFinite (p q : ℝ) : Prop :=
  0 < p ∧ 0 < q ∧ 1 / p + 1 / q = 1

namespace HolderDualFinite

theorem to_holderConjugate {p q : ℝ} (h : HolderDualFinite p q) :
    Real.HolderConjugate p q := by
  refine ⟨?_, h.1, h.2.1⟩
  simpa [one_div] using h.2.2

theorem of_holderConjugate {p q : ℝ} (h : Real.HolderConjugate p q) :
    HolderDualFinite p q := by
  exact ⟨h.left_pos, h.right_pos, by simpa [one_div] using h.inv_add_inv_eq_one⟩

theorem symm {p q : ℝ} (h : HolderDualFinite p q) :
    HolderDualFinite q p := by
  exact ⟨h.2.1, h.1, by simpa [add_comm] using h.2.2⟩

theorem two_two : HolderDualFinite 2 2 := by
  norm_num [HolderDualFinite]

theorem one_lt_left {p q : ℝ} (h : HolderDualFinite p q) : 1 < p := by
  rcases h with ⟨hp, hq, hsum⟩
  have hqinv_pos : 0 < 1 / q := one_div_pos.mpr hq
  have hp_inv_lt_one : 1 / p < 1 := by linarith
  have hmul : (1 / p) * p < 1 * p :=
    mul_lt_mul_of_pos_right hp_inv_lt_one hp
  field_simp [hp.ne'] at hmul
  linarith

theorem one_lt_right {p q : ℝ} (h : HolderDualFinite p q) : 1 < q := by
  rcases h with ⟨hp, hq, hsum⟩
  have hpinv_pos : 0 < 1 / p := one_div_pos.mpr hp
  have hq_inv_lt_one : 1 / q < 1 := by linarith
  have hmul : (1 / q) * q < 1 * q :=
    mul_lt_mul_of_pos_right hq_inv_lt_one hq
  field_simp [hq.ne'] at hmul
  linarith

theorem sub_one_mul_right_eq_left {p q : ℝ} (h : HolderDualFinite p q) :
    (p - 1) * q = p := by
  rcases h with ⟨hp, hq, hsum⟩
  field_simp [hp.ne', hq.ne'] at hsum ⊢
  nlinarith

theorem left_mul_sub_one_eq_right {p q : ℝ} (h : HolderDualFinite p q) :
    p * (q - 1) = q := by
  rcases h with ⟨hp, hq, hsum⟩
  field_simp [hp.ne', hq.ne'] at hsum ⊢
  nlinarith

end HolderDualFinite

/--
Algebraic coordinate vector appearing in the proof of Lemma 3.  The auxiliary
factor `absDeriv i` stands for the derivative of `|x_i|`; the theorem below only
uses that its absolute value is `1` away from the coordinate equality locus.
-/
noncomputable def lpGradientCandidate
    {Coord : Type*} [Fintype Coord]
    (p : ℝ) (x absDeriv : Coord → ℝ) : Coord → ℝ :=
  fun i => (|x i| ^ (p - 1) * absDeriv i) /
    (AppliedModelingLib.FiniteDimensionalNorms.lpPower p x) ^ ((p - 1) / p)

/--
Lemma 3 algebra core: the finite `Lq` power sum of the displayed
Holder-dual gradient candidate is `1`.

This is intentionally one step short of a differentiability theorem: `absDeriv`
is an explicit coordinate factor satisfying `|absDeriv i| = 1`, which is the
only property used in the source calculation after excluding coordinate
equalities.
-/
theorem lpGradientCandidate_lq_power_sum_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x absDeriv : Coord → ℝ}
    (hx : ∀ i, x i ≠ 0) (habsDeriv : ∀ i, |absDeriv i| = 1) :
    AppliedModelingLib.FiniteDimensionalNorms.lpPower q
      (lpGradientCandidate p x absDeriv) = 1 := by
  have hp : 0 < p := hdual.1
  have hp_ne : p ≠ 0 := hp.ne'
  have hmul : (p - 1) * q = p :=
    HolderDualFinite.sub_one_mul_right_eq_left hdual
  let S : ℝ := AppliedModelingLib.FiniteDimensionalNorms.lpPower p x
  have hSpos : 0 < S := by
    exact AppliedModelingLib.FiniteDimensionalNorms.lpPower_pos_of_exists_ne_zero hp
      ⟨Classical.arbitrary Coord, hx (Classical.arbitrary Coord)⟩
  have hSnonneg : 0 ≤ S := hSpos.le
  have hexp : ((p - 1) / p) * q = 1 := by
    field_simp [hp_ne]
    nlinarith [hmul]
  rw [AppliedModelingLib.FiniteDimensionalNorms.lpPower]
  calc
    (∑ i : Coord, |lpGradientCandidate p x absDeriv i| ^ q)
        = ∑ i : Coord, |x i| ^ p / S := by
          apply Finset.sum_congr rfl
          intro i _hi
          have hxi_nonneg : 0 ≤ |x i| := abs_nonneg (x i)
          have hxi_pow_nonneg : 0 ≤ |x i| ^ (p - 1) :=
            Real.rpow_nonneg hxi_nonneg (p - 1)
          have hden_nonneg : 0 ≤ S ^ ((p - 1) / p) :=
            Real.rpow_nonneg hSnonneg ((p - 1) / p)
          have habs :
              |lpGradientCandidate p x absDeriv i| =
                |x i| ^ (p - 1) / S ^ ((p - 1) / p) := by
            rw [lpGradientCandidate, abs_div, abs_mul,
              abs_of_nonneg hxi_pow_nonneg, habsDeriv i,
              mul_one, abs_of_nonneg hden_nonneg]
          calc
            |lpGradientCandidate p x absDeriv i| ^ q
                = (|x i| ^ (p - 1) / S ^ ((p - 1) / p)) ^ q := by
                  rw [habs]
            _ = (|x i| ^ (p - 1)) ^ q / (S ^ ((p - 1) / p)) ^ q := by
                  rw [Real.div_rpow hxi_pow_nonneg hden_nonneg q]
            _ = |x i| ^ ((p - 1) * q) / S ^ (((p - 1) / p) * q) := by
                  rw [← Real.rpow_mul hxi_nonneg (p - 1) q,
                    ← Real.rpow_mul hSnonneg ((p - 1) / p) q]
            _ = |x i| ^ p / S := by
                  rw [hmul, hexp, Real.rpow_one]
    _ = (∑ i : Coord, |x i| ^ p) / S := by
          rw [Finset.sum_div]
    _ = S / S := by
          rfl
    _ = 1 := div_self hSpos.ne'

/--
Lemma 3 algebra core in source norm form: the finite-coordinate `Lq` norm of
the displayed Holder-dual gradient candidate is `1`.
-/
theorem lpGradientCandidate_lq_norm_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x absDeriv : Coord → ℝ}
    (hx : ∀ i, x i ≠ 0) (habsDeriv : ∀ i, |absDeriv i| = 1) :
    finiteCoordinateNorm (SourceNorm.lp q)
      (lpGradientCandidate p x absDeriv) = 1 := by
  rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.lp,
    lpGradientCandidate_lq_power_sum_eq_one hdual hx habsDeriv]
  exact Real.one_rpow (1 / q)

/--
Source-specialized candidate for the gradient of `d ↦ ||d||_p` away from zero
coordinates.  The factor `d i / |d i|` is the derivative of `|d i|` when
`d i ≠ 0`; the denominator is written as the equivalent power-sum expression
`(sum_i |d_i|^p)^((p-1)/p)` to keep the finite-sum algebra direct.
-/
noncomputable def lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord]
    (p : ℝ) (d : Coord → ℝ) : Coord → ℝ :=
  lpGradientCandidate p d (fun i => d i / |d i|)

/--
The internal power-sum denominator used by `lpCostGradientCandidate` is the
paper's displayed denominator `||d||_p^(p-1)` for positive `p`.
-/
theorem lpCostGradientCandidate_eq_source_formula
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 0 < p) (d : Coord → ℝ) :
    lpCostGradientCandidate p d =
      fun i => (|d i| ^ (p - 1) * (d i / |d i|)) /
        (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
  let S : ℝ := AppliedModelingLib.FiniteDimensionalNorms.lpPower p d
  have hSnonneg : 0 ≤ S :=
    AppliedModelingLib.FiniteDimensionalNorms.lpPower_nonneg p d
  have hden :
      S ^ ((p - 1) / p) =
        (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
    rw [AppliedModelingLib.FiniteDimensionalNorms.lp]
    change S ^ ((p - 1) / p) = (S ^ (1 / p)) ^ (p - 1)
    rw [← Real.rpow_mul hSnonneg (1 / p) (p - 1)]
    congr 1
    field_simp [hp.ne']
  funext i
  rw [lpCostGradientCandidate, lpGradientCandidate, hden]

/--
Away from zero, the source numerator
`|d_i|^(p-1) * (d_i / |d_i|)` is the same coefficient shape as the derivative
of the finite power sum, up to the outer scalar `p`.
-/
theorem lpCostGradientCandidate_numerator_eq_lpPower_deriv_coeff
    {p z : ℝ} (hz : z ≠ 0) :
    |z| ^ (p - 1) * (z / |z|) = |z| ^ (p - 2) * z := by
  have hpos : 0 < |z| := abs_pos.mpr hz
  have hpow : |z| ^ (p - 1) / |z| = |z| ^ (p - 2) := by
    calc
      |z| ^ (p - 1) / |z| = |z| ^ (p - 1) / |z| ^ 1 := by
        rw [Real.rpow_one]
      _ = |z| ^ ((p - 1) - 1) := (Real.rpow_sub hpos (p - 1) 1).symm
      _ = |z| ^ (p - 2) := by ring_nf
  calc
    |z| ^ (p - 1) * (z / |z|)
        = (|z| ^ (p - 1) / |z|) * z := by ring
    _ = |z| ^ (p - 2) * z := by rw [hpow]

/--
Source candidate gradient rewritten with the coefficient shape coming from the
proved derivative of the finite `Lp` power sum.
-/
theorem lpCostGradientCandidate_eq_deriv_coeff_formula
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 0 < p) {d : Coord → ℝ} (hd : ∀ i, d i ≠ 0) :
    lpCostGradientCandidate p d =
      fun i => (|d i| ^ (p - 2) * d i) /
        (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
  funext i
  have hsrc := congrFun (lpCostGradientCandidate_eq_source_formula hp d) i
  rw [hsrc, lpCostGradientCandidate_numerator_eq_lpPower_deriv_coeff (hd i)]

/--
Reusable derivative fact used by the Lemma 3 path: the finite `Lp` power sum has
the expected coordinate derivative when `1 < p`.
-/
theorem hasFDerivAt_finiteCoordinate_lpPower
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 1 < p) (d : Coord → ℝ) :
    HasFDerivAt
      (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lpPower p y)
      (AppliedModelingLib.FiniteDimensionalNorms.lpPowerFDeriv p d) d := by
  exact AppliedModelingLib.FiniteDimensionalNorms.hasFDerivAt_lpPower hp d

/--
The derivative linear map of the finite-coordinate `Lp` norm is represented by
the source candidate-gradient vector away from zero coordinates.
-/
theorem lpFDeriv_eq_coordinateLinearFunctional_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {d : Coord → ℝ} (hd : ∀ i, d i ≠ 0) :
    AppliedModelingLib.FiniteDimensionalNorms.lpFDeriv p d =
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p d) := by
  ext h
  simp [AppliedModelingLib.FiniteDimensionalNorms.lpFDeriv,
    AppliedModelingLib.FiniteDimensionalNorms.lpPowerFDeriv,
    AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hSpos : 0 < AppliedModelingLib.FiniteDimensionalNorms.lpPower p d :=
    AppliedModelingLib.FiniteDimensionalNorms.lpPower_pos_of_exists_ne_zero hp_pos
      ⟨i, hd i⟩
  have hcoeff : (p⁻¹ *
        AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ (p⁻¹ - 1)) *
      (p * |d i| ^ (p - 2) * d i) =
        (|d i| ^ (p - 2) * d i) /
          (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
    have hp_ne : p ≠ 0 := ne_of_gt hp_pos
    have hden_pos :
        0 < AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ ((p - 1) / p) :=
      Real.rpow_pos_of_pos hSpos _
    have hpow :
        AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ (p⁻¹ - 1) =
          (AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ ((p - 1) / p))⁻¹ := by
      have hexp : p⁻¹ - 1 = -((p - 1) / p) := by
        field_simp [hp_ne]
        ring
      rw [hexp, Real.rpow_neg hSpos.le]
    have hden :
        AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ ((p - 1) / p) =
          (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1) := by
      let S : ℝ := AppliedModelingLib.FiniteDimensionalNorms.lpPower p d
      have hSnonneg : 0 ≤ S := hSpos.le
      rw [AppliedModelingLib.FiniteDimensionalNorms.lp]
      change S ^ ((p - 1) / p) = (S ^ (1 / p)) ^ (p - 1)
      rw [← Real.rpow_mul hSnonneg (1 / p) (p - 1)]
      congr 1
      field_simp [hp_ne]
    rw [← hden, hpow]
    field_simp [hp_ne, hden_pos.ne']
  have hvec :=
    congrFun (lpCostGradientCandidate_eq_deriv_coeff_formula hp_pos hd) i
  rw [hvec]
  calc
    (p⁻¹ * AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ (p⁻¹ - 1)) *
        (p * |d i| ^ (p - 2) * d i * h i)
        = ((p⁻¹ * AppliedModelingLib.FiniteDimensionalNorms.lpPower p d ^ (p⁻¹ - 1)) *
            (p * |d i| ^ (p - 2) * d i)) * h i := by ring
    _ = ((|d i| ^ (p - 2) * d i) /
          (AppliedModelingLib.FiniteDimensionalNorms.lp p d) ^ (p - 1)) * h i := by
          rw [hcoeff]

/--
Derivative attachment for Lemma 3: under `1 < p` and away from zero
coordinates, the source candidate-gradient vector represents the Fréchet
derivative of the finite-coordinate `Lp` norm.
-/
theorem hasFDerivAt_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {d : Coord → ℝ} (hd : ∀ i, d i ≠ 0) :
    HasFDerivAt
      (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
      (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (lpCostGradientCandidate p d)) d := by
  rw [← lpFDeriv_eq_coordinateLinearFunctional_lpCostGradientCandidate hp hd]
  exact AppliedModelingLib.FiniteDimensionalNorms.hasFDerivAt_lp hp
    ⟨Classical.arbitrary Coord, hd (Classical.arbitrary Coord)⟩

/--
Utility-gradient attachment for Definition 1: away from coordinate equalities,
the derivative of `y ↦ -||y - ideal||_p` is represented by the negative of the
finite-coordinate cost-gradient candidate.
-/
theorem hasFDerivAt_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    HasFDerivAt
      (fun y : Coord → ℝ =>
        -AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i)) x := by
  have hd : ∀ i, (fun j => x j - ideal j) i ≠ 0 := by
    intro i
    exact sub_ne_zero.mpr (hcoord i)
  have hbase :
      HasFDerivAt
        (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (fun i => x i - ideal i) :=
    hasFDerivAt_lpCostGradientCandidate hp hd
  have hcost :
      HasFDerivAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - ideal i))
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i))) x := by
    simpa [Function.comp_def] using
      (hasFDerivAt_comp_sub (𝕜 := ℝ)
        (f := fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
        (f' := AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (x := x) ideal).mpr hbase
  simpa [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional_neg] using
    hcost.neg

/--
Lemma 3 algebra core for the source candidate gradient: away from coordinate
equalities, the displayed finite Holder-dual gradient candidate has `Lq` norm
equal to `1`.
-/
theorem lpCostGradientCandidate_lq_norm_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {d : Coord → ℝ} (hd : ∀ i, d i ≠ 0) :
    finiteCoordinateNorm (SourceNorm.lp q)
      (lpCostGradientCandidate p d) = 1 := by
  exact lpGradientCandidate_lq_norm_eq_one hdual hd (fun i => by
    have hpos : 0 < |d i| := abs_pos.mpr (hd i)
    rw [abs_div, abs_abs, div_self hpos.ne'])

/--
Lemma 3 paper-coordinate wrapper: for `d = x - ideal`, if every coordinate is
away from the ideal coordinate, the source gradient candidate has `Lq` norm `1`.
-/
theorem lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    finiteCoordinateNorm (SourceNorm.lp q)
      (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1 := by
  exact lpCostGradientCandidate_lq_norm_eq_one hdual
    (fun i => sub_ne_zero.mpr (hcoord i))

/-- Coordinate hyperplane where an ideal point equals the current point in one coordinate. -/
def coordinateEqualityHyperplane
    {Coord : Type*} (x : Coord → ℝ) (i : Coord) : Set (Coord → ℝ) :=
  {ideal | x i = ideal i}

/-- Bad event excluded in Appendix C.4 Lemma 3: some coordinate equals the ideal. -/
def coordinateEqualityBadEvent
    {Coord : Type*} (x : Coord → ℝ) : Set (Coord → ℝ) :=
  {ideal | ∃ i, x i = ideal i}

theorem coordinateEqualityBadEvent_eq_biUnion
    {Coord : Type*} [Fintype Coord] (x : Coord → ℝ) :
    coordinateEqualityBadEvent x =
      ⋃ i ∈ (Finset.univ : Finset Coord), coordinateEqualityHyperplane x i := by
  ext ideal
  simp [coordinateEqualityBadEvent, coordinateEqualityHyperplane]

/--
Bounded-density reduction for Lemma 3's coordinate-equality bad event: if each
coordinate hyperplane is null for the base measure, then the finite union of
coordinate equalities is null for any bounded-density measure.
-/
theorem boundedDensity_coordinateEqualityBadEvent_null
    {Coord : Type*} [Fintype Coord] [MeasurableSpace (Coord → ℝ)]
    {ν μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : AppliedModelingLib.Probability.HasBoundedDensity ν μ C)
    (x : Coord → ℝ)
    (hcoord : ∀ i, ν (coordinateEqualityHyperplane x i) = 0) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  have hbase : ν (coordinateEqualityBadEvent x) = 0 := by
    have hle :
        ν (coordinateEqualityBadEvent x) ≤
          ∑ i ∈ (Finset.univ : Finset Coord),
            ν (coordinateEqualityHyperplane x i) := by
      rw [coordinateEqualityBadEvent_eq_biUnion x]
      exact measure_biUnion_finset_le (Finset.univ : Finset Coord)
        (coordinateEqualityHyperplane x)
    have hsum :
        (∑ i ∈ (Finset.univ : Finset Coord),
            ν (coordinateEqualityHyperplane x i)) = 0 := by
      simp [hcoord]
    exact le_antisymm (by simpa [hsum] using hle) (zero_le _)
  exact hbd.measure_eq_zero_of_base_null hbase

theorem productMeasure_coordinateEqualityHyperplane_null
    {Coord : Type*} [Fintype Coord] (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    (x : Coord → ℝ) (i : Coord) :
    Measure.pi (fun _ : Coord => ρ) (coordinateEqualityHyperplane x i) = 0 := by
  simpa [coordinateEqualityHyperplane, eq_comm] using
    Measure.pi_hyperplane (fun _ : Coord => ρ) i (x i)

/--
Concrete finite-dimensional product-measure version of the coordinate-equality
bad-event lemma: a bounded-density ideal distribution with respect to a product
of atomless one-dimensional marginals assigns probability zero to the event that
some coordinate of the ideal equals the current point.
-/
theorem productMeasure_boundedDensity_coordinateEqualityBadEvent_null
    {Coord : Type*} [Fintype Coord] (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact boundedDensity_coordinateEqualityBadEvent_null hbd x
    (productMeasure_coordinateEqualityHyperplane_null ρ x)

/--
Every coordinate hyperplane is Lebesgue-null in a finite real product.  This
is the source-faithful base-measure fact needed for C3; it does not impose
independence of the coordinates of an ideal point.
-/
theorem volume_coordinateEqualityHyperplane_null
    {Coord : Type*} [Fintype Coord]
    (x : Coord → ℝ) (i : Coord) :
    (volume : Measure (Coord → ℝ)) (coordinateEqualityHyperplane x i) = 0 := by
  simpa [MeasureTheory.volume_pi, coordinateEqualityHyperplane, eq_comm] using
    Measure.pi_hyperplane (fun _ : Coord => (volume : Measure ℝ)) i (x i)

/--
A bounded density with respect to finite-dimensional Lebesgue measure assigns
probability zero to a coordinate equality.  This uses only the C3 density
condition stated in the paper, not a product-density strengthening.
-/
theorem volume_boundedDensity_coordinateEqualityBadEvent_null
    {Coord : Type*} [Fintype Coord]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : AppliedModelingLib.Probability.HasBoundedDensity (volume : Measure (Coord → ℝ)) μ C)
    (x : Coord → ℝ) :
    μ (coordinateEqualityBadEvent x) = 0 := by
  exact boundedDensity_coordinateEqualityBadEvent_null hbd x
    (volume_coordinateEqualityHyperplane_null x)

/-- Outside the coordinate-equality bad event, every coordinate differs. -/
theorem notMem_coordinateEqualityBadEvent_iff
    {Coord : Type*} (x ideal : Coord → ℝ) :
    ideal ∉ coordinateEqualityBadEvent x ↔ ∀ i, x i ≠ ideal i := by
  simp [coordinateEqualityBadEvent]

/--
Deterministic sequence form of the bad-event exclusion used in Appendix C.4:
if every sampled ideal point avoids the coordinate-equality bad event for the
current iterate, then the Lemma 3 noncollision hypothesis holds at every step.
-/
theorem coordinate_noncollision_of_forall_notMem_coordinateEqualityBadEvent
    {Coord : Type*} (trajectory ideal : ℕ → Coord → ℝ)
    (havoid :
      ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t)) :
    ∀ t i, trajectory t i ≠ ideal t i := by
  intro t
  exact (notMem_coordinateEqualityBadEvent_iff (trajectory t) (ideal t)).mp
    (havoid t)

/--
The slab event relevant to the source's `L1/L∞` Model A proof: at least one
coordinate of the ideal lies strictly closer than the query radius.  Outside
this event, the exact raw maximizer is the coordinate-sign response.
-/
def l1LinfSlabBadEvent
    {Coord : Type*} (center : Coord → ℝ) (radius : ℝ) : Set (Coord → ℝ) :=
  {ideal | ∃ i, |center i - ideal i| < radius}

/-- Avoiding the `L1/L∞` slab event is exactly the coordinatewise good condition. -/
theorem notMem_l1LinfSlabBadEvent_iff
    {Coord : Type*} (center ideal : Coord → ℝ) (radius : ℝ) :
    ideal ∉ l1LinfSlabBadEvent center radius ↔
      ∀ i, radius ≤ |center i - ideal i| := by
  simp [l1LinfSlabBadEvent]

/-- The coordinate-slab exceptional event is Borel measurable. -/
theorem measurableSet_l1LinfSlabBadEvent
    {Coord : Type*} [Fintype Coord]
    (center : Coord → ℝ) (radius : ℝ) :
    MeasurableSet (l1LinfSlabBadEvent center radius) := by
  classical
  change MeasurableSet {ideal : Coord → ℝ | ∃ i, |center i - ideal i| < radius}
  rw [show {ideal : Coord → ℝ | ∃ i, |center i - ideal i| < radius} =
      ⋃ i : Coord, {ideal : Coord → ℝ | |center i - ideal i| < radius} by
    ext ideal
    simp]
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_Iio.preimage
    ((measurable_const.sub (measurable_pi_apply i)).abs)

/-- The strict `L1/L∞` slab event is contained in the closed coordinate slabs used by C3. -/
theorem l1LinfSlabBadEvent_subset_coordinateSlabs
    {Coord : Type*} (center : Coord → ℝ) (radius : ℝ) :
    l1LinfSlabBadEvent center radius ⊆
      {ideal : Coord → ℝ |
        ∃ i, ideal i ∈ Set.Icc (center i - radius) (center i + radius)} := by
  intro ideal hideal
  rcases hideal with ⟨i, hi⟩
  have hi' : |ideal i - center i| < radius := by
    simpa [abs_sub_comm] using hi
  have hbounds := abs_lt.mp hi'
  refine ⟨i, ?_⟩
  constructor <;> linarith

/--
Finite-coordinate slab bad region used in Lemma 2's `(p = 1, q = ∞)` case:
inside a bounding box, some ideal coordinate is within `radius` of the current
iterate's coordinate.
-/
def coordinateSlabBadRegion
    {Coord : Type*} [Fintype Coord]
    (boxLo boxHi center : Coord → ℝ) (radius : ℝ) : Set (Coord → ℝ) :=
  ⋃ i ∈ (Finset.univ : Finset Coord),
    {ideal : Coord → ℝ |
      ideal ∈ Set.Icc boxLo boxHi ∧
        ideal i ∈ Set.Icc (center i - radius) (center i + radius)}

/--
Bounded-density probability bound for the finite union of coordinate slabs.
For fixed dimension and a bounded ambient box, this is the formal geometric
core behind the paper's `O(r_t)` bad-region estimates.
-/
theorem boundedDensity_coordinateSlabBadRegion_le
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (volume : Measure (Coord → ℝ)) μ C)
    (boxLo boxHi center : Coord → ℝ) (radius : ℝ) :
    μ (coordinateSlabBadRegion boxLo boxHi center radius)
      ≤ C *
        ∑ i : Coord,
          ∏ j : Coord, ENNReal.ofReal
            ((Function.update boxHi i (center i + radius)) j -
              (Function.update boxLo i (center i - radius)) j) := by
  let slab : Coord → Set (Coord → ℝ) := fun i =>
    {ideal : Coord → ℝ |
      ideal ∈ Set.Icc boxLo boxHi ∧
        ideal i ∈ Set.Icc (center i - radius) (center i + radius)}
  calc
    μ (coordinateSlabBadRegion boxLo boxHi center radius)
        = μ (⋃ i ∈ (Finset.univ : Finset Coord), slab i) := by
          rfl
    _ ≤ ∑ i ∈ (Finset.univ : Finset Coord), μ (slab i) := by
          exact measure_biUnion_finset_le (Finset.univ : Finset Coord) slab
    _ ≤
        ∑ i ∈ (Finset.univ : Finset Coord),
          C * ∏ j : Coord, ENNReal.ofReal
            ((Function.update boxHi i (center i + radius)) j -
              (Function.update boxLo i (center i - radius)) j) := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          exact
            AppliedModelingLib.Probability.HasBoundedDensity.measure_coordinate_slab_Icc_le_const_mul_volume
              hbd boxLo boxHi i (center i) radius
    _ =
        C *
          ∑ i ∈ (Finset.univ : Finset Coord),
            ∏ j : Coord, ENNReal.ofReal
              ((Function.update boxHi i (center i + radius)) j -
                (Function.update boxLo i (center i - radius)) j) := by
          rw [Finset.mul_sum]
    _ =
        C *
          ∑ i : Coord,
            ∏ j : Coord, ENNReal.ofReal
              ((Function.update boxHi i (center i + radius)) j -
                (Function.update boxLo i (center i - radius)) j) := by
          simp

/--
Nullness of the coordinate-equality bad event gives the almost-everywhere
noncollision hypothesis needed by the Lemma 3 derivative and norm formulas.
-/
theorem ae_forall_coordinate_ne_of_coordinateEqualityBadEvent_null
    {Coord : Type*} [MeasurableSpace (Coord → ℝ)]
    {μ : Measure (Coord → ℝ)} {x : Coord → ℝ}
    (hnull : μ (coordinateEqualityBadEvent x) = 0) :
    ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i := by
  exact (measure_eq_zero_iff_ae_notMem.1 hnull).mono
    (fun ideal hideal => (notMem_coordinateEqualityBadEvent_iff x ideal).mp hideal)

/--
Product-measure bounded density gives the almost-everywhere noncollision
hypothesis needed by the Lemma 3 derivative and norm formulas.
-/
theorem ae_forall_coordinate_ne_of_productMeasure_boundedDensity
    {Coord : Type*} [Fintype Coord]
    (ρ : Measure ℝ) [SigmaFinite ρ] [NoAtoms ρ]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd :
      AppliedModelingLib.Probability.HasBoundedDensity
        (Measure.pi (fun _ : Coord => ρ)) μ C)
    (x : Coord → ℝ) :
    ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i := by
  exact ae_forall_coordinate_ne_of_coordinateEqualityBadEvent_null
    (productMeasure_boundedDensity_coordinateEqualityBadEvent_null ρ hbd x)

/--
The source C3 bounded-density condition directly gives almost-everywhere
coordinate noncollision in the finite-dimensional representation.
-/
theorem ae_forall_coordinate_ne_of_volume_boundedDensity
    {Coord : Type*} [Fintype Coord]
    {μ : Measure (Coord → ℝ)} {C : ℝ≥0∞}
    (hbd : AppliedModelingLib.Probability.HasBoundedDensity (volume : Measure (Coord → ℝ)) μ C)
    (x : Coord → ℝ) :
    ∀ᵐ ideal ∂μ, ∀ i, x i ≠ ideal i := by
  exact ae_forall_coordinate_ne_of_coordinateEqualityBadEvent_null
    (volume_boundedDensity_coordinateEqualityBadEvent_null hbd x)

/--
Structured finite-coordinate version of the paper's bounded-density ideal-point
condition C3, separated from the source-facing abstract `ILVEnvironment` field.
The density is with respect to the full finite-dimensional Lebesgue measure,
as in the paper; no coordinate-independence condition is imposed.
-/
structure FiniteCoordinateIdealDistributionData
    (Coord : Type*) [Fintype Coord] where
  idealMeasure : Measure (Coord → ℝ)
  probability : IsProbabilityMeasure idealMeasure
  densityBound : ℝ≥0∞
  densityBound_ne_top : densityBound ≠ ⊤
  hasBoundedDensity :
    AppliedModelingLib.Probability.HasBoundedDensity
      (volume : Measure (Coord → ℝ)) idealMeasure densityBound
  /-- Source condition C3 states that the bounded density is measurable. -/
  density_measurable :
    ∃ density : (Coord → ℝ) → ℝ≥0∞,
      Measurable density ∧
        idealMeasure = (volume : Measure (Coord → ℝ)).withDensity density ∧
          ∀ᵐ ideal ∂(volume : Measure (Coord → ℝ)), density ideal ≤ densityBound

namespace FiniteCoordinateIdealDistributionData

/--
The full-space bounded-density C3 carrier supplies the a.e.
coordinate-noncollision condition used by Appendix C.4 Lemma 3.
-/
theorem coordinate_noncollision_ae
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure, ∀ i, x i ≠ ideal i := by
  exact ae_forall_coordinate_ne_of_volume_boundedDensity
    D.hasBoundedDensity x

end FiniteCoordinateIdealDistributionData

/-- Paper step size `r_t = r_0 / t` for `t >= 1`. -/
noncomputable def ilvRadius (r0 : ℝ) (t : ℕ) : ℝ :=
  r0 / (t : ℝ)

/--
Tail view of the paper step-size schedule.  The update from global time
`N + t` to `N + t + 1` uses the original Algorithm 1 radius
`r_0 / (N + t + 1)`, not a restarted radius.
-/
noncomputable def ilvTailRadius (r0 : ℝ) (N t : ℕ) : ℝ :=
  ilvRadius r0 (t + N + 1)

theorem ilvRadius_nonneg {r0 : ℝ} (hr0 : 0 ≤ r0) (t : ℕ) :
    0 ≤ ilvRadius r0 t := by
  exact div_nonneg hr0 (Nat.cast_nonneg t)

theorem ilvTailRadius_nonneg {r0 : ℝ} (hr0 : 0 ≤ r0) (N t : ℕ) :
    0 ≤ ilvTailRadius r0 N t := by
  exact ilvRadius_nonneg hr0 (t + N + 1)

theorem ilvRadius_pos {r0 : ℝ} (hr0 : 0 < r0) {t : ℕ} (ht : 0 < t) :
    0 < ilvRadius r0 t := by
  exact div_pos hr0 (Nat.cast_pos.mpr ht)

theorem ilvRadius_succ_pos {r0 : ℝ} (hr0 : 0 < r0) (t : ℕ) :
    0 < ilvRadius r0 (t + 1) := by
  exact ilvRadius_pos hr0 (Nat.succ_pos t)

/-- Every positive-time harmonic ILV radius is bounded by its initial scale. -/
theorem ilvRadius_succ_le_initial {r0 : ℝ} (hr0 : 0 ≤ r0) (t : ℕ) :
    ilvRadius r0 (t + 1) ≤ r0 := by
  unfold ilvRadius
  have hpositive : (0 : ℝ) < ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos t
  have hone_le : (1 : ℝ) ≤ ((t + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le t)
  rw [div_le_iff₀ hpositive]
  simpa using mul_le_mul_of_nonneg_left hone_le hr0

theorem ilvTailRadius_pos {r0 : ℝ} (hr0 : 0 < r0) (N t : ℕ) :
    0 < ilvTailRadius r0 N t := by
  exact ilvRadius_pos hr0 (Nat.succ_pos (t + N))

theorem ilvRadius_tendsto_zero (r0 : ℝ) :
    Filter.Tendsto (ilvRadius r0) Filter.atTop (nhds 0) := by
  simpa [ilvRadius] using tendsto_const_div_atTop_nhds_zero_nat r0

theorem ilvRadius_eventually_le_of_pos (r0 : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ilvRadius r0 (t + 1) ≤ δ := by
  have heventually :
      ∀ᶠ n in Filter.atTop, ilvRadius r0 n < δ :=
    (ilvRadius_tendsto_zero r0).eventually (Iio_mem_nhds hδ)
  rcases Filter.eventually_atTop.1 heventually with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  exact le_of_lt (hT (t + 1) (le_trans ht (Nat.le_succ t)))

theorem ilvTailRadius_eventually_le_of_pos
    (r0 : ℝ) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℕ, ∀ t : ℕ, T ≤ t → ilvTailRadius r0 N t ≤ δ := by
  rcases ilvRadius_eventually_le_of_pos r0 hδ with ⟨T, hT⟩
  refine ⟨T, ?_⟩
  intro t ht
  have hTN : T ≤ t + N := le_trans ht (Nat.le_add_right t N)
  simpa [ilvTailRadius, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    hT (t + N) hTN

/--
The squared paper step sizes are summable after shifting to the source's
positive time indices.
-/
theorem ilvRadius_sq_summable (r0 : ℝ) :
    Summable (fun t : ℕ => (ilvRadius r0 (t + 1)) ^ 2) := by
  have hbase :
      Summable (fun n : ℕ => (1 / (n : ℝ) ^ (2 : ℕ) : ℝ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift :
      Summable
        (fun t : ℕ => (1 / (((t + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℝ)) := by
    simpa using
      ((summable_nat_add_iff
        (f := fun n : ℕ => (1 / (n : ℝ) ^ (2 : ℕ) : ℝ)) 1).mpr hbase)
  have hscaled :
      Summable
        (fun t : ℕ =>
          r0 ^ 2 * (1 / (((t + 1 : ℕ) : ℝ) ^ (2 : ℕ)) : ℝ)) :=
    hshift.mul_left (r0 ^ 2)
  refine hscaled.congr ?_
  intro t
  have ht : (((t + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero t
  change
    r0 ^ 2 * (1 / (((t + 1 : ℕ) : ℝ) ^ (2 : ℕ))) =
      (r0 / (((t + 1 : ℕ) : ℝ))) ^ (2 : ℕ)
  field_simp [ht]

/--
Every tail of the original paper step-size schedule remains square summable.
-/
theorem ilvTailRadius_sq_summable (r0 : ℝ) (N : ℕ) :
    Summable (fun t : ℕ => (ilvTailRadius r0 N t) ^ 2) := by
  have htail :=
    ((summable_nat_add_iff
      (f := fun t : ℕ => (ilvRadius r0 (t + 1)) ^ 2) N).mpr
      (ilvRadius_sq_summable r0))
  simpa [ilvTailRadius, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/--
For positive initial radius, the paper step sizes have divergent harmonic
partial sums after shifting to positive time indices.
-/
theorem ilvRadius_sum_tendsto_atTop {r0 : ℝ} (hr0 : 0 < r0) :
    Filter.Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
      Filter.atTop Filter.atTop := by
  simpa [ilvRadius, div_eq_mul_inv, Finset.mul_sum] using
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hr0)

/-- Positive shifted paper step sizes are not summable. -/
theorem ilvRadius_not_summable {r0 : ℝ} (hr0 : 0 < r0) :
    ¬ Summable (fun t : ℕ => ilvRadius r0 (t + 1)) := by
  have hnonneg : ∀ t : ℕ, 0 ≤ ilvRadius r0 (t + 1) := fun t =>
    ilvRadius_nonneg (le_of_lt hr0) (t + 1)
  rw [summable_iff_not_tendsto_nat_atTop_of_nonneg hnonneg]
  exact not_not.mpr (ilvRadius_sum_tendsto_atTop hr0)

theorem ilvTailRadius_not_summable {r0 : ℝ} (hr0 : 0 < r0) (N : ℕ) :
    ¬ Summable (fun t : ℕ => ilvTailRadius r0 N t) := by
  intro htail
  have hshift :
      Summable (fun t : ℕ => ilvRadius r0 ((t + N) + 1)) := by
    simpa [ilvTailRadius, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
  have hfull :
      Summable (fun t : ℕ => ilvRadius r0 (t + 1)) :=
    ((summable_nat_add_iff
      (f := fun t : ℕ => ilvRadius r0 (t + 1)) N).mp hshift)
  exact ilvRadius_not_summable hr0 hfull

/-- Every tail of the original paper step-size schedule still has divergent partial sums. -/
theorem ilvTailRadius_sum_tendsto_atTop {r0 : ℝ} (hr0 : 0 < r0) (N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => ∑ t ∈ Finset.range n, ilvTailRadius r0 N t)
      Filter.atTop Filter.atTop := by
  have hnonneg : ∀ t : ℕ, 0 ≤ ilvTailRadius r0 N t := fun t =>
    ilvTailRadius_nonneg (le_of_lt hr0) N t
  by_contra hnot
  have hsummable : Summable (fun t : ℕ => ilvTailRadius r0 N t) := by
    rw [summable_iff_not_tendsto_nat_atTop_of_nonneg hnonneg]
    exact hnot
  exact ilvTailRadius_not_summable hr0 N hsummable

/--
The step-size hypotheses used by the stochastic subgradient convergence theorem:
positive steps, square-summability, and divergent partial sums. The square and
sum conditions use shifted indices because Lean's natural numbers start at zero.
-/
def SSGMStepSizeConditions (radius : ℕ → ℝ) : Prop :=
  (∀ t : ℕ, 0 < t → 0 < radius t) ∧
    Summable (fun t : ℕ => (radius (t + 1)) ^ 2) ∧
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radius (t + 1))
        Filter.atTop Filter.atTop

theorem ilvRadius_ssgmStepSizeConditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact ⟨fun t ht => ilvRadius_pos hr0 ht,
    ilvRadius_sq_summable r0,
    ilvRadius_sum_tendsto_atTop hr0⟩

theorem algorithm1_radius_ssgmStepSizeConditions {r0 : ℝ} (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) := by
  exact ilvRadius_ssgmStepSizeConditions hr0

/--
Abstract data for a paper ILV instance.

The fields `convergesWithProbabilityOne` and `convergesToPoint` are kept
abstract in this first pass; they are the planned interface to the later
stochastic approximation library layer.
-/
structure ILVEnvironment (Voter Point : Type*) where
  solutionSpace : Set Point
  utility : Voter → Point → ℝ
  ideal : Voter → Point
  normDistance : SourceNorm → Point → Point → ℝ
  trajectory : SourceNorm → VoterResponseModel → ℕ → Point
  societalUtility : Point → ℝ
  socialOptimal : Set Point
  medianSet : Set Point
  directionalField : Point → Point
  zeroDirection : Point
  utilityGradient : Voter → Point → Point
  scalarDirection : ℝ → Point → Point
  voterExpectation : (Voter → Point) → Point
  convergesWithProbabilityOne : (ℕ → Point) → Set Point → Prop
  convergesToPoint : (ℕ → Point) → Point → Prop
  respondsAccordingTo : VoterResponseModel → Prop
  solutionSpace_nonempty_bounded_closed_convex : Prop
  uniqueIdealSolutions : Prop
  idealDistribution_bounded_measurable_density : Prop
  directionalFieldUniformlyContinuous : Prop

/--
The local feasible set queried by ILV at a current point: feasible points in
`X` within radius `r` under the chosen `Lq`-style distance.
-/
def LocalNeighborhood {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) : Set Point :=
  {candidate | candidate ∈ E.solutionSpace ∧
    E.normDistance q candidate center ≤ r}

/--
The source Model A query ball before Algorithm 1 projects the returned point
onto the feasible solution space.  Unlike `LocalNeighborhood`, this raw ball
does not impose membership in `E.solutionSpace`.
-/
def RawLocalNeighborhood {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) : Set Point :=
  {candidate | E.normDistance q candidate center ≤ r}

/--
Model A response at one query: the returned point is feasible in the queried
local neighborhood and maximizes the queried voter's utility over that
neighborhood.
-/
def ModelAResponseAt {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  response ∈ LocalNeighborhood E q center r ∧
    ∀ candidate, candidate ∈ LocalNeighborhood E q center r →
      E.utility voter candidate ≤ E.utility voter response

/--
Source-faithful Model A response at one query: a voter maximizes utility over
the raw `Lq` ball, and Algorithm 1 performs the separate projection onto the
solution space afterward.
-/
def ModelARawResponseAt {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) : Prop :=
  response ∈ RawLocalNeighborhood E q center r ∧
    ∀ candidate, candidate ∈ RawLocalNeighborhood E q center r →
      E.utility voter candidate ≤ E.utility voter response

/--
Finite-coordinate Model B normalized direction, with the subgradient vector
supplied explicitly.  The printed quotient is undefined at the zero
subgradient; the source-definedness convention is that a zero gradient causes
no movement, so its normalized direction is the zero vector.
-/
noncomputable def modelBFiniteNormalizedDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm) (gradient : Coord → ℝ) : Coord → ℝ :=
  if gradient = 0 then fun _ => 0 else
    fun i => gradient i / finiteCoordinateNorm q gradient

/-- Away from the explicit zero-gradient branch, Model B uses the printed quotient. -/
theorem modelBFiniteNormalizedDirection_of_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm) (gradient : Coord → ℝ) (hgradient : gradient ≠ 0) :
    modelBFiniteNormalizedDirection q gradient =
      fun i => gradient i / finiteCoordinateNorm q gradient := by
  simp [modelBFiniteNormalizedDirection, hgradient]

/--
Finite-coordinate Model B one-step response formula.  For a nonzero supplied
subgradient it is `x' = x + r * g / ||g||_q`; for the zero subgradient the
source-definedness convention leaves the current point unchanged.
-/
noncomputable def ModelBFiniteResponseAt
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm) (center : Coord → ℝ) (r : ℝ)
    (gradient response : Coord → ℝ) : Prop :=
  response =
    fun i => center i + r * modelBFiniteNormalizedDirection q gradient i

/--
The paper's displayed subgradient relation for a voter utility.  The direction
of the inequality is kept exactly as printed in the Model B paragraph.
-/
def FiniteSourceSubgradientAt
    {Coord : Type*} [Fintype Coord]
    (utility : (Coord → ℝ) → ℝ) (x gradient : Coord → ℝ) : Prop :=
  ∀ y,
    utility y - utility x ≥
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        gradient (fun i => y i - x i)

/--
Finite-coordinate Model B with its source subgradient premise visible: a voter
moves from the current point by the full radius in a displayed utility
subgradient direction.
-/
noncomputable def ModelBFiniteResponseWithSourceSubgradient
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utility : (Coord → ℝ) → ℝ) (q : SourceNorm)
    (center : Coord → ℝ) (r : ℝ) (response : Coord → ℝ) : Prop :=
  ∃ gradient,
    FiniteSourceSubgradientAt utility center gradient ∧
      ModelBFiniteResponseAt q center r gradient response

/--
A response minimizes distance to a voter's ideal point over a feasible local
query set.  This is the appendix cost-minimization version of body-text Model A
utility maximization for `Lp`-normed utilities.
-/
def NormDistanceMinimizerOn {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p : SourceNorm)
    (target : Point) (feasible : Set Point) (response : Point) : Prop :=
  response ∈ feasible ∧
    ∀ candidate, candidate ∈ feasible →
      E.normDistance p response target ≤ E.normDistance p candidate target

theorem mem_localNeighborhood_iff {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center candidate : Point) (r : ℝ) :
    candidate ∈ LocalNeighborhood E q center r ↔
      candidate ∈ E.solutionSpace ∧
        E.normDistance q candidate center ≤ r := by
  rfl

theorem mem_rawLocalNeighborhood_iff {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center candidate : Point) (r : ℝ) :
    candidate ∈ RawLocalNeighborhood E q center r ↔
      E.normDistance q candidate center ≤ r := by
  rfl

theorem localNeighborhood_mem_solutionSpace {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r : ℝ}
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    candidate ∈ E.solutionSpace :=
  hmem.1

theorem localNeighborhood_normDistance_le {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r : ℝ}
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    E.normDistance q candidate center ≤ r :=
  hmem.2

theorem localNeighborhood_mono_radius {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {center candidate : Point} {r R : ℝ}
    (hrR : r ≤ R)
    (hmem : candidate ∈ LocalNeighborhood E q center r) :
    candidate ∈ LocalNeighborhood E q center R := by
  exact ⟨hmem.1, le_trans hmem.2 hrR⟩

theorem modelAResponseAt_iff {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        ∀ candidate, candidate ∈ LocalNeighborhood E q center r →
          E.utility voter candidate ≤ E.utility voter response := by
  rfl

theorem modelAResponseAt_iff_isMaxOn {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        IsMaxOn (E.utility voter) (LocalNeighborhood E q center r) response := by
  rfl

theorem modelARawResponseAt_iff {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelARawResponseAt E q center r voter response ↔
      response ∈ RawLocalNeighborhood E q center r ∧
        ∀ candidate, candidate ∈ RawLocalNeighborhood E q center r →
          E.utility voter candidate ≤ E.utility voter response := by
  rfl

theorem modelARawResponseAt_iff_isMaxOn {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point) :
    ModelARawResponseAt E q center r voter response ↔
      response ∈ RawLocalNeighborhood E q center r ∧
        IsMaxOn (E.utility voter) (RawLocalNeighborhood E q center r) response := by
  rfl

theorem modelBFiniteResponseAt_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm) (center : Coord → ℝ) (r : ℝ)
    (gradient response : Coord → ℝ) :
    ModelBFiniteResponseAt q center r gradient response ↔
      response =
        fun i => center i + r *
          modelBFiniteNormalizedDirection q gradient i := by
  rfl

/-- The source-defined zero-gradient branch of Model B leaves the point fixed. -/
theorem modelBFiniteResponseAt_of_gradient_eq_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {q : SourceNorm} {center response : Coord → ℝ} {r : ℝ}
    (hresponse : ModelBFiniteResponseAt q center r 0 response) :
    response = center := by
  rw [modelBFiniteResponseAt_formula] at hresponse
  simpa [modelBFiniteNormalizedDirection] using hresponse

/-- Away from the zero-gradient branch, Model B is the printed quotient formula. -/
theorem modelBFiniteResponseAt_of_gradient_ne_zero_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {q : SourceNorm} {center gradient response : Coord → ℝ} {r : ℝ}
    (hgradient : gradient ≠ 0) :
    ModelBFiniteResponseAt q center r gradient response ↔
      response = fun i => center i + r *
        (gradient i / finiteCoordinateNorm q gradient) := by
  simp [modelBFiniteResponseAt_formula, modelBFiniteNormalizedDirection, hgradient]

/--
The coordinatewise-boundary reading of Model B used by the Proposition 2
proof for an `L∞` neighborhood.  Every non-tied coordinate moves by the full
radius toward that coordinate of the voter's ideal; a tied coordinate does not
move.  This rule depends on derivative signs, not on their relative
magnitudes.
-/
def ModelBCoordinatewiseBoundaryResponseAt
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) (response : Coord → ℝ) : Prop :=
  response = fun i =>
    center i - r * ((center i - ideal i) / |center i - ideal i|)

/-- Coordinate increment form of the finite Model B response formula. -/
theorem modelBFiniteResponseAt_coord_increment
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {q : SourceNorm} {center : Coord → ℝ} {r : ℝ}
    {gradient response : Coord → ℝ} (i : Coord)
    (hresponse : ModelBFiniteResponseAt q center r gradient response) :
    response i - center i = r * modelBFiniteNormalizedDirection q gradient i := by
  rw [modelBFiniteResponseAt_formula] at hresponse
  rw [hresponse]
  simp [modelBFiniteNormalizedDirection]

/--
Signed coordinate increment form of Model B.  This is the algebraic shell used
by the Theorem 3 Appendix C.6 coordinate-drift argument before taking
expectations over the sampled voter.
-/
theorem modelBFiniteResponseAt_signed_coord_increment
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {q : SourceNorm} {center : Coord → ℝ} {r a : ℝ}
    {gradient response : Coord → ℝ} (i : Coord)
    (hresponse : ModelBFiniteResponseAt q center r gradient response) :
    a * (response i - center i) =
      r * (a * modelBFiniteNormalizedDirection q gradient i) := by
  rw [modelBFiniteResponseAt_coord_increment i hresponse]
  ring

theorem modelBFiniteNormalizedDirection_l2_norm_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (gradient : Coord → ℝ) :
    finiteCoordinateNorm SourceNorm.l2
        (modelBFiniteNormalizedDirection SourceNorm.l2 gradient) ≤ 1 := by
  by_cases hzero : finiteCoordinateNorm SourceNorm.l2 gradient = 0
  · have hdir :
        modelBFiniteNormalizedDirection SourceNorm.l2 gradient =
          fun _ : Coord => 0 := by
      funext i
      simp [modelBFiniteNormalizedDirection, hzero]
    rw [hdir]
    have hnorm :
        finiteCoordinateNorm SourceNorm.l2 (fun _ : Coord => 0) = 0 := by
      exact AppliedModelingLib.FiniteDimensionalNorms.normL2_zero
    linarith
  · have hnonneg : 0 ≤ finiteCoordinateNorm SourceNorm.l2 gradient := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg gradient)
    have hpos : 0 < finiteCoordinateNorm SourceNorm.l2 gradient :=
      lt_of_le_of_ne' hnonneg hzero
    have hgradient : gradient ≠ 0 := by
      intro hgradient
      subst gradient
      apply hzero
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.normL2_zero (ι := Coord))
    have hdir :
        modelBFiniteNormalizedDirection SourceNorm.l2 gradient =
          fun i => (finiteCoordinateNorm SourceNorm.l2 gradient)⁻¹ *
            gradient i := by
      rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
      funext i
      rw [div_eq_mul_inv]
      ring
    rw [hdir, finiteCoordinateNorm_l2_smul, abs_of_pos (inv_pos.mpr hpos)]
    field_simp [hpos.ne']
    exact le_rfl

theorem modelBFiniteResponseAt_l2_step_distance_le_abs_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center gradient response : Coord → ℝ} {r : ℝ}
    (hresponse :
      ModelBFiniteResponseAt SourceNorm.l2 center r gradient response) :
    finiteCoordinateDistance SourceNorm.l2 response center ≤ |r| := by
  have hdiff :
      (fun i => response i - center i) =
        fun i => r * modelBFiniteNormalizedDirection SourceNorm.l2 gradient i := by
    funext i
    exact modelBFiniteResponseAt_coord_increment i hresponse
  unfold finiteCoordinateDistance
  rw [hdiff, finiteCoordinateNorm_l2_smul]
  exact mul_le_of_le_one_right (abs_nonneg r)
    (modelBFiniteNormalizedDirection_l2_norm_le_one gradient)

theorem modelBFiniteResponseAt_l2_within_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center gradient response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hresponse :
      ModelBFiniteResponseAt SourceNorm.l2 center r gradient response) :
    finiteCoordinateDistance SourceNorm.l2 response center ≤ r := by
  simpa [abs_of_nonneg hr] using
    modelBFiniteResponseAt_l2_step_distance_le_abs_radius hresponse

/--
For finite `Lq`, a Model B response with a unit-`Lq` supplied direction lies on
the boundary of the radius-`r` local ball.
-/
theorem modelBFiniteResponseAt_lp_boundary_distance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {q : ℝ} (hq : 0 < q)
    {center gradient response : Coord → ℝ} {r : ℝ}
    (hnorm : finiteCoordinateNorm (SourceNorm.lp q) gradient = 1)
    (hresponse : ModelBFiniteResponseAt (SourceNorm.lp q) center r gradient response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center = |r| := by
  rw [modelBFiniteResponseAt_formula] at hresponse
  have hgradient : gradient ≠ 0 := by
    intro hgradient
    subst gradient
    have hzeroNorm :
        finiteCoordinateNorm (SourceNorm.lp q) (fun _ : Coord => (0 : ℝ)) = 0 := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.lp_zero_of_pos (ι := Coord) hq)
    exact zero_ne_one (hzeroNorm.symm.trans hnorm)
  rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient] at hresponse
  rw [hresponse]
  have hvec :
      (fun i => (center i + r * (gradient i /
          finiteCoordinateNorm (SourceNorm.lp q) gradient)) - center i) =
        fun i => r * gradient i := by
    funext i
    rw [hnorm]
    ring
  unfold finiteCoordinateDistance
  rw [hvec]
  change AppliedModelingLib.FiniteDimensionalNorms.lp q (fun i => r * gradient i) = |r|
  have hnorm' : AppliedModelingLib.FiniteDimensionalNorms.lp q gradient = 1 := by
    simpa [finiteCoordinateNorm] using hnorm
  rw [AppliedModelingLib.FiniteDimensionalNorms.lp_smul_of_pos hq, hnorm']
  simp

/--
For the Appendix C.4 Lemma 3 candidate gradient, the Model B normalization by
the `Lq` norm does not change the vector.
-/
theorem modelBFiniteNormalizedDirection_lpCostGradientCandidate_eq_self
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    modelBFiniteNormalizedDirection (SourceNorm.lp q)
      (lpCostGradientCandidate p (fun i => x i - ideal i)) =
        lpCostGradientCandidate p (fun i => x i - ideal i) := by
  ext i
  have hnorm :=
    lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl hdual hcoord
  have hgradient :
      lpCostGradientCandidate p (fun i => x i - ideal i) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    have hzeroNorm :
        finiteCoordinateNorm (SourceNorm.lp q) (fun _ : Coord => (0 : ℝ)) = 0 := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.lp_zero_of_pos (ι := Coord) hdual.2.1)
    exact zero_ne_one (hzeroNorm.symm.trans hnorm)
  rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient,
    hnorm]
  simp

/--
The negative of the Appendix C.4 candidate gradient also has `Lq` norm one, so
Model B normalization does not change the utility-gradient direction either.
-/
theorem modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    modelBFiniteNormalizedDirection (SourceNorm.lp q)
      (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i) =
        fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i := by
  ext i
  have hnorm :
      finiteCoordinateNorm (SourceNorm.lp q)
        (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i) = 1 := by
    simpa [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.lp,
      AppliedModelingLib.FiniteDimensionalNorms.lpPower] using
      (lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl
        (Coord := Coord) hdual hcoord)
  have hgradient :
      (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    have hzeroNorm :
        finiteCoordinateNorm (SourceNorm.lp q) (fun _ : Coord => (0 : ℝ)) = 0 := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.lp_zero_of_pos (ι := Coord) hdual.2.1)
    exact zero_ne_one (hzeroNorm.symm.trans hnorm)
  rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
  rw [hnorm]
  simp

/--
Theorem 2-specific boundary fact: moving in the sign-correct utility-gradient
direction `-∇cost` reaches the radius-`r` boundary in the finite `Lq` distance.
-/
theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hcoord : ∀ i, center i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center = |r| := by
  have hnorm :
      finiteCoordinateNorm (SourceNorm.lp q)
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i) = 1 := by
    simpa [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.lp,
      AppliedModelingLib.FiniteDimensionalNorms.lpPower] using
      (lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl
        (Coord := Coord) hdual hcoord)
  exact modelBFiniteResponseAt_lp_boundary_distance hdual.2.1 hnorm hresponse

theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance_of_notMem_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (havoid : ideal ∉ coordinateEqualityBadEvent center)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center = |r| := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance
    hdual ((notMem_coordinateEqualityBadEvent_iff center ideal).mp havoid)
    hresponse

theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_within_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hcoord : ∀ i, center i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    finiteCoordinateDistance (SourceNorm.lp q) response center ≤ r := by
  rw [modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance
    hdual hcoord hresponse, abs_of_nonneg hr]

/--
For the Appendix C.4 Lemma 3 candidate gradient, Model B's finite-coordinate
one-step formula reduces to movement by the unnormalized candidate gradient.
-/
theorem modelBFiniteResponseAt_lpCostGradientCandidate_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (lpCostGradientCandidate p (fun i => center i - ideal i)) response ↔
      response =
        fun i => center i + r *
          lpCostGradientCandidate p (fun j => center j - ideal j) i := by
  unfold ModelBFiniteResponseAt
  rw [modelBFiniteNormalizedDirection_lpCostGradientCandidate_eq_self hdual hcoord]

/--
The sign-correct Theorem 2 Model B step moves opposite the finite `Lp` cost
gradient, once Lemma 3 removes the normalization.
-/
theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response ↔
      response =
        fun i => center i - r *
          lpCostGradientCandidate p (fun j => center j - ideal j) i := by
  unfold ModelBFiniteResponseAt
  rw [modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self hdual hcoord]
  simp [sub_eq_add_neg, mul_neg]

/-- A projection operator onto the feasible solution space `X`. -/
def ProjectionOnto {Point : Type*} (X : Set Point) (project : Point → Point) : Prop :=
  ∀ y, project y ∈ X

/--
Norm-minimizing version of the projection notation `[·]_X`, parameterized by the
paper-level distance used to measure proximity to the raw point.
-/
def IsNormProjectionOnto {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (project : Point → Point) : Prop :=
  ∀ y, project y ∈ E.solutionSpace ∧
    IsMinOn (fun x => E.normDistance q x y) E.solutionSpace (project y)

theorem isNormProjectionOnto_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (project : Point → Point) :
    IsNormProjectionOnto E q project ↔
      ∀ y, project y ∈ E.solutionSpace ∧
        IsMinOn (fun x => E.normDistance q x y) E.solutionSpace (project y) := by
  rfl

theorem projectionOnto_of_isNormProjectionOnto {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    {project : Point → Point}
    (hproject : IsNormProjectionOnto E q project) :
    ProjectionOnto E.solutionSpace project := by
  intro y
  exact (hproject y).1

/-- Algorithm 1 projected update: `x_t = [x'_t]_X`. -/
def Algorithm1ProjectedUpdate
    {Point : Type*} (project : Point → Point) (raw next : Point) : Prop :=
  next = project raw

theorem algorithm1ProjectedUpdate_formula
    {Point : Type*} (project : Point → Point) (raw next : Point) :
    Algorithm1ProjectedUpdate project raw next ↔ next = project raw := by
  rfl

theorem algorithm1ProjectedUpdate_mem_of_projectionOnto
    {Point : Type*} {X : Set Point} {project : Point → Point}
    {raw next : Point}
    (hproject : ProjectionOnto X project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    next ∈ X := by
  rw [algorithm1ProjectedUpdate_formula] at hupdate
  rw [hupdate]
  exact hproject raw

theorem algorithm1ProjectedUpdate_mem_solutionSpace_of_normProjection
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {project : Point → Point} {raw next : Point}
    (hproject : IsNormProjectionOnto E q project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    next ∈ E.solutionSpace := by
  exact algorithm1ProjectedUpdate_mem_of_projectionOnto
    (projectionOnto_of_isNormProjectionOnto E q hproject) hupdate

theorem algorithm1ProjectedUpdates_mem_of_projectionOnto
    {Point : Type*} {X : Set Point} {project : Point → Point}
    {raw trajectory : ℕ → Point}
    (hproject : ProjectionOnto X project)
    (h0 : trajectory 0 ∈ X)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ X := by
  intro t
  induction t with
  | zero => exact h0
  | succ t _ih =>
      exact algorithm1ProjectedUpdate_mem_of_projectionOnto hproject (hupdate t)

theorem algorithm1ProjectedUpdates_mem_solutionSpace_of_normProjection
    {Voter Point : Type*} {E : ILVEnvironment Voter Point} {q : SourceNorm}
    {project : Point → Point} {raw trajectory : ℕ → Point}
    (hproject : IsNormProjectionOnto E q project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (hupdate :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact algorithm1ProjectedUpdates_mem_of_projectionOnto
    (projectionOnto_of_isNormProjectionOnto E q hproject) h0 hupdate

/--
Algorithm 1 stopping-window condition, expressed using the paper-level
distance chosen for the trajectory.
-/
def Algorithm1WindowStable {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) : Prop :=
  ∀ l m,
    l ∈ Finset.Icc (t - N) t →
      m ∈ Finset.Icc (t - N) t →
        E.normDistance q (trajectory l) (trajectory m) ≤ epsilon

theorem algorithm1WindowStable_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (t N : ℕ) (epsilon : ℝ) :
    Algorithm1WindowStable E q trajectory t N epsilon ↔
      ∀ l m,
        l ∈ Finset.Icc (t - N) t →
          m ∈ Finset.Icc (t - N) t →
            E.normDistance q (trajectory l) (trajectory m) ≤ epsilon := by
  rfl

/-- Algorithm 1 stops either at terminal time `T` or at a stable recent window. -/
def Algorithm1StopCondition {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) : Prop :=
  t = T ∨ Algorithm1WindowStable E q trajectory t N epsilon

theorem algorithm1StopCondition_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (q : SourceNorm)
    (trajectory : ℕ → Point) (T N t : ℕ) (epsilon : ℝ) :
    Algorithm1StopCondition E q trajectory T N t epsilon ↔
      t = T ∨ Algorithm1WindowStable E q trajectory t N epsilon := by
  rfl

/--
Finite-coordinate projected stochastic subgradient update from Appendix C.1:
`x_t = [x_{t-1} - r_t * (g_t + z_t + b_t)]_X`.
-/
def FiniteProjectedSSGMUpdateAt
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous : Coord → ℝ) (radius : ℝ)
    (subgradient noise bias next : Coord → ℝ) : Prop :=
  next =
    project
      (fun i => previous i -
        radius * (subgradient i + noise i + bias i))

theorem finiteProjectedSSGMUpdateAt_formula
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous : Coord → ℝ) (radius : ℝ)
    (subgradient noise bias next : Coord → ℝ) :
    FiniteProjectedSSGMUpdateAt project previous radius
        subgradient noise bias next ↔
      next =
        project
          (fun i => previous i -
            radius * (subgradient i + noise i + bias i)) := by
  rfl

/-- Decomposition of a reported direction into mean subgradient, noise, and bias. -/
def FiniteSSGMDirectionDecomposition
    {Coord : Type*}
    (reported averageSubgradient noise bias : Coord → ℝ) : Prop :=
  reported = fun i => averageSubgradient i + noise i + bias i

theorem finiteSSGMDirectionDecomposition_formula
    {Coord : Type*}
    (reported averageSubgradient noise bias : Coord → ℝ) :
    FiniteSSGMDirectionDecomposition reported averageSubgradient noise bias ↔
      reported = fun i => averageSubgradient i + noise i + bias i := by
  rfl

/--
Finite-coordinate subgradient predicate: `g` is a subgradient of `cost` at `x`
if the affine lower bound with slope `g` holds at every point.
-/
def FiniteSubgradientAt
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) : Prop :=
  ∀ y,
    cost x +
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g
        (fun i => y i - x i) ≤ cost y

theorem finiteSubgradientAt_formula
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ) (x g : Coord → ℝ) :
    FiniteSubgradientAt cost x g ↔
      ∀ y,
        cost x +
          AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g
            (fun i => y i - x i) ≤ cost y := by
  rfl

theorem coordinateLinearFunctional_apply
    {Coord : Type*} [Fintype Coord] (g d : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g d =
      ∑ i : Coord, g i * d i := by
  simp [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional]

theorem coordinateLinearFunctional_apply_finset_weighted_sum
    {Coord Component : Type*} [Fintype Coord]
    (components : Finset Component) (coeff : Component → ℝ)
    (componentGradient : Component → Coord → ℝ) (d : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (fun i => components.sum (fun k => coeff k * componentGradient k i)) d =
      components.sum
        (fun k =>
          coeff k *
            AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
              (componentGradient k) d) := by
  rw [coordinateLinearFunctional_apply]
  simp_rw [coordinateLinearFunctional_apply]
  calc
    (∑ i : Coord,
        (components.sum (fun k => coeff k * componentGradient k i)) * d i)
        =
          ∑ i : Coord,
            components.sum
              (fun k => (coeff k * componentGradient k i) * d i) := by
            simp_rw [Finset.sum_mul]
    _ =
          components.sum
            (fun k =>
              ∑ i : Coord, (coeff k * componentGradient k i) * d i) := by
            exact Finset.sum_comm
    _ =
          components.sum
            (fun k =>
              coeff k *
                ∑ i : Coord, componentGradient k i * d i) := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _hi
            ring

theorem finiteSubgradientAt_finset_nonneg_weighted_sum
    {Coord Component : Type*} [Fintype Coord]
    (components : Finset Component) {coeff : Component → ℝ}
    {componentCost : Component → (Coord → ℝ) → ℝ}
    {x : Coord → ℝ} {componentGradient : Component → Coord → ℝ}
    (hcoeff : ∀ k, k ∈ components → 0 ≤ coeff k)
    (hsubgradient :
      ∀ k, k ∈ components →
        FiniteSubgradientAt (componentCost k) x (componentGradient k)) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        components.sum (fun k => coeff k * componentCost k y))
      x
      (fun i => components.sum (fun k => coeff k * componentGradient k i)) := by
  intro y
  let d : Coord → ℝ := fun i => y i - x i
  have hweighted :
      ∀ k ∈ components,
        coeff k * componentCost k x +
            coeff k *
              AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
                (componentGradient k) d ≤
          coeff k * componentCost k y := by
    intro k hk
    have h := hsubgradient k hk y
    have hmul := mul_le_mul_of_nonneg_left h (hcoeff k hk)
    linarith
  have hsum := Finset.sum_le_sum hweighted
  have hleft :
      (components.sum (fun k => coeff k * componentCost k x)) +
          components.sum
            (fun k =>
              coeff k *
                AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
                  (componentGradient k) d) =
        components.sum
          (fun k =>
            coeff k * componentCost k x +
              coeff k *
                AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
                  (componentGradient k) d) := by
    rw [← Finset.sum_add_distrib]
  calc
    (components.sum (fun k => coeff k * componentCost k x)) +
        AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => components.sum (fun k => coeff k * componentGradient k i))
          (fun i => y i - x i)
        =
          (components.sum (fun k => coeff k * componentCost k x)) +
            components.sum
              (fun k =>
                coeff k *
                  AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
                    (componentGradient k) d) := by
            rw [coordinateLinearFunctional_apply_finset_weighted_sum]
    _ =
          components.sum
            (fun k =>
              coeff k * componentCost k x +
                coeff k *
                  AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
                    (componentGradient k) d) := hleft
    _ ≤ components.sum (fun k => coeff k * componentCost k y) := hsum

/--
Supporting-line inequality for a differentiable convex real function.  This
one-dimensional bridge lets the finite-dimensional subgradient proof below use
mathlib's convex slope calculus along affine lines.
-/
theorem convexOn_univ_tangent_le_of_hasDerivAt
    {f : ℝ → ℝ} {a z0 : ℝ}
    (hconv : ConvexOn ℝ Set.univ f)
    (hf : HasDerivAt f a z0) :
    ∀ z : ℝ, f z0 + a * (z - z0) ≤ f z := by
  intro z
  rcases lt_trichotomy z z0 with hlt | heq | hgt
  · have hslope : slope f z z0 ≤ a :=
      hconv.slope_le_of_hasDerivAt
        (Set.mem_univ z) (Set.mem_univ z0) hlt hf
    have hden_pos : 0 < z0 - z := sub_pos.mpr hlt
    have hslope' : (f z0 - f z) / (z0 - z) ≤ a := by
      simpa [slope_def_field] using hslope
    have hmul : f z0 - f z ≤ a * (z0 - z) :=
      (div_le_iff₀ hden_pos).mp hslope'
    linarith
  · subst heq
    simp
  · have hslope : a ≤ slope f z0 z :=
      hconv.le_slope_of_hasDerivAt
        (Set.mem_univ z0) (Set.mem_univ z) hgt hf
    have hden_pos : 0 < z - z0 := sub_pos.mpr hgt
    have hslope' : a ≤ (f z - f z0) / (z - z0) := by
      simpa [slope_def_field] using hslope
    have hmul : a * (z - z0) ≤ f z - f z0 :=
      (le_div_iff₀ hden_pos).mp hslope'
    linarith

/--
For a convex finite-coordinate cost on the whole vector space, the Fréchet
derivative vector supplied by `coordinateLinearFunctional` is a finite
subgradient.  This connects mathlib convex calculus to the paper-local SSGM
subgradient predicate.
-/
theorem finiteSubgradientAt_of_convexOn_univ_hasFDerivAt
    {Coord : Type*} [Fintype Coord]
    {cost : (Coord → ℝ) → ℝ} {x g : Coord → ℝ}
    (hconv : ConvexOn ℝ Set.univ cost)
    (hderiv :
      HasFDerivAt cost
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g) x) :
    FiniteSubgradientAt cost x g := by
  intro y
  let line : ℝ →ᵃ[ℝ] (Coord → ℝ) := AffineMap.lineMap x y
  have hlineConv :
      ConvexOn ℝ Set.univ (fun t : ℝ => cost (line t)) := by
    simpa [line, Set.preimage_univ] using hconv.comp_affineMap line
  have hlineDeriv :
      HasDerivAt (fun t : ℝ => cost (line t))
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g
          (fun i => y i - x i)) 0 := by
    have hline : HasDerivAt line (fun i => y i - x i) (0 : ℝ) := by
      simpa [line] using
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
    have hderiv_line :
        HasFDerivAt cost
          (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional g)
          (line 0) := by
      simpa [line, AffineMap.lineMap_apply] using hderiv
    simpa using hderiv_line.comp_hasDerivAt 0 hline
  have htan := convexOn_univ_tangent_le_of_hasDerivAt hlineConv hlineDeriv 1
  simpa [FiniteSubgradientAt, line, AffineMap.lineMap_apply] using htan

/--
Finite `Lp` cost convexity, routed through mathlib's `PiLp` norm.  This removes
one paper-local proof obligation from the Lemma 3-to-SSGM bridge for finite
Holder-dual exponents.
-/
theorem convexOn_univ_finiteCoordinate_lp_cost
    {Coord : Type*} [Fintype Coord]
    {p : ℝ} (hp : 1 ≤ p) (ideal : Coord → ℝ) :
    ConvexOn ℝ Set.univ
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i)) := by
  let pE : ENNReal := ENNReal.ofReal p
  have hp_nonneg : 0 ≤ p := le_trans zero_le_one hp
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE_toReal : pE.toReal = p := ENNReal.toReal_ofReal hp_nonneg
  have hpE_pos : 0 < pE.toReal := by
    simpa [hpE_toReal] using hp_pos
  letI : Fact (1 ≤ pE) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  let toPiLp : (Coord → ℝ) →L[ℝ] @PiLp pE Coord (fun _ => ℝ) :=
    (PiLp.continuousLinearEquiv pE ℝ (fun _ : Coord => ℝ)).symm.toContinuousLinearMap
  let shiftedToPiLp : (Coord → ℝ) →ᵃ[ℝ] @PiLp pE Coord (fun _ => ℝ) :=
    { toFun := fun y => toPiLp (fun i => y i - ideal i)
      linear := toPiLp.toLinearMap
      map_vadd' := by
        intro y v
        ext i
        simp [toPiLp, PiLp.toLp_apply, add_sub_assoc] }
  have hconv :
      ConvexOn ℝ Set.univ
        (fun z : @PiLp pE Coord (fun _ => ℝ) => ‖z‖) :=
    convexOn_univ_norm
  have hcomp := hconv.comp_affineMap shiftedToPiLp
  have hfun :
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i)) =
      (fun y : Coord → ℝ => ‖shiftedToPiLp y‖) := by
    funext y
    calc
      AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal i)
          = AppliedModelingLib.FiniteDimensionalNorms.lp pE.toReal
              (fun i => y i - ideal i) := by rw [hpE_toReal]
      _ = ‖(WithLp.toLp pE (fun i => y i - ideal i) :
              @PiLp pE Coord (fun _ => ℝ))‖ := by
            exact AppliedModelingLib.FiniteDimensionalNorms.lp_toReal_eq_piLp_norm
              pE hpE_pos (fun i => y i - ideal i)
      _ = ‖shiftedToPiLp y‖ := by
            rfl
  simpa [hfun, shiftedToPiLp, Function.comp_def, Set.preimage_univ] using hcomp

/--
Specialized Lemma 3-to-SSGM bridge: once convexity of the finite `Lp` cost is
available, the source candidate gradient is a finite subgradient at every point
away from coordinate equalities.
-/
theorem finiteSubgradientAt_lpCostGradientCandidate_of_convexOn
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {x ideal : Coord → ℝ}
    (hcoord : ∀ i, x i ≠ ideal i)
    (hconv :
      ConvexOn ℝ Set.univ
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - ideal i))) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      x
      (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  have hd : ∀ i, (fun j => x j - ideal j) i ≠ 0 := by
    intro i
    exact sub_ne_zero.mpr (hcoord i)
  have hbase :
      HasFDerivAt
        (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (fun i => x i - ideal i) :=
    hasFDerivAt_lpCostGradientCandidate hp hd
  have hderiv :
      HasFDerivAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - ideal i))
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i))) x := by
    simpa [Function.comp_def] using
      (hasFDerivAt_comp_sub (𝕜 := ℝ)
        (f := fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.lp p y)
        (f' := AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (lpCostGradientCandidate p (fun i => x i - ideal i)))
        (x := x) ideal).mpr hbase
  exact finiteSubgradientAt_of_convexOn_univ_hasFDerivAt hconv hderiv

/--
Lemma 3-to-SSGM bridge with the convexity premise discharged by the finite
`PiLp` norm interpretation.
-/
theorem finiteSubgradientAt_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p : ℝ} (hp : 1 < p) {x ideal : Coord → ℝ}
    (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - ideal i))
      x
      (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  exact finiteSubgradientAt_lpCostGradientCandidate_of_convexOn
    hp hcoord (convexOn_univ_finiteCoordinate_lp_cost hp.le ideal)

theorem finiteSubgradientAt_l2DistanceGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x ideal : Coord → ℝ}
    (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ => finiteCoordinateDistance SourceNorm.l2 y ideal)
      x
      (lpCostGradientCandidate 2 (fun i => x i - ideal i)) := by
  have hp : (1 : ℝ) < 2 := by norm_num
  have hcost :
      (fun y : Coord → ℝ => finiteCoordinateDistance SourceNorm.l2 y ideal) =
        fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp 2 (fun i => y i - ideal i) := by
    funext y
    rw [finiteCoordinateDistance_l2,
      finiteDimensionalNorms_l2_eq_lp_two]
  rw [hcost]
  exact finiteSubgradientAt_lpCostGradientCandidate
    (p := (2 : ℝ)) hp hcoord

/--
The Euclidean cost direction normalized by the full Euclidean distance.  Unlike
the general finite-`Lp` coordinate formula, this `p = 2` specialization is
defined and differentiable whenever the two points differ in at least one
coordinate.
-/
noncomputable def l2DistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord]
    (x ideal : Coord → ℝ) : Coord → ℝ :=
  fun i => (x i - ideal i) /
    AppliedModelingLib.FiniteDimensionalNorms.l2 (fun j => x j - ideal j)

/-- At the Euclidean endpoint, the general finite-`Lp` candidate simplifies to the normalized `L2` direction. -/
theorem lpCostGradientCandidate_two_eq_l2DistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord]
    (x ideal : Coord → ℝ) :
    lpCostGradientCandidate 2 (fun i => x i - ideal i) =
      l2DistanceNormalizedGradient x ideal := by
  rw [lpCostGradientCandidate_eq_source_formula (by norm_num : (0 : ℝ) < 2)]
  ext i
  rw [← finiteDimensionalNorms_l2_eq_lp_two]
  norm_num
  unfold l2DistanceNormalizedGradient
  by_cases hzero : x i - ideal i = 0
  · simp [hzero]
  · have habs : |x i - ideal i| ≠ 0 := abs_ne_zero.mpr hzero
    have hnumerator : |x i - ideal i| *
        ((x i - ideal i) / |x i - ideal i|) = x i - ideal i := by
      field_simp [habs]
    rw [hnumerator]

/--
Away from its ideal point, the normalized Euclidean direction is a subgradient
of the finite-coordinate Euclidean distance.
-/
theorem finiteSubgradientAt_l2DistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x ideal : Coord → ℝ}
    (hne : ∃ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ => finiteCoordinateDistance SourceNorm.l2 y ideal)
      x (l2DistanceNormalizedGradient x ideal) := by
  have hconvLp :
      ConvexOn ℝ Set.univ
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp 2 (fun i => y i - ideal i)) :=
    convexOn_univ_finiteCoordinate_lp_cost (p := (2 : ℝ)) (by norm_num) ideal
  have hconv :
      ConvexOn ℝ Set.univ
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i)) := by
    rw [show (fun y : Coord → ℝ =>
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i)) =
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp 2 (fun i => y i - ideal i)) by
      funext y
      exact finiteDimensionalNorms_l2_eq_lp_two _]
    exact hconvLp
  have hbase :
      HasFDerivAt
        (fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.l2 y)
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => (x i - ideal i) /
            AppliedModelingLib.FiniteDimensionalNorms.l2 (fun j => x j - ideal j)))
        (fun i => x i - ideal i) := by
    apply AppliedModelingLib.FiniteDimensionalNorms.hasFDerivAt_l2
    simpa only [sub_ne_zero] using hne
  have hderiv :
      HasFDerivAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i))
        (AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (l2DistanceNormalizedGradient x ideal)) x := by
    simpa [l2DistanceNormalizedGradient, Function.comp_def] using
      (hasFDerivAt_comp_sub (𝕜 := ℝ)
        (f := fun y : Coord → ℝ => AppliedModelingLib.FiniteDimensionalNorms.l2 y)
        (f' := AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => (x i - ideal i) /
            AppliedModelingLib.FiniteDimensionalNorms.l2 (fun j => x j - ideal j)))
        (x := x) ideal).mpr hbase
  change FiniteSubgradientAt
    (fun y : Coord → ℝ =>
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => y i - ideal i))
    x (l2DistanceNormalizedGradient x ideal)
  exact finiteSubgradientAt_of_convexOn_univ_hasFDerivAt hconv hderiv

/-- The Euclidean distance between the restrictions of two vectors to a finite coordinate block. -/
noncomputable def finiteCoordinateBlockL2Distance
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) : ℝ :=
  AppliedModelingLib.FiniteDimensionalNorms.l2
    (fun i : {i : Coord // i ∈ block} => x i - ideal i)

/-- Restricting a finite-coordinate Euclidean distance to a coordinate block cannot increase it. -/
theorem finiteCoordinateBlockL2Distance_le_l2
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) :
    finiteCoordinateBlockL2Distance block x ideal ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => x i - ideal i) := by
  unfold finiteCoordinateBlockL2Distance AppliedModelingLib.FiniteDimensionalNorms.l2
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
  apply Real.sqrt_le_sqrt
  calc
    (∑ i : {i : Coord // i ∈ block}, (x i - ideal i) ^ 2) =
        ∑ i ∈ block, (x i - ideal i) ^ 2 :=
      (Finset.sum_subtype (p := fun i => i ∈ block) block
        (by intro i; rfl) (fun i => (x i - ideal i) ^ 2)).symm
    _ ≤ ∑ i ∈ (Finset.univ : Finset Coord), (x i - ideal i) ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ block)
        (fun i _ _ => sq_nonneg (x i - ideal i))

/--
The normalized Euclidean direction on a finite coordinate block, extended by
zero outside that block.
-/
noncomputable def l2BlockDistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) : Coord → ℝ :=
  by
    classical
    exact fun i => if i ∈ block then
      (x i - ideal i) / finiteCoordinateBlockL2Distance block x ideal
    else 0

theorem l2BlockDistanceNormalizedGradient_eq_subtype
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) (i : {i : Coord // i ∈ block}) :
    l2BlockDistanceNormalizedGradient block x ideal i =
      l2DistanceNormalizedGradient
        (fun j : {j : Coord // j ∈ block} => x j)
        (fun j : {j : Coord // j ∈ block} => ideal j) i := by
  simp [l2BlockDistanceNormalizedGradient, finiteCoordinateBlockL2Distance,
    l2DistanceNormalizedGradient]

theorem coordinateLinearFunctional_l2BlockDistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal d : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
      (l2BlockDistanceNormalizedGradient block x ideal) d =
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
        (l2DistanceNormalizedGradient
          (fun j : {j : Coord // j ∈ block} => x j)
          (fun j : {j : Coord // j ∈ block} => ideal j))
        (fun j : {j : Coord // j ∈ block} => d j) := by
  classical
  rw [coordinateLinearFunctional_apply, coordinateLinearFunctional_apply]
  calc
    (∑ i : Coord, l2BlockDistanceNormalizedGradient block x ideal i * d i) =
        ∑ i ∈ block, l2BlockDistanceNormalizedGradient block x ideal i * d i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ block)
      intro i _hiBlock hiNotBlock
      simp [l2BlockDistanceNormalizedGradient, hiNotBlock]
    _ = ∑ i : {i : Coord // i ∈ block},
        l2BlockDistanceNormalizedGradient block x ideal i * d i :=
      Finset.sum_subtype block (by simp) _
    _ = ∑ i : {i : Coord // i ∈ block},
        l2DistanceNormalizedGradient
          (fun j : {j : Coord // j ∈ block} => x j)
          (fun j : {j : Coord // j ∈ block} => ideal j) i * d i := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [l2BlockDistanceNormalizedGradient_eq_subtype]

/--
Away from its block-restricted ideal point, the zero-extended normalized
Euclidean block direction is a subgradient of the corresponding block
distance.
-/
theorem finiteSubgradientAt_blockL2DistanceNormalizedGradient
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ)
    (hne : ∃ i, i ∈ block ∧ x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ => finiteCoordinateBlockL2Distance block y ideal)
      x (l2BlockDistanceNormalizedGradient block x ideal) := by
  rcases hne with ⟨i, hi, hxi⟩
  letI : Nonempty {i : Coord // i ∈ block} := ⟨⟨i, hi⟩⟩
  let xBlock : {i : Coord // i ∈ block} → ℝ := fun j => x j
  let idealBlock : {i : Coord // i ∈ block} → ℝ := fun j => ideal j
  have hneBlock : ∃ j : {i : Coord // i ∈ block}, xBlock j ≠ idealBlock j :=
    ⟨⟨i, hi⟩, hxi⟩
  have hbase := finiteSubgradientAt_l2DistanceNormalizedGradient
    (Coord := {i : Coord // i ∈ block}) (x := xBlock) (ideal := idealBlock) hneBlock
  intro y
  simpa only [finiteCoordinateBlockL2Distance, xBlock, idealBlock,
    coordinateLinearFunctional_l2BlockDistanceNormalizedGradient] using
    hbase (fun i : {i : Coord // i ∈ block} => y i)

theorem l2BlockDistanceNormalizedGradient_eq_zero_of_not_mem
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) {i : Coord}
    (hi : i ∉ block) :
    l2BlockDistanceNormalizedGradient block x ideal i = 0 := by
  simp [l2BlockDistanceNormalizedGradient, hi]

/--
The zero-extended block direction has the same Euclidean quantity as the
normalized direction on the corresponding subtype of coordinates.
-/
theorem l2_l2BlockDistanceNormalizedGradient_eq_subtype
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l2BlockDistanceNormalizedGradient block x ideal) =
      AppliedModelingLib.FiniteDimensionalNorms.l2
        (l2DistanceNormalizedGradient
          (fun j : {j : Coord // j ∈ block} => x j)
          (fun j : {j : Coord // j ∈ block} => ideal j)) := by
  classical
  unfold AppliedModelingLib.FiniteDimensionalNorms.l2 AppliedModelingLib.FiniteDimensionalNorms.l2Sq
  congr 1
  calc
    (∑ i : Coord, l2BlockDistanceNormalizedGradient block x ideal i ^ 2) =
        ∑ i ∈ block, l2BlockDistanceNormalizedGradient block x ideal i ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ block)
      intro i _hiBlock hiNotBlock
      simp [l2BlockDistanceNormalizedGradient, hiNotBlock]
    _ = ∑ i : {i : Coord // i ∈ block},
        l2BlockDistanceNormalizedGradient block x ideal i ^ 2 :=
      Finset.sum_subtype block (by simp) _
    _ = ∑ i : {i : Coord // i ∈ block},
        l2DistanceNormalizedGradient
          (fun j : {j : Coord // j ∈ block} => x j)
          (fun j : {j : Coord // j ∈ block} => ideal j) i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [l2BlockDistanceNormalizedGradient_eq_subtype]

/-- Zero-extended normalized directions on pairwise-disjoint coordinate blocks are disjoint. -/
theorem l2BlockDistanceNormalizedGradients_coordinatewise_disjoint
    {Coord Component : Type*} [Fintype Coord]
    (components : Finset Component) (block : Component → Finset Coord)
    (x : Coord → ℝ) (ideal : Component → Coord → ℝ)
    (hblocks : ∀ k l, k ∈ components → l ∈ components → k ≠ l →
      Disjoint (block k) (block l)) :
    ∀ i k l, k ∈ components → l ∈ components → k ≠ l →
      l2BlockDistanceNormalizedGradient (block k) x (ideal k) i = 0 ∨
        l2BlockDistanceNormalizedGradient (block l) x (ideal l) i = 0 := by
  intro i k l hk hl hkl
  by_cases hik : i ∈ block k
  · right
    apply l2BlockDistanceNormalizedGradient_eq_zero_of_not_mem
    intro hil
    exact (Finset.disjoint_left.mp (hblocks k l hk hl hkl)) hik hil
  · left
    exact l2BlockDistanceNormalizedGradient_eq_zero_of_not_mem _ _ _ hik

/-- The exact finite Model A response for an `L2` query ball. -/
noncomputable def l2BallResponse
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  if finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r then ideal else
    fun i => center i - r * l2DistanceNormalizedGradient center ideal i

/-- Outside the open ideal-containing ball, the exact response has the displayed radial form. -/
theorem l2BallResponse_eq_radial_of_not_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (houtside : ¬ finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r) :
    l2BallResponse center ideal r =
      fun i => center i - r * l2DistanceNormalizedGradient center ideal i := by
  rw [l2BallResponse, if_neg houtside]

/-- A nonzero normalized finite-coordinate Euclidean direction has norm one. -/
theorem l2DistanceNormalizedGradient_l2_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ}
    (hne : ∃ i, center i ≠ ideal i) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l2DistanceNormalizedGradient center ideal) = 1 := by
  have hpos : 0 < AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => center i - ideal i) := by
    apply AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero
    simpa only [sub_ne_zero] using hne
  unfold l2DistanceNormalizedGradient
  have hrewrite :
      (fun i => (center i - ideal i) /
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun j => center j - ideal j)) =
        (fun i => (AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun j => center j - ideal j))⁻¹ * (center i - ideal i)) := by
    funext i
    rw [div_eq_inv_mul]
  rw [hrewrite, AppliedModelingLib.FiniteDimensionalNorms.normL2_smul,
    abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

/-- A nonzero block-restricted Euclidean direction has full ambient `L2` quantity one. -/
theorem l2BlockDistanceNormalizedGradient_l2_eq_one
    {Coord : Type*} [Fintype Coord]
    (block : Finset Coord) (x ideal : Coord → ℝ)
    (hne : ∃ i, i ∈ block ∧ x i ≠ ideal i) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l2BlockDistanceNormalizedGradient block x ideal) = 1 := by
  rcases hne with ⟨i, hi, hxi⟩
  letI : Nonempty {i : Coord // i ∈ block} := ⟨⟨i, hi⟩⟩
  rw [l2_l2BlockDistanceNormalizedGradient_eq_subtype]
  apply l2DistanceNormalizedGradient_l2_eq_one
  exact ⟨⟨i, hi⟩, hxi⟩

/-- The radial part of the exact `L2` response remains in its query ball. -/
theorem l2BallResponse_l2_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.l2
      (l2BallResponse center ideal r) center ≤ r := by
  by_cases hinside : finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r
  · rw [l2BallResponse, if_pos hinside]
    change AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => ideal i - center i) ≤ r
    rw [AppliedModelingLib.FiniteDimensionalNorms.normL2_sub_rev]
    exact hinside
  · have hne : ∃ i, center i ≠ ideal i := by
      by_contra hne
      push Not at hne
      apply hinside
      change AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => center i - ideal i) ≤ r
      have hzero : (fun i => center i - ideal i) = 0 := by
        ext i
        simp [hne i]
      calc
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => center i - ideal i) =
            AppliedModelingLib.FiniteDimensionalNorms.l2 0 := by rw [hzero]
        _ = 0 := AppliedModelingLib.FiniteDimensionalNorms.normL2_zero
        _ ≤ r := hr
    rw [l2BallResponse, if_neg hinside]
    change AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => (center i - r * l2DistanceNormalizedGradient center ideal i) - center i) ≤ r
    have hrewrite :
        (fun i => (center i - r * l2DistanceNormalizedGradient center ideal i) - center i) =
          fun i => (-r) * l2DistanceNormalizedGradient center ideal i := by
      funext i
      ring
    rw [hrewrite, AppliedModelingLib.FiniteDimensionalNorms.normL2_smul,
      l2DistanceNormalizedGradient_l2_eq_one hne, abs_neg, abs_of_nonneg hr]
    linarith

/--
Outside the ideal-containing ball, the radial response reduces its Euclidean
cost by exactly the query radius.
-/
theorem l2BallResponse_l2_cost_eq_sub_of_not_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (houtside : ¬ finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => l2BallResponse center ideal r i - ideal i) =
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => center i - ideal i) - r := by
  have hlt : r < AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => center i - ideal i) := by
    exact lt_of_not_ge houtside
  have hpos : 0 < AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => center i - ideal i) := lt_of_le_of_lt hr hlt
  have hfactor : 0 ≤ 1 - r /
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => center i - ideal i) := by
    rw [sub_nonneg]
    exact (div_le_one₀ hpos).mpr (le_of_lt hlt)
  rw [l2BallResponse_eq_radial_of_not_distance_le houtside]
  have hrewrite :
      (fun i => (center i - r * l2DistanceNormalizedGradient center ideal i) - ideal i) =
        fun i => (1 - r /
          AppliedModelingLib.FiniteDimensionalNorms.l2 (fun j => center j - ideal j)) *
            (center i - ideal i) := by
    funext i
    unfold l2DistanceNormalizedGradient
    field_simp [hpos.ne']
    ring
  rw [hrewrite, AppliedModelingLib.FiniteDimensionalNorms.normL2_smul,
    abs_of_nonneg hfactor]
  field_simp [hpos.ne']

/-- The exact finite `L2` response minimizes Euclidean cost over its `L2` query ball. -/
theorem l2BallResponse_minimizes_l2_on_l2Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hcandidate : finiteCoordinateDistance SourceNorm.l2 candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => l2BallResponse center ideal r i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => candidate i - ideal i) := by
  by_cases hinside : finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r
  · rw [l2BallResponse, if_pos hinside]
    simpa only [sub_self, AppliedModelingLib.FiniteDimensionalNorms.normL2_zero] using
      AppliedModelingLib.FiniteDimensionalNorms.normL2_nonneg
        (fun i => candidate i - ideal i)
  · rw [l2BallResponse_l2_cost_eq_sub_of_not_distance_le hr hinside]
    have hcandidate' : AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => center i - candidate i) ≤ r := by
      rw [AppliedModelingLib.FiniteDimensionalNorms.normL2_sub_rev]
      exact hcandidate
    have htriangle := AppliedModelingLib.FiniteDimensionalNorms.normL2_add_le
      (fun i => center i - candidate i) (fun i => candidate i - ideal i)
    have hbound : AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => center i - ideal i) ≤
        r + AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => candidate i - ideal i) := by
      calc
        AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => center i - ideal i) =
            AppliedModelingLib.FiniteDimensionalNorms.l2
              (fun i => (center i - candidate i) + (candidate i - ideal i)) := by
          congr 1
          funext i
          ring
        _ ≤ AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => center i - candidate i) +
            AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => candidate i - ideal i) := htriangle
        _ ≤ r + AppliedModelingLib.FiniteDimensionalNorms.l2 (fun i => candidate i - ideal i) := by
          gcongr
    linarith

/-- The strict ideal-containing-ball event used by the finite `L2/L2` Model A argument. -/
def l2BallBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center : Coord → ℝ) (radius : ℝ) : Set (Coord → ℝ) :=
  {ideal | finiteCoordinateDistance SourceNorm.l2 center ideal < radius}

/-- A strict Euclidean ball is contained in every chosen-coordinate strict slab envelope. -/
theorem l2BallBadEvent_subset_l1LinfSlabBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center : Coord → ℝ) (radius : ℝ) :
    l2BallBadEvent center radius ⊆ l1LinfSlabBadEvent center radius := by
  intro ideal hideal
  let i : Coord := Classical.choice inferInstance
  refine ⟨i, ?_⟩
  exact (finiteCoordinateDistance_l2_coord_abs_le center ideal i).trans_lt hideal

/-- The direction encoded by the exact finite `L2` Model A response. -/
noncomputable def l2BallDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => (center i - l2BallResponse center ideal r i) / r

/-- On and outside the strict ideal-containing ball, the exact direction is the normalized Euclidean subgradient. -/
theorem l2BallResponse_eq_radial_of_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : r ≤ finiteCoordinateDistance SourceNorm.l2 center ideal) :
    l2BallResponse center ideal r =
      fun i => center i - r * l2DistanceNormalizedGradient center ideal i := by
  by_cases houtside : ¬ finiteCoordinateDistance SourceNorm.l2 center ideal ≤ r
  · exact l2BallResponse_eq_radial_of_not_distance_le houtside
  · push Not at houtside
    have heq : finiteCoordinateDistance SourceNorm.l2 center ideal = r :=
      le_antisymm houtside hgood
    rw [l2BallResponse, if_pos houtside]
    ext i
    unfold l2DistanceNormalizedGradient
    rw [show AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun j => center j - ideal j) = r by exact heq]
    field_simp [hr.ne']
    ring

/-- Off the strict ball event, the exact finite `L2` Model A direction is the ordinary sampled subgradient. -/
theorem l2BallDirection_eq_l2DistanceNormalizedGradient_of_notMem_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l2BallBadEvent center r) :
    l2BallDirection center ideal r = l2DistanceNormalizedGradient center ideal := by
  have hdistance : r ≤ finiteCoordinateDistance SourceNorm.l2 center ideal := by
    exact not_lt.mp hgood
  unfold l2BallDirection
  rw [l2BallResponse_eq_radial_of_distance_le hr hdistance]
  ext i
  field_simp [hr.ne']
  ring

/-- The exact finite `L2` Model A direction has Euclidean norm at most one. -/
theorem l2BallDirection_l2_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2 (l2BallDirection center ideal r) ≤ 1 := by
  unfold l2BallDirection
  have hrewrite :
      (fun i => (center i - l2BallResponse center ideal r i) / r) =
        fun i => r⁻¹ * (center i - l2BallResponse center ideal r i) := by
    funext i
    rw [div_eq_inv_mul]
  rw [hrewrite, AppliedModelingLib.FiniteDimensionalNorms.normL2_smul,
    abs_of_pos (inv_pos.mpr hr)]
  have hball := l2BallResponse_l2_distance_le (center := center) (ideal := ideal) hr.le
  change AppliedModelingLib.FiniteDimensionalNorms.l2
    (fun i => l2BallResponse center ideal r i - center i) ≤ r at hball
  rw [AppliedModelingLib.FiniteDimensionalNorms.normL2_sub_rev] at hball
  exact (inv_mul_le_iff₀ hr).mpr (by simpa using hball)

/-- The normalized Euclidean sampled direction has norm at most one, including at its zero convention. -/
theorem l2DistanceNormalizedGradient_l2_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l2DistanceNormalizedGradient center ideal) ≤ 1 := by
  by_cases hne : ∃ i, center i ≠ ideal i
  · rw [l2DistanceNormalizedGradient_l2_eq_one hne]
  · push Not at hne
    have hzero : l2DistanceNormalizedGradient center ideal = 0 := by
      unfold l2DistanceNormalizedGradient
      ext i
      simp [hne i]
    rw [hzero]
    simp [AppliedModelingLib.FiniteDimensionalNorms.l2,
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq]

/-- The state-dependent difference between the exact `L2` response direction and its sampled subgradient. -/
noncomputable def l2BallDirectionSubgradientPerturbation
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => l2BallDirection center ideal r i - l2DistanceNormalizedGradient center ideal i

/-- The exact `L2` perturbation vanishes off the strict ideal-containing ball event. -/
theorem l2BallDirectionSubgradientPerturbation_eq_zero_of_notMem_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l2BallBadEvent center r) :
    l2BallDirectionSubgradientPerturbation center ideal r = 0 := by
  unfold l2BallDirectionSubgradientPerturbation
  rw [l2BallDirection_eq_l2DistanceNormalizedGradient_of_notMem_badEvent hr hgood]
  ext i
  simp

/-- The exact finite `L2` perturbation has Euclidean norm at most two. -/
theorem l2BallDirectionSubgradientPerturbation_l2_le_two
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l2BallDirectionSubgradientPerturbation center ideal r) ≤ 2 := by
  unfold l2BallDirectionSubgradientPerturbation
  have htriangle := AppliedModelingLib.FiniteDimensionalNorms.normL2_add_le
    (l2BallDirection center ideal r) (fun i => -l2DistanceNormalizedGradient center ideal i)
  have hneg : AppliedModelingLib.FiniteDimensionalNorms.l2
      (fun i => -l2DistanceNormalizedGradient center ideal i) =
        AppliedModelingLib.FiniteDimensionalNorms.l2 (l2DistanceNormalizedGradient center ideal) := by
    rw [show (fun i => -l2DistanceNormalizedGradient center ideal i) =
      (fun i => (-1 : ℝ) * l2DistanceNormalizedGradient center ideal i) by
        funext i; ring,
      AppliedModelingLib.FiniteDimensionalNorms.normL2_smul]
    simp
  calc
    AppliedModelingLib.FiniteDimensionalNorms.l2
        (fun i => l2BallDirection center ideal r i -
          l2DistanceNormalizedGradient center ideal i) =
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun i => l2BallDirection center ideal r i +
            (-l2DistanceNormalizedGradient center ideal i)) := by
      congr 1
    _ ≤ AppliedModelingLib.FiniteDimensionalNorms.l2 (l2BallDirection center ideal r) +
        AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun i => -l2DistanceNormalizedGradient center ideal i) := htriangle
    _ ≤ 2 := by
      rw [hneg]
      have hd := l2BallDirection_l2_le_one (center := center) (ideal := ideal) hr
      have hg := l2DistanceNormalizedGradient_l2_le_one center ideal
      linarith

/-- The exact finite `L2` perturbation has squared Euclidean norm at most four. -/
theorem l2BallDirectionSubgradientPerturbation_l2Sq_le_four
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (l2BallDirectionSubgradientPerturbation center ideal r) ≤ 4 := by
  have h := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_sq_of_normL2_le
    (x := l2BallDirectionSubgradientPerturbation center ideal r)
    (by norm_num : (0 : ℝ) ≤ 2)
    (l2BallDirectionSubgradientPerturbation_l2_le_two hr)
  norm_num at h ⊢
  exact h

theorem unitSign_abs_eq_one {d : ℝ} (hd : d ≠ 0) :
    abs (d / |d|) = 1 := by
  have hpos : 0 < |d| := abs_pos.mpr hd
  rw [abs_div, abs_abs, div_self hpos.ne']

theorem unitSign_abs_le_one (d : ℝ) :
    abs (d / |d|) ≤ 1 := by
  by_cases hd : d = 0
  · simp [hd]
  · rw [unitSign_abs_eq_one hd]

theorem unitSign_mul_self_eq_abs {d : ℝ} (hd : d ≠ 0) :
    (d / |d|) * d = |d| := by
  have hne : |d| ≠ 0 := abs_ne_zero.mpr hd
  calc
    (d / |d|) * d = d ^ 2 / |d| := by ring
    _ = |d| ^ 2 / |d| := by rw [sq_abs]
    _ = |d| := by field_simp [hne]

theorem abs_add_unitSign_mul_sub_eq_unitSign_mul
    {d z : ℝ} (hd : d ≠ 0) :
    |d| + (d / |d|) * (z - d) = (d / |d|) * z := by
  calc
    |d| + (d / |d|) * (z - d)
        = |d| + (d / |d|) * z - (d / |d|) * d := by ring
    _ = |d| + (d / |d|) * z - |d| := by
          rw [unitSign_mul_self_eq_abs hd]
    _ = (d / |d|) * z := by ring

theorem unitSign_mul_le_abs {d z : ℝ} (hd : d ≠ 0) :
    (d / |d|) * z ≤ |z| := by
  calc
    (d / |d|) * z ≤ |(d / |d|) * z| := le_abs_self _
    _ = |z| := by
      rw [abs_mul, unitSign_abs_eq_one hd, one_mul]

theorem finiteSubgradientAt_l1Cost_unitSignCandidate
    {Coord : Type*} [Fintype Coord]
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => y i - ideal i))
      x
      (fun i => (x i - ideal i) / |x i - ideal i|) := by
  intro y
  have hlinear :
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => (x i - ideal i) / |x i - ideal i|)
          (fun i => y i - x i) =
        ∑ i : Coord,
          ((x i - ideal i) / |x i - ideal i|) * (y i - x i) := by
    simp [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional]
  rw [hlinear]
  change
    (∑ i : Coord, |x i - ideal i|) +
        (∑ i : Coord,
          ((x i - ideal i) / |x i - ideal i|) * (y i - x i)) ≤
      ∑ i : Coord, |y i - ideal i|
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _hi
  have hd : x i - ideal i ≠ 0 := sub_ne_zero.mpr (hcoord i)
  have hrewrite :
      |x i - ideal i| +
          ((x i - ideal i) / |x i - ideal i|) * (y i - x i) =
        ((x i - ideal i) / |x i - ideal i|) * (y i - ideal i) := by
    have hsub : y i - x i = (y i - ideal i) - (x i - ideal i) := by ring
    rw [hsub]
    exact abs_add_unitSign_mul_sub_eq_unitSign_mul hd
  rw [hrewrite]
  exact unitSign_mul_le_abs hd

theorem finiteCoordinateNorm_linf_l1CostUnitSign_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    finiteCoordinateNorm SourceNorm.linfty
      (fun i => (x i - ideal i) / |x i - ideal i|) = 1 := by
  rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.linf]
  exact Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset Coord))
    (H := Finset.univ_nonempty)
    (f := fun i => abs ((x i - ideal i) / |x i - ideal i|))
    (a := 1)
    (fun i _hi => unitSign_abs_eq_one (sub_ne_zero.mpr (hcoord i)))

/-- At the `L1` endpoint, the displayed finite-`Lp` direction is the unit-sign subgradient. -/
theorem lpCostGradientCandidate_one_eq_unitSign
    {Coord : Type*} [Fintype Coord] (d : Coord → ℝ) :
    lpCostGradientCandidate 1 d = fun i => d i / |d i| := by
  ext i
  simp [lpCostGradientCandidate, lpGradientCandidate]

theorem lpCostGradientCandidate_one_coord_abs_le_one
    {Coord : Type*} [Fintype Coord] (d : Coord → ℝ) (i : Coord) :
    |lpCostGradientCandidate 1 d i| ≤ 1 := by
  rw [lpCostGradientCandidate_one_eq_unitSign]
  exact unitSign_abs_le_one (d i)

/-- The `p = 1` endpoint of the displayed candidate is a subgradient of the finite `L1` cost. -/
theorem finiteSubgradientAt_lpCostGradientCandidate_one
    {Coord : Type*} [Fintype Coord]
    {x ideal : Coord → ℝ} (hcoord : ∀ i, x i ≠ ideal i) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.lp 1 (fun i => y i - ideal i))
      x
      (lpCostGradientCandidate 1 (fun i => x i - ideal i)) := by
  rw [lpCostGradientCandidate_one_eq_unitSign]
  simp_rw [AppliedModelingLib.FiniteDimensionalNorms.lp_one]
  exact finiteSubgradientAt_l1Cost_unitSignCandidate hcoord

/-- The `L1/L∞` endpoint turns Model B's normalized direction into the unit-sign update. -/
theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_one_formula
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} (hcoord : ∀ i, center i ≠ ideal i)
    (r : ℝ) (response : Coord → ℝ) :
    ModelBFiniteResponseAt SourceNorm.linfty center r
        (fun i => -lpCostGradientCandidate 1 (fun j => center j - ideal j) i)
        response ↔
      response = fun i => center i - r *
        lpCostGradientCandidate 1 (fun j => center j - ideal j) i := by
  have hnorm : finiteCoordinateNorm SourceNorm.linfty
      (fun i => -lpCostGradientCandidate 1 (fun j => center j - ideal j) i) = 1 := by
    rw [lpCostGradientCandidate_one_eq_unitSign]
    rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.linf]
    exact Finset.sup'_eq_of_forall
      (s := (Finset.univ : Finset Coord))
      (H := Finset.univ_nonempty)
      (f := fun i => abs (-((center i - ideal i) / |center i - ideal i|)))
      (a := 1)
      (fun i _hi => by
        change abs (-((center i - ideal i) / |center i - ideal i|)) = 1
        rw [abs_neg, unitSign_abs_eq_one (sub_ne_zero.mpr (hcoord i))])
  have hgradient :
      (fun i => -lpCostGradientCandidate 1 (fun j => center j - ideal j) i) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    have hzeroNorm :
        finiteCoordinateNorm SourceNorm.linfty (fun _ : Coord => (0 : ℝ)) = 0 := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.linf_zero (ι := Coord))
    exact zero_ne_one (hzeroNorm.symm.trans hnorm)
  rw [modelBFiniteResponseAt_formula,
    modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
  rw [hnorm]
  constructor <;> intro hresponse
  · rw [hresponse]
    funext i
    simp
    ring
  · rw [hresponse]
    funext i
    simp
    ring

/-- The unprojected sign step used by the source `L1/L∞` local-minimization argument. -/
noncomputable def l1LinfRawResponse
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => center i - r * ((center i - ideal i) / |center i - ideal i|)

/-- On a coordinate that does not cross its ideal point, the sign step reduces its `L1` cost by exactly its radius. -/
theorem l1LinfRawResponse_coordinate_cost
    {Coord : Type*} [Fintype Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i : Coord}
    (hrnonneg : 0 ≤ r)
    (hr : r ≤ |center i - ideal i|) :
    |l1LinfRawResponse center ideal r i - ideal i| =
      |center i - ideal i| - r := by
  by_cases hzero : center i = ideal i
  · have hrzero : r ≤ 0 := by simpa [hzero] using hr
    have : r = 0 := le_antisymm hrzero hrnonneg
    simp [l1LinfRawResponse, hzero, this]
  let d : ℝ := center i - ideal i
  have hpos : 0 < |d| := abs_pos.mpr (sub_ne_zero.mpr hzero)
  have hfactor : 0 ≤ 1 - r / |d| := by
    rw [sub_nonneg]
    exact (div_le_one₀ hpos).mpr (by simpa [d] using hr)
  change |center i - r * ((center i - ideal i) / |center i - ideal i|) - ideal i| =
    |center i - ideal i| - r
  have heq : center i - r * ((center i - ideal i) / |center i - ideal i|) - ideal i =
      (1 - r / |d|) * d := by
    dsimp [d]
    field_simp [hpos.ne']
    ring
  rw [heq, abs_mul, abs_of_nonneg hfactor]
  have hfinal : (1 - r / |d|) * |d| = |d| - r := by
    field_simp [hpos.ne']
  simpa [d] using hfinal

/-- Every sign step of nonnegative radius remains in the finite `L∞` query ball. -/
theorem l1LinfRawResponse_coordinate_distance_le
    {Coord : Type*} [Fintype Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i : Coord}
    (hr : 0 ≤ r) :
    |l1LinfRawResponse center ideal r i - center i| ≤ r := by
  simp only [l1LinfRawResponse]
  rw [sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg hr]
  calc
    r * abs ((center i - ideal i) / |center i - ideal i|) =
        abs ((center i - ideal i) / |center i - ideal i|) * r := mul_comm _ _
    _ ≤ 1 * r := mul_le_mul_of_nonneg_right (unitSign_abs_le_one _) hr
    _ = r := one_mul r

/-- Every point in the finite `L∞` ball has at least the coordinate cost reached by the sign step. -/
theorem l1Linf_coordinate_cost_lower_bound_of_linfBall
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} {i : Coord}
    (hcandidate : finiteCoordinateDistance SourceNorm.linfty candidate center ≤ r) :
    |center i - ideal i| - r ≤ |candidate i - ideal i| := by
  apply (sub_le_iff_le_add).mpr
  have hcandidate_i : |candidate i - center i| ≤ r :=
    le_trans (finiteCoordinateDistance_linf_coord_abs_le candidate center i) hcandidate
  calc
    |center i - ideal i| = |(center i - candidate i) + (candidate i - ideal i)| := by
      congr 1
      ring
    _ ≤ |center i - candidate i| + |candidate i - ideal i| := abs_add_le _ _
    _ = |candidate i - center i| + |candidate i - ideal i| := by rw [abs_sub_comm]
    _ ≤ r + |candidate i - ideal i| := by gcongr
    _ = |candidate i - ideal i| + r := by ring

/-- Equality in the coordinate lower bound uniquely identifies the sign-step coordinate. -/
theorem l1LinfRawResponse_coordinate_eq_of_cost_eq
    {Coord : Type*} [Fintype Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} {i : Coord}
    (hr : 0 ≤ r)
    (hgood : r ≤ |center i - ideal i|)
    (hcandidate : |candidate i - center i| ≤ r)
    (heq : |candidate i - ideal i| = |center i - ideal i| - r) :
    candidate i = l1LinfRawResponse center ideal r i := by
  by_cases hzero : center i = ideal i
  · have hrzero : r ≤ 0 := by simpa [hzero] using hgood
    have hr_eq_zero : r = 0 := le_antisymm hrzero hr
    have hcandidate_eq : candidate i = center i := by
      have hdiff_zero : candidate i - center i = 0 := by
        apply abs_eq_zero.mp
        simpa [hr_eq_zero] using hcandidate
      linarith
    simp [l1LinfRawResponse, hzero, hr_eq_zero, hcandidate_eq]
  let d : ℝ := center i - ideal i
  have hdne : d ≠ 0 := sub_ne_zero.mpr hzero
  have hbounds := abs_le.mp hcandidate
  rcases le_total 0 d with hd | hd
  · have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hdne)
    have habs : |center i - ideal i| = d := by
      simp [d, abs_of_nonneg hd]
    have hbelow : ideal i ≤ center i - r := by
      rw [habs] at hgood
      dsimp [d] at hgood
      linarith
    have hcandidate_above_ideal : 0 ≤ candidate i - ideal i := by
      linarith [hbounds.1]
    have hraw : l1LinfRawResponse center ideal r i = center i - r := by
      simp [l1LinfRawResponse, d, abs_of_pos hdpos, div_self hdpos.ne']
    rw [abs_of_nonneg hcandidate_above_ideal, habs] at heq
    rw [hraw]
    linarith
  · have hdneg : d < 0 := lt_of_le_of_ne hd hdne
    have habs : |center i - ideal i| = -d := by
      simp [d, abs_of_neg hdneg]
    have habove : center i + r ≤ ideal i := by
      rw [habs] at hgood
      dsimp [d] at hgood
      linarith
    have hcandidate_below_ideal : candidate i - ideal i ≤ 0 := by
      linarith [hbounds.2]
    have hsign_d : d / |d| = -1 := by
      rw [abs_of_neg hdneg]
      field_simp [hdneg.ne]
    have hsign : (center i - ideal i) / |center i - ideal i| = -1 := by
      simpa [d] using hsign_d
    have hraw : l1LinfRawResponse center ideal r i = center i + r := by
      simp [l1LinfRawResponse, hsign]
    rw [abs_of_nonpos hcandidate_below_ideal, habs] at heq
    rw [hraw]
    dsimp [d] at heq
    linarith

/-- The sign step minimizes finite `L1` distance over the full finite `L∞` ball when no coordinate crosses its ideal point. -/
theorem l1LinfRawResponse_minimizes_l1_on_linfBall
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|)
    {candidate : Coord → ℝ}
    (hcandidate : finiteCoordinateDistance SourceNorm.linfty candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l1
        (fun i => l1LinfRawResponse center ideal r i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => candidate i - ideal i) := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
  apply Finset.sum_le_sum
  intro i _hi
  rw [l1LinfRawResponse_coordinate_cost hr (hgood i)]
  exact l1Linf_coordinate_cost_lower_bound_of_linfBall hcandidate

/-- The `L1/L∞` sign response is the unique finite-ball minimizer on the good event. -/
theorem l1LinfRawResponse_eq_of_l1_cost_le_on_linfBall
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|)
    (hresponse_ball :
      finiteCoordinateDistance SourceNorm.linfty response center ≤ r)
    (hresponse_cost :
      AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => response i - ideal i) ≤
        AppliedModelingLib.FiniteDimensionalNorms.l1
          (fun i => l1LinfRawResponse center ideal r i - ideal i)) :
    response = l1LinfRawResponse center ideal r := by
  have hcoord_lower : ∀ i,
      |center i - ideal i| - r ≤ |response i - ideal i| :=
    fun i => l1Linf_coordinate_cost_lower_bound_of_linfBall hresponse_ball
  have hraw_sum :
      (∑ i : Coord, |l1LinfRawResponse center ideal r i - ideal i|) =
        ∑ i : Coord, (|center i - ideal i| - r) := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact l1LinfRawResponse_coordinate_cost hr (hgood i)
  have hsum_lower :
      (∑ i : Coord, (|center i - ideal i| - r)) ≤
        ∑ i : Coord, |response i - ideal i| := by
    apply Finset.sum_le_sum
    intro i _hi
    exact hcoord_lower i
  have hsum_upper :
      (∑ i : Coord, |response i - ideal i|) ≤
        ∑ i : Coord, (|center i - ideal i| - r) := by
    simpa only [AppliedModelingLib.FiniteDimensionalNorms.l1, hraw_sum] using hresponse_cost
  have hsum_eq :
      (∑ i : Coord, |response i - ideal i|) =
        ∑ i : Coord, (|center i - ideal i| - r) :=
    le_antisymm hsum_upper hsum_lower
  have hdelta_sum :
      (∑ i : Coord, (|response i - ideal i| - (|center i - ideal i| - r))) = 0 := by
    rw [Finset.sum_sub_distrib]
    linarith
  have hdelta_nonneg : ∀ i : Coord,
      0 ≤ |response i - ideal i| - (|center i - ideal i| - r) :=
    fun i => sub_nonneg.mpr (hcoord_lower i)
  have hcoord_eq : ∀ i : Coord,
      |response i - ideal i| = |center i - ideal i| - r := by
    intro i
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _hj => hdelta_nonneg j)).mp hdelta_sum i (Finset.mem_univ i)
    exact sub_eq_zero.mp hzero
  ext i
  apply l1LinfRawResponse_coordinate_eq_of_cost_eq hr (hgood i)
  · exact le_trans (finiteCoordinateDistance_linf_coord_abs_le response center i)
      hresponse_ball
  · exact hcoord_eq i

/-- The coordinatewise clamp of an ideal point to an `L∞` ball. -/
noncomputable def l1LinfBallResponse
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => max (center i - r) (min (center i + r) (ideal i))

/-- The coordinatewise clamp remains in its finite `L∞` ball. -/
theorem l1LinfBallResponse_linf_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.linfty
      (l1LinfBallResponse center ideal r) center ≤ r := by
  apply finiteCoordinateDistance_linf_le_of_forall_coord_abs_le
  intro i
  apply abs_le.mpr
  constructor
  · have hlow : center i - r ≤
        max (center i - r) (min (center i + r) (ideal i)) := le_max_left _ _
    change -r ≤ max (center i - r) (min (center i + r) (ideal i)) - center i
    linarith
  · have hleft : center i - r ≤ center i + r := by linarith
    have hright : min (center i + r) (ideal i) ≤ center i + r := min_le_left _ _
    have hupp : max (center i - r) (min (center i + r) (ideal i)) ≤ center i + r :=
      max_le hleft hright
    change max (center i - r) (min (center i + r) (ideal i)) - center i ≤ r
    linarith

/-- The coordinatewise clamp minimizes absolute distance to the ideal over its coordinate interval. -/
theorem l1LinfBallResponse_coordinate_cost_le
    {Coord : Type*} [Fintype Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} {i : Coord}
    (hr : 0 ≤ r)
    (hcandidate : |candidate i - center i| ≤ r) :
    |l1LinfBallResponse center ideal r i - ideal i| ≤
      |candidate i - ideal i| := by
  have hbounds := abs_le.mp hcandidate
  by_cases hlow : ideal i ≤ center i - r
  · have hclamp : l1LinfBallResponse center ideal r i = center i - r := by
      rw [l1LinfBallResponse]
      exact max_eq_left (le_trans (min_le_right _ _) hlow)
    rw [hclamp, abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  by_cases hhigh : center i + r ≤ ideal i
  · have hclamp : l1LinfBallResponse center ideal r i = center i + r := by
      rw [l1LinfBallResponse, min_eq_left hhigh]
      exact max_eq_right (by linarith)
    rw [hclamp, abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
  have hideal_lower : center i - r ≤ ideal i := le_of_not_ge hlow
  have hideal_upper : ideal i ≤ center i + r := le_of_not_ge hhigh
  have hclamp : l1LinfBallResponse center ideal r i = ideal i := by
    simp [l1LinfBallResponse, hideal_lower, hideal_upper]
  rw [hclamp, sub_self, abs_zero]
  exact abs_nonneg _

/-- The clamp is the exact finite `L1` minimizer over the finite `L∞` ball. -/
theorem l1LinfBallResponse_minimizes_l1_on_linfBall
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hcandidate : finiteCoordinateDistance SourceNorm.linfty candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l1
        (fun i => l1LinfBallResponse center ideal r i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l1 (fun i => candidate i - ideal i) := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
  apply Finset.sum_le_sum
  intro i _hi
  apply l1LinfBallResponse_coordinate_cost_le hr
  exact le_trans (finiteCoordinateDistance_linf_coord_abs_le candidate center i)
    hcandidate

/-- Outside the source slab bad event, the exact clamp equals the coordinate-sign response. -/
theorem l1LinfBallResponse_eq_l1LinfRawResponse_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|) :
    l1LinfBallResponse center ideal r = l1LinfRawResponse center ideal r := by
  apply l1LinfRawResponse_eq_of_l1_cost_le_on_linfBall hr hgood
  · exact l1LinfBallResponse_linf_distance_le hr
  · apply l1LinfBallResponse_minimizes_l1_on_linfBall hr
    apply finiteCoordinateDistance_linf_le_of_forall_coord_abs_le
    intro i
    exact l1LinfRawResponse_coordinate_distance_le hr

/--
The direction encoded by the exact coordinatewise Model A response.  For a
positive radius, Algorithm 1's raw response is `center - r * direction`; the
zero-radius convention is harmless and makes this a total finite-coordinate
function.
-/
noncomputable def l1LinfBallDirection
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => (center i - l1LinfBallResponse center ideal r i) / r

/-- The exact clamp response has the displayed Algorithm 1 step form. -/
theorem l1LinfBallResponse_eq_center_sub_radius_mul_direction
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) :
    l1LinfBallResponse center ideal r =
      fun i => center i - r * l1LinfBallDirection center ideal r i := by
  ext i
  by_cases hr : r = 0
  · subst r
    simp [l1LinfBallDirection, l1LinfBallResponse]
  · rw [l1LinfBallDirection]
    have hcancel : r * ((center i - l1LinfBallResponse center ideal r i) / r) =
        center i - l1LinfBallResponse center ideal r i := by
      rw [mul_comm, div_mul_cancel₀ _ hr]
    linarith

/-- Each coordinate of the positive-radius clamp direction has absolute value at most one. -/
theorem l1LinfBallDirection_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i : Coord} (hr : 0 < r) :
    |l1LinfBallDirection center ideal r i| ≤ 1 := by
  rw [l1LinfBallDirection, abs_div, abs_of_pos hr]
  have hball := finiteCoordinateDistance_linf_coord_abs_le
    (l1LinfBallResponse center ideal r) center i
  have hball' := le_trans hball
    (l1LinfBallResponse_linf_distance_le (center := center) (ideal := ideal) hr.le)
  rw [abs_sub_comm] at hball'
  exact (div_le_iff₀ hr).mpr (by simpa using hball')

/-- The exact Model A direction has squared Euclidean norm at most the dimension. -/
theorem l1LinfBallDirection_l2Sq_le_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (l1LinfBallDirection center ideal r) ≤
      Fintype.card Coord := by
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (l1LinfBallDirection center ideal r) (by norm_num : (0 : ℝ) ≤ 1)
    (fun i => l1LinfBallDirection_coordinate_abs_le_one (center := center)
      (ideal := ideal) (i := i) hr)
  norm_num at hnorm ⊢
  exact hnorm

/-- Outside the slab event, the exact Model A direction is the `L1` unit-sign subgradient. -/
theorem l1LinfBallDirection_eq_lpCostGradientCandidate_one_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ∀ i, r ≤ |center i - ideal i|) :
    l1LinfBallDirection center ideal r =
      lpCostGradientCandidate 1 (fun i => center i - ideal i) := by
  ext i
  rw [l1LinfBallDirection,
    l1LinfBallResponse_eq_l1LinfRawResponse_of_good hr.le hgood,
    l1LinfRawResponse,
    lpCostGradientCandidate_one_eq_unitSign]
  have habspos : 0 < |center i - ideal i| :=
    lt_of_lt_of_le hr (hgood i)
  field_simp [hr.ne', habspos.ne']
  ring

/--
Outside the named source slab event, the exact Model A direction is the
ordinary sampled `L1` subgradient.  This is the direct event-level bridge used
by the rare-perturbation argument.
-/
theorem l1LinfBallDirection_eq_lpCostGradientCandidate_one_of_notMem_slabBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l1LinfSlabBadEvent center r) :
    l1LinfBallDirection center ideal r =
      lpCostGradientCandidate 1 (fun i => center i - ideal i) := by
  apply l1LinfBallDirection_eq_lpCostGradientCandidate_one_of_good hr
  exact (notMem_l1LinfSlabBadEvent_iff center ideal r).mp hgood

/--
The exact Model A direction minus the ordinary sampled `L1` subgradient.
It vanishes off the C3-controlled coordinate-slab event, so it is the
rare state-dependent perturbation in the stochastic approximation proof.
-/
noncomputable def l1LinfBallDirectionSubgradientPerturbation
    {Coord : Type*} [Fintype Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => l1LinfBallDirection center ideal r i -
    lpCostGradientCandidate 1 (fun j => center j - ideal j) i

/-- Off the slab event, the exact Model A perturbation is zero. -/
theorem l1LinfBallDirectionSubgradientPerturbation_eq_zero_of_notMem_slabBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r)
    (hgood : ideal ∉ l1LinfSlabBadEvent center r) :
    l1LinfBallDirectionSubgradientPerturbation center ideal r = 0 := by
  unfold l1LinfBallDirectionSubgradientPerturbation
  rw [l1LinfBallDirection_eq_lpCostGradientCandidate_one_of_notMem_slabBadEvent hr hgood]
  ext i
  simp

/-- A coordinatewise difference between the exact Model A direction and a sampled `L1` subgradient is at most two. -/
theorem l1LinfBallDirection_subgradient_gap_coordinate_abs_le_two
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i : Coord} (hr : 0 < r) :
    |l1LinfBallDirection center ideal r i -
        lpCostGradientCandidate 1 (fun j => center j - ideal j) i| ≤ 2 := by
  calc
    |l1LinfBallDirection center ideal r i -
        lpCostGradientCandidate 1 (fun j => center j - ideal j) i| ≤
        |l1LinfBallDirection center ideal r i| +
          |lpCostGradientCandidate 1 (fun j => center j - ideal j) i| := by
      simpa using (abs_sub_le
        (l1LinfBallDirection center ideal r i) 0
        (lpCostGradientCandidate 1 (fun j => center j - ideal j) i))
    _ ≤ 2 := by
      have hdirection := l1LinfBallDirection_coordinate_abs_le_one
        (center := center) (ideal := ideal) (i := i) hr
      have hsubgradient := lpCostGradientCandidate_one_coord_abs_le_one
        (fun j => center j - ideal j) i
      linarith

/-- The Model A/sample-subgradient discrepancy has squared Euclidean norm at most four times dimension. -/
theorem l1LinfBallDirection_subgradient_gap_l2Sq_le_four_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (fun i => l1LinfBallDirection center ideal r i -
        lpCostGradientCandidate 1 (fun j => center j - ideal j) i) ≤
      4 * Fintype.card Coord := by
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (fun i => l1LinfBallDirection center ideal r i -
      lpCostGradientCandidate 1 (fun j => center j - ideal j) i)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun i => l1LinfBallDirection_subgradient_gap_coordinate_abs_le_two
      (center := center) (ideal := ideal) (i := i) hr)
  norm_num at hnorm ⊢
  nlinarith

/-- The rare Model A perturbation has squared Euclidean norm at most `4 * card`. -/
theorem l1LinfBallDirectionSubgradientPerturbation_l2Sq_le_four_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (l1LinfBallDirectionSubgradientPerturbation center ideal r) ≤
      4 * Fintype.card Coord := by
  simpa only [l1LinfBallDirectionSubgradientPerturbation] using
    l1LinfBallDirection_subgradient_gap_l2Sq_le_four_card
      (center := center) (ideal := ideal) hr

/-- The rare Model A perturbation has Euclidean norm at most `2 * sqrt(card)`. -/
theorem l1LinfBallDirectionSubgradientPerturbation_l2_le_two_mul_sqrt_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 < r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2
      (l1LinfBallDirectionSubgradientPerturbation center ideal r) ≤
      2 * Real.sqrt (Fintype.card Coord) := by
  apply AppliedModelingLib.FiniteDimensionalNorms.normL2_le_of_normL2Sq_le
  · positivity
  · calc
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (l1LinfBallDirectionSubgradientPerturbation center ideal r) ≤
          4 * Fintype.card Coord :=
        l1LinfBallDirectionSubgradientPerturbation_l2Sq_le_four_card hr
      _ = (2 * Real.sqrt (Fintype.card Coord)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        norm_num

/--
Projecting the exact raw Model A clamp is a finite projected SSGM update with
its displayed clamp direction.  This identity is valid on both the good and
the slab-bad event.
-/
theorem finiteProjectedSSGMUpdateAt_of_l1LinfBallResponse
    {Coord : Type*} [Fintype Coord]
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ)
    (hraw : raw = l1LinfBallResponse previous ideal radius)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (l1LinfBallDirection previous ideal radius)
      (fun _ => 0) (fun _ => 0) next := by
  unfold FiniteProjectedSSGMUpdateAt Algorithm1ProjectedUpdate at *
  rw [hproject, hraw, l1LinfBallResponse_eq_center_sub_radius_mul_direction]
  congr
  ext i
  ring

/-- The sign step has finite `L∞` distance at most its nonnegative radius. -/
theorem l1LinfRawResponse_linf_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal : Coord → ℝ} {r : ℝ} (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.linfty
      (l1LinfRawResponse center ideal r) center ≤ r := by
  apply finiteCoordinateDistance_linf_le_of_forall_coord_abs_le
  intro i
  exact l1LinfRawResponse_coordinate_distance_le hr

theorem finiteCoordinate_linf_eq_active_abs
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {d : Coord → ℝ} {i0 : Coord}
    (hmax : ∀ i, |d i| ≤ |d i0|) :
    AppliedModelingLib.FiniteDimensionalNorms.linf d = |d i0| := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.linf]
  apply le_antisymm
  · exact Finset.sup'_le
      (s := (Finset.univ : Finset Coord))
      (H := Finset.univ_nonempty)
      (f := fun i => |d i|)
      (a := |d i0|)
      (fun i _hi => hmax i)
  · exact Finset.le_sup'
      (s := (Finset.univ : Finset Coord))
      (f := fun i => |d i|)
      (Finset.mem_univ i0)

theorem finiteSubgradientAt_linfCost_singleActiveCoordinate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {x ideal : Coord → ℝ} {i0 : Coord}
    (hmax : ∀ i, |x i - ideal i| ≤ |x i0 - ideal i0|)
    (hnz : x i0 ≠ ideal i0) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      x
      (fun i => if i = i0 then
          (x i0 - ideal i0) / |x i0 - ideal i0| else 0) := by
  intro y
  let d0 : ℝ := x i0 - ideal i0
  let z0 : ℝ := y i0 - ideal i0
  have hd0 : d0 ≠ 0 := by
    exact sub_ne_zero.mpr hnz
  have hcostx :
      AppliedModelingLib.FiniteDimensionalNorms.linf
          (fun i => x i - ideal i) = |d0| := by
    exact finiteCoordinate_linf_eq_active_abs
      (d := fun i => x i - ideal i) (i0 := i0) hmax
  have hlinear :
      AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (fun i => if i = i0 then d0 / |d0| else 0)
          (fun i => y i - x i) =
        (d0 / |d0|) * (y i0 - x i0) := by
    simp [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional, d0]
  have hleft :
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => x i - ideal i) +
          AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
            (fun i => if i = i0 then
                (x i0 - ideal i0) / |x i0 - ideal i0| else 0)
            (fun i => y i - x i) =
        (d0 / |d0|) * z0 := by
    rw [hcostx]
    simpa [d0, z0] using
      (by
        rw [hlinear]
        have hsub : y i0 - x i0 = z0 - d0 := by
          simp [d0, z0]
        rw [hsub]
        exact abs_add_unitSign_mul_sub_eq_unitSign_mul hd0)
  rw [hleft]
  have hcoord : (d0 / |d0|) * z0 ≤ |z0| :=
    unitSign_mul_le_abs hd0
  have hsup :
      |z0| ≤ AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => y i - ideal i) := by
    rw [AppliedModelingLib.FiniteDimensionalNorms.linf]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset Coord))
      (f := fun i => |y i - ideal i|)
      (Finset.mem_univ i0)
  exact le_trans hcoord hsup

theorem finiteCoordinateNorm_l1_singleActiveSign_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {x ideal : Coord → ℝ} {i0 : Coord}
    (hnz : x i0 ≠ ideal i0) :
    finiteCoordinateNorm SourceNorm.l1
      (fun i => if i = i0 then
        (x i0 - ideal i0) / |x i0 - ideal i0| else 0) = 1 := by
  have hd0 : x i0 - ideal i0 ≠ 0 := sub_ne_zero.mpr hnz
  rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.l1]
  change
    (∑ i : Coord,
      abs (if i = i0 then
        (x i0 - ideal i0) / |x i0 - ideal i0| else 0)) = 1
  rw [Finset.sum_eq_single i0]
  · simp [unitSign_abs_eq_one hd0]
  · intro i _hi hne
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i0))

/-- A deterministic active coordinate attaining the finite `L∞` displacement. -/
noncomputable def linfL1ActiveCoordinate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) : Coord :=
  Classical.choose (Finset.exists_max_image (Finset.univ : Finset Coord)
    (fun i => |center i - ideal i|) Finset.univ_nonempty)

/-- The canonical active coordinate dominates every coordinate displacement. -/
theorem linfL1ActiveCoordinate_is_max
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) :
    ∀ i, |center i - ideal i| ≤
      |center (linfL1ActiveCoordinate center ideal) -
        ideal (linfL1ActiveCoordinate center ideal)| := by
  have hchoice := Classical.choose_spec
    (Finset.exists_max_image (Finset.univ : Finset Coord)
      (fun i => |center i - ideal i|) Finset.univ_nonempty)
  intro i
  exact hchoice.2 i (Finset.mem_univ i)

/-- The signed coordinate direction selected by the `L∞/L1` local argument. -/
noncomputable def linfL1SingleActiveDirection
    {Coord : Type*} [DecidableEq Coord]
    (center ideal : Coord → ℝ) (i0 : Coord) : Coord → ℝ :=
  fun i => if i = i0 then
    (center i0 - ideal i0) / |center i0 - ideal i0| else 0

/-- All coordinates attaining the finite `L∞` displacement. -/
noncomputable def linfL1ActiveCoordinates
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) : Finset Coord :=
  Finset.univ.filter (fun i =>
    |center i - ideal i| =
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun j => center j - ideal j))

/-- The deterministic active coordinate belongs to the finite active-coordinate set. -/
theorem linfL1ActiveCoordinate_mem_activeCoordinates
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) :
    linfL1ActiveCoordinate center ideal ∈ linfL1ActiveCoordinates center ideal := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  symm
  exact finiteCoordinate_linf_eq_active_abs
    (linfL1ActiveCoordinate_is_max center ideal)

/-- The number of active `L∞` coordinates is the corresponding finite indicator sum. -/
theorem linfL1ActiveCoordinates_card_eq_indicatorSum
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) :
    ((linfL1ActiveCoordinates center ideal).card : ℝ) =
      ∑ i : Coord, if |center i - ideal i| =
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun j => center j - ideal j)
        then 1 else 0 := by
  simpa [linfL1ActiveCoordinates] using
    (Finset.sum_boole (fun i : Coord => |center i - ideal i| =
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun j => center j - ideal j))
      (Finset.univ : Finset Coord)).symm

/--
The uniform average of active signed-coordinate directions.  Unlike an
arbitrary tie-break, this definition is directly Borel-measurable in finite
coordinates and remains a valid `L∞` sample-cost subgradient at ties.
-/
noncomputable def linfL1SymmetricActiveDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal : Coord → ℝ) : Coord → ℝ :=
  let active := linfL1ActiveCoordinates center ideal
  if AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => center i - ideal i) = 0 then
    fun _ => 0
  else
    fun i => if i ∈ active then
      ((center i - ideal i) / |center i - ideal i|) / (active.card : ℝ)
    else 0

/-- Off the zero-displacement case, the symmetric direction is the uniform active sum. -/
theorem linfL1SymmetricActiveDirection_eq_weighted_sum_of_linf_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ}
    (hnonzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) ≠ 0) :
    linfL1SymmetricActiveDirection center ideal = fun i =>
      (linfL1ActiveCoordinates center ideal).sum (fun j =>
        (1 / ((linfL1ActiveCoordinates center ideal).card : ℝ)) *
          linfL1SingleActiveDirection center ideal j i) := by
  classical
  let active := linfL1ActiveCoordinates center ideal
  funext i
  by_cases hi : i ∈ active
  · rw [linfL1SymmetricActiveDirection]
    simp only [if_neg hnonzero, active, if_pos hi]
    rw [Finset.sum_eq_single i]
    · simp [linfL1SingleActiveDirection]
      ring
    · intro j hj hji
      have hij : i ≠ j := Ne.symm hji
      simp [linfL1SingleActiveDirection, hij]
    · exact fun h => (h hi).elim
  · rw [linfL1SymmetricActiveDirection]
    simp only [if_neg hnonzero, active, if_neg hi]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hij : i ≠ j := by
      intro h
      apply hi
      simpa [h] using hj
    simp [linfL1SingleActiveDirection, hij]

/-- The active signed direction is a finite subgradient of the `L∞` sample cost. -/
theorem finiteSubgradientAt_linfL1SingleActiveDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 < r)
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|)
    (hnoncross : r ≤ |center i0 - ideal i0|) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center (linfL1SingleActiveDirection center ideal i0) := by
  apply finiteSubgradientAt_linfCost_singleActiveCoordinate hmax
  intro hzero
  have : r ≤ 0 := by simpa [hzero] using hnoncross
  exact (not_lt_of_ge this) hr

/--
Any coordinate attaining the finite `L∞` displacement defines a sample-cost
subgradient.  The zero-displacement case uses the zero subgradient directly,
so this statement does not require a positive query radius.
-/
theorem finiteSubgradientAt_linfL1SingleActiveDirection_of_max
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {i0 : Coord}
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center (linfL1SingleActiveDirection center ideal i0) := by
  by_cases hnz : center i0 ≠ ideal i0
  · exact finiteSubgradientAt_linfCost_singleActiveCoordinate hmax hnz
  · have hcenter : center = ideal := by
      ext i
      have hi : |center i - ideal i| = 0 := by
        apply le_antisymm
        · have hi_le : |center i - ideal i| ≤ 0 := by
            calc
              |center i - ideal i| ≤ |center i0 - ideal i0| := hmax i
              _ = 0 := by simp [not_ne_iff.mp hnz]
          exact hi_le
        · exact abs_nonneg _
      exact sub_eq_zero.mp (abs_eq_zero.mp hi)
    subst center
    intro y
    have hcost : AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => ideal i - ideal i) = 0 := by
      simp [AppliedModelingLib.FiniteDimensionalNorms.linf]
    have hdirection : linfL1SingleActiveDirection ideal ideal i0 = fun _ => 0 := by
      funext i
      simp [linfL1SingleActiveDirection]
    change AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => ideal i - ideal i) +
        AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (linfL1SingleActiveDirection ideal ideal i0) (fun i => y i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)
    rw [hcost, hdirection]
    simpa [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional] using
      (AppliedModelingLib.FiniteDimensionalNorms.linf_nonneg (fun i => y i - ideal i))

/--
Uniformly averaging the signed directions of all maximum-displacement
coordinates gives a symmetric finite subgradient of the `L∞` sample cost.
This avoids a nonmeasurable arbitrary tie-break in the stochastic route.
-/
theorem finiteSubgradientAt_linfL1SymmetricActiveDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal : Coord → ℝ) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center (linfL1SymmetricActiveDirection center ideal) := by
  classical
  let active := linfL1ActiveCoordinates center ideal
  have hactive_mem : linfL1ActiveCoordinate center ideal ∈ active := by
    simpa [active] using
      linfL1ActiveCoordinate_mem_activeCoordinates center ideal
  have hactive_nonempty : active.Nonempty := ⟨_, hactive_mem⟩
  have hcard_pos : 0 < active.card := Finset.card_pos.mpr hactive_nonempty
  have hcard_ne : (active.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcard_pos)
  by_cases hzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) = 0
  · have hcenter : center = ideal := by
      ext i
      have hi : |center i - ideal i| ≤ 0 := by
        calc
          |center i - ideal i| ≤
              |center (linfL1ActiveCoordinate center ideal) -
                ideal (linfL1ActiveCoordinate center ideal)| :=
            linfL1ActiveCoordinate_is_max center ideal i
          _ = AppliedModelingLib.FiniteDimensionalNorms.linf
              (fun j => center j - ideal j) := by
            symm
            exact finiteCoordinate_linf_eq_active_abs
              (linfL1ActiveCoordinate_is_max center ideal)
          _ = 0 := hzero
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))
    subst center
    intro y
    change AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => ideal i - ideal i) +
        AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional
          (linfL1SymmetricActiveDirection ideal ideal)
          (fun i => y i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)
    have hcost : AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => ideal i - ideal i) = 0 := by
      simp [AppliedModelingLib.FiniteDimensionalNorms.linf]
    have hdirection : linfL1SymmetricActiveDirection ideal ideal = fun _ => 0 := by
      rw [linfL1SymmetricActiveDirection]
      simp
    rw [hcost, hdirection]
    simpa [AppliedModelingLib.FiniteDimensionalNorms.coordinateLinearFunctional] using
      (AppliedModelingLib.FiniteDimensionalNorms.linf_nonneg (fun i => y i - ideal i))
  · have hcoeff : ∀ j, j ∈ active → 0 ≤ 1 / (active.card : ℝ) := by
      intro _ _
      exact div_nonneg (by norm_num) (by positivity)
    have hcomponent : ∀ j, j ∈ active →
        FiniteSubgradientAt
          (fun y : Coord → ℝ =>
            AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
          center (linfL1SingleActiveDirection center ideal j) := by
      intro j hj
      apply finiteSubgradientAt_linfL1SingleActiveDirection_of_max
      intro i
      have hjmax : |center j - ideal j| =
          AppliedModelingLib.FiniteDimensionalNorms.linf
            (fun k => center k - ideal k) := by
        change j ∈ Finset.univ.filter (fun k =>
          |center k - ideal k| =
            AppliedModelingLib.FiniteDimensionalNorms.linf
              (fun l => center l - ideal l)) at hj
        exact (Finset.mem_filter.mp hj).2
      calc
        |center i - ideal i| ≤
            AppliedModelingLib.FiniteDimensionalNorms.linf
              (fun k => center k - ideal k) :=
          by
            rw [AppliedModelingLib.FiniteDimensionalNorms.linf_eq_sup_abs]
            exact Finset.le_sup'
              (s := (Finset.univ : Finset Coord))
              (f := fun k => |center k - ideal k|)
              (Finset.mem_univ i)
        _ = |center j - ideal j| := hjmax.symm
    have hweighted := finiteSubgradientAt_finset_nonneg_weighted_sum
      active hcoeff hcomponent
    have hcost : ∀ y : Coord → ℝ,
        active.sum (fun _ =>
          (1 / (active.card : ℝ)) *
            AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i)) =
          AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i) := by
      intro y
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      field_simp
    rw [linfL1SymmetricActiveDirection_eq_weighted_sum_of_linf_ne_zero hzero]
    convert hweighted using 1
    ext y
    symm
    exact hcost y

/-- Every coordinate of the symmetric active `L∞` direction has absolute value at most one. -/
theorem linfL1SymmetricActiveDirection_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal : Coord → ℝ) (i : Coord) :
    |linfL1SymmetricActiveDirection center ideal i| ≤ 1 := by
  classical
  let active := linfL1ActiveCoordinates center ideal
  have hactive_mem : linfL1ActiveCoordinate center ideal ∈ active := by
    simpa [active] using
      linfL1ActiveCoordinate_mem_activeCoordinates center ideal
  have hcard_pos : 0 < active.card :=
    Finset.card_pos.mpr ⟨_, hactive_mem⟩
  have hcard_one : (1 : ℝ) ≤ active.card := by
    exact_mod_cast hcard_pos
  by_cases hzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun j => center j - ideal j) = 0
  · rw [linfL1SymmetricActiveDirection]
    simp [hzero]
  · rw [linfL1SymmetricActiveDirection]
    simp only [if_neg hzero]
    by_cases hi : i ∈ active
    · rw [if_pos hi]
      have hi_active : |center i - ideal i| =
          AppliedModelingLib.FiniteDimensionalNorms.linf
            (fun j => center j - ideal j) := by
        change i ∈ Finset.univ.filter (fun j =>
          |center j - ideal j| =
            AppliedModelingLib.FiniteDimensionalNorms.linf
              (fun k => center k - ideal k)) at hi
        exact (Finset.mem_filter.mp hi).2
      have hcoord_ne : center i - ideal i ≠ 0 := by
        intro hcoord
        apply hzero
        rw [← hi_active, hcoord, abs_zero]
      calc
        |((center i - ideal i) / |center i - ideal i|) /
            (active.card : ℝ)| =
            (|center i - ideal i| / |center i - ideal i|) /
              (active.card : ℝ) := by
          simp [abs_div, abs_abs]
        _ = 1 / (active.card : ℝ) := by
          rw [div_self (ne_of_gt (abs_pos.mpr hcoord_ne))]
        _ ≤ 1 := (div_le_one₀ (by positivity)).mpr hcard_one
    · rw [if_neg hi]
      norm_num

/-- Away from the ideal, the symmetric active `L∞` subgradient has `L1` norm one. -/
theorem finiteCoordinateNorm_l1_linfL1SymmetricActiveDirection_eq_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ}
    (hnonzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) ≠ 0) :
    finiteCoordinateNorm SourceNorm.l1
      (linfL1SymmetricActiveDirection center ideal) = 1 := by
  classical
  let active := linfL1ActiveCoordinates center ideal
  have hactive_mem : linfL1ActiveCoordinate center ideal ∈ active := by
    simpa [active] using
      linfL1ActiveCoordinate_mem_activeCoordinates center ideal
  have hcard_pos : 0 < active.card :=
    Finset.card_pos.mpr ⟨_, hactive_mem⟩
  rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.l1,
    linfL1SymmetricActiveDirection]
  simp only [if_neg hnonzero]
  change (∑ i : Coord,
      |if i ∈ active then
        (center i - ideal i) / |center i - ideal i| / (active.card : ℝ) else 0|) = 1
  have hterm : ∀ i ∈ active,
      |(center i - ideal i) / |center i - ideal i| / (active.card : ℝ)| =
        1 / (active.card : ℝ) := by
    intro i hi
    have hi_active : |center i - ideal i| =
        AppliedModelingLib.FiniteDimensionalNorms.linf
          (fun j => center j - ideal j) := by
      change i ∈ Finset.univ.filter (fun j =>
        |center j - ideal j| =
          AppliedModelingLib.FiniteDimensionalNorms.linf
            (fun k => center k - ideal k)) at hi
      exact (Finset.mem_filter.mp hi).2
    have hcoord_ne : center i - ideal i ≠ 0 := by
      intro hcoord
      apply hnonzero
      rw [← hi_active, hcoord, abs_zero]
    calc
      |(center i - ideal i) / |center i - ideal i| / (active.card : ℝ)| =
          (|center i - ideal i| / |center i - ideal i|) /
            (active.card : ℝ) := by
        simp [abs_div, abs_abs]
      _ = 1 / (active.card : ℝ) := by
        rw [div_self (ne_of_gt (abs_pos.mpr hcoord_ne))]
  calc
    (∑ i : Coord,
        |if i ∈ active then
          (center i - ideal i) / |center i - ideal i| / (active.card : ℝ) else 0|) =
        ∑ i : Coord, if i ∈ active then
          |(center i - ideal i) / |center i - ideal i| / (active.card : ℝ)| else 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : i ∈ active <;> simp [hi]
    _ =
        active.sum (fun i =>
          |(center i - ideal i) / |center i - ideal i| / (active.card : ℝ)|) := by
      rw [← Finset.sum_filter]
      simp
    _ = active.sum (fun _ => 1 / (active.card : ℝ)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = 1 := by
      rw [Finset.sum_const]
      simp only [nsmul_eq_mul]
      field_simp [Nat.ne_of_gt hcard_pos]

/--
For a nonzero `L∞` displacement, negating the symmetric cost subgradient
already has unit `L1` norm, so Model B's normalized utility direction is
exactly that negative subgradient.
-/
theorem modelBFiniteNormalizedDirection_l1_neg_linfL1SymmetricActiveDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ}
    (hnonzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) ≠ 0) :
    modelBFiniteNormalizedDirection SourceNorm.l1
      (fun i => -linfL1SymmetricActiveDirection center ideal i) =
      fun i => -linfL1SymmetricActiveDirection center ideal i := by
  have hnorm : finiteCoordinateNorm SourceNorm.l1
      (fun i => -linfL1SymmetricActiveDirection center ideal i) = 1 := by
    rw [finiteCoordinateNorm, AppliedModelingLib.FiniteDimensionalNorms.l1]
    simpa only [abs_neg] using
      finiteCoordinateNorm_l1_linfL1SymmetricActiveDirection_eq_one hnonzero
  have hgradient :
      (fun i => -linfL1SymmetricActiveDirection center ideal i) ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    have hzeroNorm :
        finiteCoordinateNorm SourceNorm.l1 (fun _ : Coord => (0 : ℝ)) = 0 := by
      simpa [finiteCoordinateNorm] using
        (AppliedModelingLib.FiniteDimensionalNorms.normL1_zero (ι := Coord))
    exact zero_ne_one (hzeroNorm.symm.trans hnorm)
  rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
  rw [hnorm]
  funext i
  ring

/--
The one-coordinate local step in the corrected `L∞/L1` Model A argument.
Its exact optimality requires the active-coordinate margin hypotheses proved
below; when a crossing or a near tie occurs, the paper permits a different
exact local minimizer.
-/
noncomputable def linfL1SingleActiveRawResponse
    {Coord : Type*} [DecidableEq Coord]
    (center ideal : Coord → ℝ) (r : ℝ) (i0 : Coord) : Coord → ℝ :=
  fun i => center i - r * linfL1SingleActiveDirection center ideal i0 i

/--
The corrected good event for the `L∞/L1` local argument: the selected maximum
does not cross its ideal and is separated from every competing displacement by
the query radius.
-/
def LinfL1CorrectedGood
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Prop :=
  r ≤ |center (linfL1ActiveCoordinate center ideal) -
    ideal (linfL1ActiveCoordinate center ideal)| ∧
  ∀ i, i ≠ linfL1ActiveCoordinate center ideal →
    |center i - ideal i| ≤
      |center (linfL1ActiveCoordinate center ideal) -
        ideal (linfL1ActiveCoordinate center ideal)| - r

/-- The complement of the corrected `L∞/L1` local good event. -/
def linfL1CorrectedBadEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center : Coord → ℝ) (r : ℝ) : Set (Coord → ℝ) :=
  {ideal | ¬ LinfL1CorrectedGood center ideal r}

/-- A broad pairwise near-tie event for finite `L∞` displacements. -/
def linfL1NearTieBadEvent
    {Coord : Type*} (center : Coord → ℝ) (r : ℝ) : Set (Coord → ℝ) :=
  {ideal | ∃ i j, i ≠ j ∧
    abs (abs (center i - ideal i) - abs (center j - ideal j)) < r}

/-- The finite pairwise near-tie envelope is Borel measurable. -/
theorem measurableSet_linfL1NearTieBadEvent
    {Coord : Type*} [Fintype Coord]
    (center : Coord → ℝ) (radius : ℝ) :
    MeasurableSet (linfL1NearTieBadEvent center radius) := by
  classical
  change MeasurableSet {ideal : Coord → ℝ | ∃ i j, i ≠ j ∧
    abs (abs (center i - ideal i) - abs (center j - ideal j)) < radius}
  rw [show {ideal : Coord → ℝ | ∃ i j, i ≠ j ∧
      abs (abs (center i - ideal i) - abs (center j - ideal j)) < radius} =
      ⋃ i : Coord, ⋃ j : Coord, {ideal : Coord → ℝ | i ≠ j ∧
        abs (abs (center i - ideal i) - abs (center j - ideal j)) < radius} by
    ext ideal
    simp]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hdiff : Measurable (fun ideal : Coord → ℝ =>
        abs (center i - ideal i) - abs (center j - ideal j)) :=
      ((measurable_const.sub (measurable_pi_apply i)).abs).sub
        ((measurable_const.sub (measurable_pi_apply j)).abs)
    rw [show {ideal : Coord → ℝ | i ≠ j ∧
        abs (abs (center i - ideal i) - abs (center j - ideal j)) < radius} =
        {ideal : Coord → ℝ |
          abs (abs (center i - ideal i) - abs (center j - ideal j)) < radius} by
      ext ideal
      simp [hij]]
    exact (measurableSet_Iio : MeasurableSet (Set.Iio radius)).preimage hdiff.abs

/-- A near tie in absolute values is a small difference strip or a small sum strip. -/
theorem abs_abs_sub_abs_lt_implies_abs_sub_or_abs_add_lt
    {u v r : ℝ} (h : abs (abs u - abs v) < r) :
    |u - v| < r ∨ |u + v| < r := by
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · left
    simpa [abs_of_nonneg hu, abs_of_nonneg hv] using h
  · right
    rw [abs_of_nonneg hu, abs_of_nonpos hv] at h
    rw [show u - -v = u + v by ring] at h
    exact h
  · right
    rw [abs_of_nonpos hu, abs_of_nonneg hv] at h
    rw [show -u - v = -(u + v) by ring, abs_neg] at h
    exact h
  · left
    rw [abs_of_nonpos hu, abs_of_nonpos hv] at h
    rw [show -u - -v = -(u - v) by ring, abs_neg] at h
    exact h

/--
The pairwise near-tie event is contained in the union of closed linear slabs
for coordinate differences and coordinate sums.  This is the measurable
bounded-density envelope used by the corrected C3 argument.
-/
theorem linfL1NearTieBadEvent_subset_linearSlabs
    {Coord : Type*} (center : Coord → ℝ) (r : ℝ) :
    linfL1NearTieBadEvent center r ⊆
      {ideal : Coord → ℝ | ∃ i j, i ≠ j ∧
        (ideal i - ideal j ∈ Set.Icc (center i - center j - r)
          (center i - center j + r) ∨
          ideal i + ideal j ∈ Set.Icc (center i + center j - r)
            (center i + center j + r))} := by
  intro ideal hideal
  rcases hideal with ⟨i, j, hij, hnear⟩
  rcases abs_abs_sub_abs_lt_implies_abs_sub_or_abs_add_lt hnear with hdiff | hsum
  · refine ⟨i, j, hij, Or.inl ?_⟩
    have hbounds := abs_lt.mp hdiff
    constructor <;> linarith
  · refine ⟨i, j, hij, Or.inr ?_⟩
    have hbounds := abs_lt.mp hsum
    constructor <;> linarith

/--
Closed bounded-box envelope for the corrected pairwise near-tie event.  Each
pair contributes a difference slab and a sum slab, which are both generic
linear-coordinate slabs after a volume-preserving shear.
-/
def linfL1LinearTieSlabBadRegion
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (boxLo boxHi center : Coord → ℝ) (r : ℝ) : Set (Coord → ℝ) :=
  ⋃ i ∈ (Finset.univ : Finset Coord), ⋃ j ∈ (Finset.univ.erase i),
    {ideal : Coord → ℝ |
      ideal ∈ Set.Icc boxLo boxHi ∧
        (ideal i - ideal j ∈ Set.Icc (center i - center j - r)
          (center i - center j + r) ∨
          ideal i + ideal j ∈ Set.Icc (center i + center j - r)
            (center i + center j + r))}

/-- The bounded near-tie event is contained in its closed linear-slab envelope. -/
theorem inter_linfL1NearTieBadEvent_subset_linearTieSlabBadRegion
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (boxLo boxHi center : Coord → ℝ) (r : ℝ) :
    (Set.Icc boxLo boxHi ∩ linfL1NearTieBadEvent center r) ⊆
      linfL1LinearTieSlabBadRegion boxLo boxHi center r := by
  intro ideal hideal
  rcases linfL1NearTieBadEvent_subset_linearSlabs center r hideal.2 with
    ⟨i, j, hij, hslab⟩
  rw [linfL1LinearTieSlabBadRegion]
  refine Set.mem_iUnion.2 ⟨i, ?_⟩
  refine Set.mem_iUnion.2 ⟨Finset.mem_univ i, ?_⟩
  refine Set.mem_iUnion.2 ⟨j, ?_⟩
  refine Set.mem_iUnion.2 ⟨Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩, ?_⟩
  exact ⟨hideal.1, hslab⟩

/--
The corrected exceptional event is covered by a coordinate crossing slab or a
pairwise near-tie event.  This is the source correction's deterministic C3
reduction.
-/
theorem linfL1CorrectedBadEvent_subset_slab_union_nearTie
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center : Coord → ℝ) (r : ℝ) :
    linfL1CorrectedBadEvent center r ⊆
      l1LinfSlabBadEvent center r ∪ linfL1NearTieBadEvent center r := by
  intro ideal hbad
  by_cases hslab : ideal ∈ l1LinfSlabBadEvent center r
  · exact Or.inl hslab
  right
  have hcross : ∀ i, r ≤ |center i - ideal i| :=
    (notMem_l1LinfSlabBadEvent_iff center ideal r).mp hslab
  let i0 : Coord := linfL1ActiveCoordinate center ideal
  have hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0| := by
    simpa [i0] using linfL1ActiveCoordinate_is_max center ideal
  by_contra hnotie
  have hmargin : ∀ i, i ≠ i0 → |center i - ideal i| ≤
      |center i0 - ideal i0| - r := by
    intro i hi
    by_contra hnotle
    have hlt : |center i0 - ideal i0| < |center i - ideal i| + r := by
      linarith
    have hdiff : abs (abs (center i0 - ideal i0) -
        abs (center i - ideal i)) < r := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hmax i))]
      linarith
    exact hnotie ⟨i0, i, hi.symm, hdiff⟩
  exact hbad ⟨hcross i0, hmargin⟩

/-- The finite nonempty coordinate subsets used by the exact `L∞/L1` water-filling level. -/
noncomputable def linfL1WaterfillSubsets
    (Coord : Type*) [Fintype Coord] : Finset (Finset Coord) := by
  classical
  exact ((Finset.univ : Finset Coord).powerset.erase ∅)

/-- There is always a nonempty coordinate subset in the water-filling maximum. -/
theorem linfL1WaterfillSubsets_nonempty
    (Coord : Type*) [Fintype Coord] [Nonempty Coord] :
    (linfL1WaterfillSubsets Coord).Nonempty := by
  classical
  let i0 : Coord := Classical.choice inferInstance
  refine ⟨{i0}, Finset.mem_erase.mpr ⟨Finset.singleton_ne_empty _, ?_⟩⟩
  simp

/--
The finite water-filling level for minimizing `L∞` distance to `ideal` over an
`L1` ball around `center`.  It is the maximum subset-average residual, clipped
at zero; this finite formula avoids a nonmeasurable argmin choice.
-/
noncomputable def linfL1WaterfillLevel
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : ℝ :=
  max 0 ((linfL1WaterfillSubsets Coord).sup'
    (linfL1WaterfillSubsets_nonempty Coord)
    fun A => ((∑ i ∈ A, |center i - ideal i|) - r) / (A.card : ℝ))

/-- The finite water-filling level is Borel in the current state and ideal. -/
theorem measurable_linfL1WaterfillLevel
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (r : ℝ) :
    Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
      linfL1WaterfillLevel z.1 z.2 r) := by
  classical
  unfold linfL1WaterfillLevel
  apply measurable_const.max
  have hsup := Finset.measurable_sup' (α := ℝ) (δ := (Coord → ℝ) × (Coord → ℝ))
    (s := linfL1WaterfillSubsets Coord)
    (f := fun A z => ((∑ i ∈ A, |z.1 i - z.2 i|) - r) / (A.card : ℝ))
    (linfL1WaterfillSubsets_nonempty Coord) (by
      intro A _hA
      have hsum : Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
          ∑ i ∈ A, |z.1 i - z.2 i|) :=
        Finset.measurable_sum A fun i _ =>
          (((measurable_pi_apply i).comp measurable_fst).sub
            ((measurable_pi_apply i).comp measurable_snd)).abs
      exact (hsum.sub measurable_const).div measurable_const)
  convert hsup using 1
  funext z
  exact (Finset.sup'_apply
    (C := fun _ : (Coord → ℝ) × (Coord → ℝ) => ℝ)
    (linfL1WaterfillSubsets_nonempty Coord)
    (fun A z => ((∑ i ∈ A, |z.1 i - z.2 i|) - r) / (A.card : ℝ)) z).symm

/-- The exact water-filling raw response for the source `L∞/L1` Model A endpoint. -/
noncomputable def linfL1WaterfillRawResponse
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => center i -
    ((center i - ideal i) / |center i - ideal i|) *
      max (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0

/-- The exact water-filling raw response is Borel in state and ideal. -/
theorem measurable_linfL1WaterfillRawResponse
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (r : ℝ) :
    Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
      linfL1WaterfillRawResponse z.1 z.2 r) := by
  apply measurable_pi_lambda
  intro i
  unfold linfL1WaterfillRawResponse
  have hdisplacement : Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
      z.1 i - z.2 i) :=
    ((measurable_pi_apply i).comp measurable_fst).sub
      ((measurable_pi_apply i).comp measurable_snd)
  have hamount : Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
      max (|z.1 i - z.2 i| - linfL1WaterfillLevel z.1 z.2 r) 0) :=
    (hdisplacement.abs.sub (measurable_linfL1WaterfillLevel r)).max measurable_const
  exact ((measurable_pi_apply i).comp measurable_fst).sub
    ((hdisplacement.div hdisplacement.abs).mul hamount)

/-- The water-filling level is nonnegative by construction. -/
theorem linfL1WaterfillLevel_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) :
    0 ≤ linfL1WaterfillLevel center ideal r := by
  unfold linfL1WaterfillLevel
  exact le_max_left _ _

/-- Every nonempty subset's residual average is bounded by the water-filling level. -/
theorem linfL1WaterfillSubset_average_le_level
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) (A : Finset Coord)
    (hA : A ∈ linfL1WaterfillSubsets Coord) :
    ((∑ i ∈ A, |center i - ideal i|) - r) / (A.card : ℝ) ≤
      linfL1WaterfillLevel center ideal r := by
  unfold linfL1WaterfillLevel
  exact (Finset.le_sup' (f := fun B : Finset Coord =>
    ((∑ i ∈ B, |center i - ideal i|) - r) / (B.card : ℝ)) hA).trans
      (le_max_right _ _)

/-- Coordinates whose displacement remains above the water-filling level. -/
noncomputable def linfL1WaterfillActiveCoordinates
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Finset Coord := by
  classical
  exact Finset.univ.filter (fun i =>
    linfL1WaterfillLevel center ideal r < |center i - ideal i|)

/-- The total water-filling motion is the residual sum over its active coordinates. -/
theorem linfL1Waterfill_sum_amount_eq_active_sum
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) :
    (∑ i : Coord, max
      (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0) =
      ∑ i ∈ linfL1WaterfillActiveCoordinates center ideal r,
        (|center i - ideal i| - linfL1WaterfillLevel center ideal r) := by
  classical
  rw [linfL1WaterfillActiveCoordinates, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hactive : linfL1WaterfillLevel center ideal r < |center i - ideal i|
  · rw [max_eq_left (by linarith)]
    simp [hactive]
  · rw [max_eq_right (by linarith)]
    simp [hactive]

/-- A nonempty water-filling active set is among the finite subsets defining its level. -/
theorem linfL1WaterfillActiveCoordinates_mem_subsets
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ)
    (hnonempty : (linfL1WaterfillActiveCoordinates center ideal r).Nonempty) :
    linfL1WaterfillActiveCoordinates center ideal r ∈
      linfL1WaterfillSubsets Coord := by
  classical
  rw [linfL1WaterfillSubsets]
  exact Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp hnonempty, by
    rw [Finset.mem_powerset]
    exact (linfL1WaterfillActiveCoordinates center ideal r).subset_univ⟩

/-- A water-filling coordinate moves toward its ideal by exactly its displayed amount. -/
theorem linfL1WaterfillRawResponse_coordinate_distance_eq_amount
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) (i : Coord) :
    |linfL1WaterfillRawResponse center ideal r i - center i| =
      max (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0 := by
  let amount : ℝ := max
    (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0
  have hlevel : 0 ≤ linfL1WaterfillLevel center ideal r :=
    linfL1WaterfillLevel_nonneg center ideal r
  change |(center i - (center i - ideal i) / |center i - ideal i| * amount) - center i| = amount
  rw [sub_sub_cancel_left, abs_neg, abs_mul]
  by_cases hzero : center i - ideal i = 0
  · have hamount : amount = 0 := by
      dsimp [amount]
      rw [hzero, abs_zero, zero_sub, max_eq_right]
      linarith
    simp [hzero, hamount]
  · rw [unitSign_abs_eq_one hzero, one_mul, abs_of_nonneg]
    exact le_max_right _ _

/-- The total exact water-filling motion never exceeds the available `L1` radius. -/
theorem linfL1Waterfill_sum_amount_le_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∑ i : Coord, max
      (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0) ≤ r := by
  rw [linfL1Waterfill_sum_amount_eq_active_sum]
  let active := linfL1WaterfillActiveCoordinates center ideal r
  by_cases hactive : active.Nonempty
  · have hmember : active ∈ linfL1WaterfillSubsets Coord := by
      simpa [active] using
        linfL1WaterfillActiveCoordinates_mem_subsets center ideal r hactive
    have havg := linfL1WaterfillSubset_average_le_level center ideal r active hmember
    have hcardNat : 0 < active.card := Finset.card_pos.mpr hactive
    have hcard : 0 < (active.card : ℝ) := by exact_mod_cast hcardNat
    have hmul : (∑ i ∈ active, |center i - ideal i|) - r ≤
        linfL1WaterfillLevel center ideal r * (active.card : ℝ) :=
      (div_le_iff₀ hcard).mp havg
    have hsum : (∑ i ∈ active,
        (|center i - ideal i| - linfL1WaterfillLevel center ideal r)) =
        (∑ i ∈ active, |center i - ideal i|) -
          (active.card : ℝ) * linfL1WaterfillLevel center ideal r := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    nlinarith
  · have hempty : active = ∅ := Finset.not_nonempty_iff_eq_empty.mp hactive
    simp [active, hempty, hr]

/-- The exact water-filling response lies in the source `L1` query ball. -/
theorem linfL1WaterfillRawResponse_l1_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.l1
      (linfL1WaterfillRawResponse center ideal r) center ≤ r := by
  rw [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
  calc
    (∑ i : Coord, |linfL1WaterfillRawResponse center ideal r i - center i|) =
        ∑ i : Coord, max
          (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0 := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact linfL1WaterfillRawResponse_coordinate_distance_eq_amount center ideal r i
    _ ≤ r := linfL1Waterfill_sum_amount_le_radius center ideal hr

/--
Every feasible `L1`-ball candidate bounds each nonempty subset's average
residual; this is the finite dual lower bound for water-filling.
-/
theorem linfL1Subset_average_le_linf_cost_of_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ}
    (hball : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r)
    (A : Finset Coord) (hA : A.Nonempty) :
    ((∑ i ∈ A, |center i - ideal i|) - r) / (A.card : ℝ) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  let cost : ℝ := AppliedModelingLib.FiniteDimensionalNorms.linf
    (fun i => candidate i - ideal i)
  have hcardNat : 0 < A.card := Finset.card_pos.mpr hA
  have hcard : 0 < (A.card : ℝ) := by exact_mod_cast hcardNat
  have hcoordinate : ∀ i ∈ A, |center i - ideal i| ≤
      cost + |candidate i - center i| := by
    intro i _hi
    calc
      |center i - ideal i| ≤ |center i - candidate i| + |candidate i - ideal i| := by
        simpa using abs_sub_le (center i) (candidate i) (ideal i)
      _ = |candidate i - center i| + |candidate i - ideal i| := by
        rw [abs_sub_comm (center i) (candidate i)]
      _ ≤ |candidate i - center i| + cost := by
        apply add_le_add_right
        unfold cost AppliedModelingLib.FiniteDimensionalNorms.linf
        exact Finset.le_sup' (s := (Finset.univ : Finset Coord))
          (f := fun j => |candidate j - ideal j|) (Finset.mem_univ i)
      _ = cost + |candidate i - center i| := by ring
  have hsum_coordinate := Finset.sum_le_sum hcoordinate
  have hstep_subset : (∑ i ∈ A, |candidate i - center i|) ≤
      ∑ i : Coord, |candidate i - center i| :=
    Finset.sum_le_sum_of_subset_of_nonneg A.subset_univ
      (by intro i _hi _hnot; exact abs_nonneg _)
  have hstep : (∑ i : Coord, |candidate i - center i|) ≤ r := by
    simpa [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
      using hball
  have hsum : (∑ i ∈ A, |center i - ideal i|) ≤
      (A.card : ℝ) * cost + r := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hsum_coordinate
    linarith
  apply (div_le_iff₀ hcard).mpr
  linarith

/-- The water-filling level is a lower bound on the `L∞` cost of every feasible candidate. -/
theorem linfL1WaterfillLevel_le_linf_cost_of_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ}
    (hball : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r) :
    linfL1WaterfillLevel center ideal r ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  classical
  unfold linfL1WaterfillLevel
  apply max_le
  · exact AppliedModelingLib.FiniteDimensionalNorms.linf_nonneg _
  · apply Finset.sup'_le
    intro A hA
    have hAne : A.Nonempty := by
      exact Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hA).1
    exact linfL1Subset_average_le_linf_cost_of_l1Ball hball A hAne

/-- Every coordinate of the water-filled response has residual cost at most its level. -/
theorem linfL1WaterfillRawResponse_coordinate_cost_le_level
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) (i : Coord) :
    |linfL1WaterfillRawResponse center ideal r i - ideal i| ≤
      linfL1WaterfillLevel center ideal r := by
  let level : ℝ := linfL1WaterfillLevel center ideal r
  let d : ℝ := center i - ideal i
  let amount : ℝ := max (|d| - level) 0
  have hlevel : 0 ≤ level := by
    simpa [level] using linfL1WaterfillLevel_nonneg center ideal r
  unfold linfL1WaterfillRawResponse
  have hrewrite : center i -
      ((center i - ideal i) / |center i - ideal i|) *
        max (|center i - ideal i| - linfL1WaterfillLevel center ideal r) 0 - ideal i =
      d - (d / |d|) * amount := by
    dsimp [d, amount, level]
    ring
  rw [hrewrite]
  change |d - (d / |d|) * amount| ≤ level
  by_cases hzero : d = 0
  · rw [hzero]
    simpa using hlevel
  by_cases hle : |d| ≤ level
  · have hamount : amount = 0 := by
      dsimp [amount]
      rw [max_eq_right]
      linarith
    rw [hamount]
    simpa using hle
  · have hlt : level < |d| := lt_of_not_ge hle
    have hamount : amount = |d| - level := by
      dsimp [amount]
      rw [max_eq_left]
      linarith
    rw [hamount]
    have hden : |d| ≠ 0 := abs_ne_zero.mpr hzero
    have hcalc : d - (d / |d|) * (|d| - level) = (level / |d|) * d := by
      field_simp [hden]
      ring
    rw [hcalc, abs_mul, abs_div, abs_abs, abs_of_nonneg hlevel]
    field_simp [hden]
    exact le_rfl

/-- The water-filled response attains `L∞` cost at most the water-filling level. -/
theorem linfL1WaterfillRawResponse_linf_cost_le_level
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (center ideal : Coord → ℝ) (r : ℝ) :
    AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => linfL1WaterfillRawResponse center ideal r i - ideal i) ≤
        linfL1WaterfillLevel center ideal r := by
  unfold AppliedModelingLib.FiniteDimensionalNorms.linf
  apply Finset.sup'_le
  intro i _hi
  exact linfL1WaterfillRawResponse_coordinate_cost_le_level center ideal r i

/-- The Borel water-filled point is an exact `L∞` minimizer over the source `L1` query ball. -/
theorem linfL1WaterfillRawResponse_minimizes_linf_on_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hcandidate : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => linfL1WaterfillRawResponse center ideal r i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  exact (linfL1WaterfillRawResponse_linf_cost_le_level center ideal r).trans
    (linfL1WaterfillLevel_le_linf_cost_of_l1Ball hcandidate)

/-- The canonical one-coordinate response used off the corrected exceptional event. -/
noncomputable def linfL1CanonicalRawResponse
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  linfL1SingleActiveRawResponse center ideal r (linfL1ActiveCoordinate center ideal)

/-- The normalized direction encoded by an arbitrary positive-radius `L1` raw response. -/
noncomputable def linfL1RawDirection
    {Coord : Type*}
    (center raw : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => (center i - raw i) / r

/-- The normalized raw-direction map is Borel at every fixed positive or zero radius. -/
theorem measurable_linfL1RawDirection
    {Coord : Type*}
    (r : ℝ) :
    Measurable (fun z : (Coord → ℝ) × (Coord → ℝ) =>
      linfL1RawDirection z.1 z.2 r) := by
  apply measurable_pi_lambda
  intro i
  exact (((measurable_pi_apply i).comp measurable_fst).sub
    ((measurable_pi_apply i).comp measurable_snd)).div measurable_const

/-- The one-coordinate response uses exactly its nonnegative `L1` query radius. -/
theorem linfL1SingleActiveRawResponse_l1_distance_eq
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 ≤ r) (hnz : center i0 ≠ ideal i0) :
    finiteCoordinateDistance SourceNorm.l1
      (linfL1SingleActiveRawResponse center ideal r i0) center = r := by
  rw [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
  rw [Finset.sum_eq_single i0]
  · rw [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection,
      if_pos rfl, sub_sub_cancel_left, abs_neg, abs_mul, abs_of_nonneg hr,
      unitSign_abs_eq_one (sub_ne_zero.mpr hnz)]
    ring
  · intro i _hi hne
    simp [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection, hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ i0))

/-- The one-coordinate response is always feasible for its nonnegative `L1` query ball. -/
theorem linfL1SingleActiveRawResponse_l1_distance_le
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.l1
      (linfL1SingleActiveRawResponse center ideal r i0) center ≤ r := by
  by_cases hnz : center i0 = ideal i0
  · rw [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1]
    have hraw : linfL1SingleActiveRawResponse center ideal r i0 = center := by
      ext i
      by_cases hi : i = i0
      · subst i
        simp [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection, hnz]
      · simp [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection, hi]
    simp [hraw, hr]
  · exact (linfL1SingleActiveRawResponse_l1_distance_eq hr hnz).le

/--
If the selected displacement exceeds every competing displacement by at least
the query radius and cannot cross its ideal, the one-coordinate step has the
displayed `L∞` cost.
-/
theorem linfL1SingleActiveRawResponse_linf_cost_eq
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 ≤ r)
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|)
    (hnoncross : r ≤ |center i0 - ideal i0|)
    (hmargin : ∀ i, i ≠ i0 → |center i - ideal i| ≤
      |center i0 - ideal i0| - r) :
    AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => linfL1SingleActiveRawResponse center ideal r i0 i - ideal i) =
      |center i0 - ideal i0| - r := by
  rw [AppliedModelingLib.FiniteDimensionalNorms.linf]
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _hi
    by_cases hi : i = i0
    · subst i
      have hcost := l1LinfRawResponse_coordinate_cost
        (center := center) (ideal := ideal) (i := i0) hr hnoncross
      simpa [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection,
        l1LinfRawResponse] using hcost.le
    · simpa [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection, hi] using
        hmargin i hi
  · rw [show (|center i0 - ideal i0| - r) =
        |linfL1SingleActiveRawResponse center ideal r i0 i0 - ideal i0| by
          have hcost := l1LinfRawResponse_coordinate_cost
            (center := center) (ideal := ideal) (i := i0) hr hnoncross
          simpa [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection,
            l1LinfRawResponse] using hcost.symm]
    exact Finset.le_sup'
      (s := (Finset.univ : Finset Coord))
      (f := fun i => |linfL1SingleActiveRawResponse center ideal r i0 i - ideal i|)
      (Finset.mem_univ i0)

/-- Every `L1`-ball candidate retains at least the active displacement minus its radius. -/
theorem linfL1_active_cost_lower_bound_of_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hcandidate : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r) :
    |center i0 - ideal i0| - r ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  apply le_trans ?_ (Finset.le_sup'
    (s := (Finset.univ : Finset Coord))
    (f := fun i => |candidate i - ideal i|)
    (Finset.mem_univ i0))
  apply (sub_le_iff_le_add).mpr
  have hcoord : |candidate i0 - center i0| ≤ r :=
    le_trans (finiteCoordinateDistance_l1_coord_abs_le candidate center i0) hcandidate
  calc
    |center i0 - ideal i0| =
        |(center i0 - candidate i0) + (candidate i0 - ideal i0)| := by
      congr 1
      ring
    _ ≤ |center i0 - candidate i0| + |candidate i0 - ideal i0| := abs_add_le _ _
    _ = |candidate i0 - center i0| + |candidate i0 - ideal i0| := by
      rw [abs_sub_comm]
    _ ≤ r + |candidate i0 - ideal i0| := by gcongr
    _ = |candidate i0 - ideal i0| + r := by ring

/--
Corrected local optimality for the `L∞`-cost, `L1`-query endpoint.  The
non-crossing premise is the additional exceptional case omitted by the
printed appendix argument.
-/
theorem linfL1SingleActiveRawResponse_minimizes_linf_on_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 ≤ r)
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|)
    (hnoncross : r ≤ |center i0 - ideal i0|)
    (hmargin : ∀ i, i ≠ i0 → |center i - ideal i| ≤
      |center i0 - ideal i0| - r)
    (hcandidate : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => linfL1SingleActiveRawResponse center ideal r i0 i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  rw [linfL1SingleActiveRawResponse_linf_cost_eq hr hmax hnoncross hmargin]
  exact linfL1_active_cost_lower_bound_of_l1Ball hcandidate

/--
At positive radius, the corrected one-coordinate optimizer is the unique
`L∞`-cost minimizer on the `L1` query ball.  This removes Model A's
tie-breaking ambiguity off the corrected exceptional event.
-/
theorem linfL1SingleActiveRawResponse_eq_of_linf_cost_le_on_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal response : Coord → ℝ} {r : ℝ} {i0 : Coord}
    (hr : 0 < r)
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|)
    (hnoncross : r ≤ |center i0 - ideal i0|)
    (hmargin : ∀ i, i ≠ i0 → |center i - ideal i| ≤
      |center i0 - ideal i0| - r)
    (hresponse_ball : finiteCoordinateDistance SourceNorm.l1 response center ≤ r)
    (hresponse_cost :
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => response i - ideal i) ≤
        AppliedModelingLib.FiniteDimensionalNorms.linf
          (fun i => linfL1SingleActiveRawResponse center ideal r i0 i - ideal i)) :
    response = linfL1SingleActiveRawResponse center ideal r i0 := by
  have hnz : center i0 ≠ ideal i0 := by
    intro hzero
    have : r ≤ 0 := by simpa [hzero] using hnoncross
    exact (not_lt_of_ge this) hr
  have hrawcost := linfL1SingleActiveRawResponse_linf_cost_eq hr.le
    hmax hnoncross hmargin
  have hcost_upper :
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => response i - ideal i) ≤
        |center i0 - ideal i0| - r := by
    rw [← hrawcost]
    exact hresponse_cost
  have hcoord_ball : |response i0 - center i0| ≤ r :=
    le_trans (finiteCoordinateDistance_l1_coord_abs_le response center i0)
      hresponse_ball
  have hcoord_lower : |center i0 - ideal i0| - r ≤
      |response i0 - ideal i0| := by
    apply (sub_le_iff_le_add).mpr
    calc
      |center i0 - ideal i0| =
          |(center i0 - response i0) + (response i0 - ideal i0)| := by
        congr 1
        ring
      _ ≤ |center i0 - response i0| + |response i0 - ideal i0| := abs_add_le _ _
      _ = |response i0 - center i0| + |response i0 - ideal i0| := by
        rw [abs_sub_comm]
      _ ≤ r + |response i0 - ideal i0| := by gcongr
      _ = |response i0 - ideal i0| + r := by ring
  have hcoord_upper : |response i0 - ideal i0| ≤
      |center i0 - ideal i0| - r := by
    exact le_trans (Finset.le_sup'
      (s := (Finset.univ : Finset Coord))
      (f := fun i => |response i - ideal i|)
      (Finset.mem_univ i0)) hcost_upper
  have hcoord_cost : |response i0 - ideal i0| =
      |center i0 - ideal i0| - r :=
    le_antisymm hcoord_upper hcoord_lower
  have hactive_eq : response i0 =
      linfL1SingleActiveRawResponse center ideal r i0 i0 := by
    have hsingle := l1LinfRawResponse_coordinate_eq_of_cost_eq hr.le hnoncross
      hcoord_ball hcoord_cost
    simpa [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection,
      l1LinfRawResponse] using hsingle
  have hactive_step : |response i0 - center i0| = r := by
    rw [hactive_eq, linfL1SingleActiveRawResponse,
      linfL1SingleActiveDirection, if_pos rfl, sub_sub_cancel_left, abs_neg,
      abs_mul, abs_of_pos hr, unitSign_abs_eq_one (sub_ne_zero.mpr hnz)]
    ring
  have hsum_le : (∑ i : Coord, |response i - center i|) ≤ r := by
    simpa [finiteCoordinateDistance_l1, AppliedModelingLib.FiniteDimensionalNorms.l1] using
      hresponse_ball
  have hsum_eq : (∑ i : Coord, |response i - center i|) = r := by
    apply le_antisymm hsum_le
    rw [← hactive_step]
    exact Finset.single_le_sum
      (fun j _hj => abs_nonneg (response j - center j))
      (Finset.mem_univ i0)
  have hdelta_sum : (∑ i : Coord,
      (|response i - center i| - if i = i0 then r else 0)) = 0 := by
    rw [Finset.sum_sub_distrib]
    have hbase : (∑ i : Coord, if i = i0 then r else 0) = r := by
      rw [Finset.sum_eq_single i0]
      · simp
      · intro i _hi hne
        simp [hne]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ i0))
    linarith
  have hdelta_nonneg : ∀ i : Coord,
      0 ≤ |response i - center i| - if i = i0 then r else 0 := by
    intro i
    by_cases hi : i = i0
    · simpa [hi, hactive_step]
    · simp [hi, abs_nonneg]
  have hdelta_zero : ∀ i : Coord,
      (|response i - center i| - (if i = i0 then r else 0)) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _hj => hdelta_nonneg j)).mp hdelta_sum i (Finset.mem_univ i)
  ext i
  by_cases hi : i = i0
  · subst i
    exact hactive_eq
  · have hzero : |response i - center i| = 0 := by
      simpa [hi] using hdelta_zero i
    have hresponse_center : response i = center i := by
      exact sub_eq_zero.mp (abs_eq_zero.mp hzero)
    simp [linfL1SingleActiveRawResponse, linfL1SingleActiveDirection, hi,
      hresponse_center]

/-- A normalized direction from an `L1`-ball raw response has coordinate magnitude at most one. -/
theorem linfL1RawDirection_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center raw : Coord → ℝ} {r : ℝ} {i : Coord}
    (hr : 0 < r)
    (hraw_ball : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r) :
    |linfL1RawDirection center raw r i| ≤ 1 := by
  rw [linfL1RawDirection, abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  have hcoord : |raw i - center i| ≤ r :=
    le_trans (finiteCoordinateDistance_l1_coord_abs_le raw center i) hraw_ball
  simpa [abs_sub_comm] using hcoord

/-- Every normalized direction from an `L1`-ball raw response has bounded squared Euclidean norm. -/
theorem linfL1RawDirection_l2Sq_le_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {center raw : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hraw_ball : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq (linfL1RawDirection center raw r) ≤
      Fintype.card Coord := by
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (linfL1RawDirection center raw r) (by norm_num : (0 : ℝ) ≤ 1)
    (fun i => linfL1RawDirection_coordinate_abs_le_one hr hraw_ball)
  norm_num at hnorm ⊢
  exact hnorm

/--
The arbitrary Model A/raw-sampled-subgradient discrepancy for the corrected
`L∞/L1` endpoint.  It vanishes off the corrected exceptional event.
-/
noncomputable def linfL1RawDirectionSubgradientPerturbation
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal raw : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => linfL1RawDirection center raw r i -
    linfL1SingleActiveDirection center ideal (linfL1ActiveCoordinate center ideal) i

/--
The discrepancy between an arbitrary exact `L∞/L1` Model A direction and the
Borel symmetric active subgradient.  This is the perturbation used by the
stochastic convergence route: the symmetric direction has an exact population
mean even on the measure-zero tie surfaces.
-/
noncomputable def linfL1RawDirectionSymmetricPerturbation
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal raw : Coord → ℝ) (r : ℝ) : Coord → ℝ :=
  fun i => linfL1RawDirection center raw r i -
    linfL1SymmetricActiveDirection center ideal i

/-- The corrected Model A discrepancy has a uniform squared Euclidean bound. -/
theorem linfL1RawDirectionSubgradientPerturbation_l2Sq_le_four_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal raw : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hraw_ball : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (linfL1RawDirectionSubgradientPerturbation center ideal raw r) ≤
      4 * Fintype.card Coord := by
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (linfL1RawDirectionSubgradientPerturbation center ideal raw r)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun i => by
      unfold linfL1RawDirectionSubgradientPerturbation
      calc
        |linfL1RawDirection center raw r i -
            linfL1SingleActiveDirection center ideal
              (linfL1ActiveCoordinate center ideal) i| ≤
            |linfL1RawDirection center raw r i| +
              |linfL1SingleActiveDirection center ideal
                (linfL1ActiveCoordinate center ideal) i| := by
          simpa using (abs_sub_le
            (linfL1RawDirection center raw r i) 0
            (linfL1SingleActiveDirection center ideal
              (linfL1ActiveCoordinate center ideal) i))
        _ ≤ 2 := by
          have hraw := linfL1RawDirection_coordinate_abs_le_one (i := i) hr hraw_ball
          have hactive : |linfL1SingleActiveDirection center ideal
              (linfL1ActiveCoordinate center ideal) i| ≤ 1 := by
            unfold linfL1SingleActiveDirection
            split <;> simp [unitSign_abs_le_one]
          linarith)
  norm_num at hnorm ⊢
  nlinarith

/-- The symmetric-direction perturbation has the same uniform energy bound. -/
theorem linfL1RawDirectionSymmetricPerturbation_l2Sq_le_four_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal raw : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hraw_ball : finiteCoordinateDistance SourceNorm.l1 raw center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (linfL1RawDirectionSymmetricPerturbation center ideal raw r) ≤
      4 * Fintype.card Coord := by
  have hnorm := AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_le_card_mul_sq_of_abs_le
    (linfL1RawDirectionSymmetricPerturbation center ideal raw r)
    (by norm_num : (0 : ℝ) ≤ 2)
    (fun i => by
      unfold linfL1RawDirectionSymmetricPerturbation
      calc
        |linfL1RawDirection center raw r i -
            linfL1SymmetricActiveDirection center ideal i| ≤
            |linfL1RawDirection center raw r i| +
              |linfL1SymmetricActiveDirection center ideal i| := by
          simpa using abs_sub_le
            (linfL1RawDirection center raw r i) 0
            (linfL1SymmetricActiveDirection center ideal i)
        _ ≤ 2 := by
          have hraw := linfL1RawDirection_coordinate_abs_le_one (i := i) hr hraw_ball
          have hsymm := linfL1SymmetricActiveDirection_coordinate_abs_le_one
            center ideal i
          linarith)
  norm_num at hnorm ⊢
  nlinarith

/-- On the corrected good event, the canonical response minimizes `L∞` cost on its `L1` ball. -/
theorem linfL1CanonicalRawResponse_minimizes_linf_on_l1Ball
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal candidate : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hcandidate : finiteCoordinateDistance SourceNorm.l1 candidate center ≤ r) :
    AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => linfL1CanonicalRawResponse center ideal r i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => candidate i - ideal i) := by
  exact linfL1SingleActiveRawResponse_minimizes_linf_on_l1Ball hr
    (linfL1ActiveCoordinate_is_max center ideal) hgood.1 hgood.2 hcandidate

/-- At positive radius, the corrected canonical direction is an `L∞` sample-cost subgradient. -/
theorem finiteSubgradientAt_linfL1CanonicalDirection
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center
      (linfL1SingleActiveDirection center ideal
        (linfL1ActiveCoordinate center ideal)) := by
  exact finiteSubgradientAt_linfL1SingleActiveDirection hr
    (linfL1ActiveCoordinate_is_max center ideal) hgood.1

/--
A finite-coordinate trajectory follows the projected SSGM recurrence at every
successor step. The update from `t` to `t+1` uses `radius (t+1)`, matching the
paper's positive-time indexing.
-/
def FollowsFiniteProjectedSSGM
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  ∀ t : ℕ,
    FiniteProjectedSSGMUpdateAt project (trajectory t) (radius (t + 1))
      (subgradient t) (noise t) (bias t) (trajectory (t + 1))

theorem followsFiniteProjectedSSGM_formula
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ↔
      ∀ t : ℕ,
        FiniteProjectedSSGMUpdateAt project (trajectory t) (radius (t + 1))
          (subgradient t) (noise t) (bias t) (trajectory (t + 1)) := by
  rfl

theorem followsFiniteProjectedSSGM_zero_noise_bias_formula
    {Coord : Type*}
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSSGM project trajectory radius subgradient
        (fun _t _i => 0) (fun _t _i => 0) ↔
      ∀ t : ℕ,
        trajectory (t + 1) =
          project (fun i =>
            trajectory t i - radius (t + 1) * subgradient t i) := by
  rw [followsFiniteProjectedSSGM_formula]
  simp [finiteProjectedSSGMUpdateAt_formula]

theorem followsFiniteProjectedSSGM_mem_of_projectionOnto
    {Coord : Type*} {X : Set (Coord → ℝ)}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    {subgradient noise bias : ℕ → Coord → ℝ}
    (hproject : ProjectionOnto X project)
    (hfollow :
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias)
    (h0 : trajectory 0 ∈ X) :
    ∀ t : ℕ, trajectory t ∈ X := by
  intro t
  induction t with
  | zero => exact h0
  | succ t _ih =>
      have hupd := hfollow t
      unfold FiniteProjectedSSGMUpdateAt at hupd
      rw [hupd]
      exact hproject _

/--
A projected SSGM recurrence whose selected directions have already been
certified as finite-coordinate subgradients of a deterministic cost objective.
This isolates the remaining stochastic convergence theorem from the local
Model B algebra.
-/
def FollowsFiniteProjectedSubgradientMethod
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
    ∀ t : ℕ, FiniteSubgradientAt cost (trajectory t) (subgradient t)

/--
Stochastic/sample-cost variant of the finite projected subgradient-method
predicate.  At time `t`, the selected direction is a finite subgradient of the
sample cost observed at that time.  This matches the paper's voter-sampling
view before taking expectations in the SSGM convergence theorem.
-/
def FollowsFiniteProjectedSampleSubgradientMethod
    {Coord : Type*} [Fintype Coord]
    (sampleCost : ℕ → (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) : Prop :=
  FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
    ∀ t : ℕ, FiniteSubgradientAt (sampleCost t) (trajectory t) (subgradient t)

theorem followsFiniteProjectedSubgradientMethod_formula
    {Coord : Type*} [Fintype Coord]
    (cost : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSubgradientMethod cost project trajectory radius
        subgradient noise bias ↔
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
        ∀ t : ℕ, FiniteSubgradientAt cost (trajectory t) (subgradient t) := by
  rfl

theorem followsFiniteProjectedSampleSubgradientMethod_formula
    {Coord : Type*} [Fintype Coord]
    (sampleCost : ℕ → (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    (trajectory : ℕ → Coord → ℝ) (radius : ℕ → ℝ)
    (subgradient noise bias : ℕ → Coord → ℝ) :
    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project trajectory
        radius subgradient noise bias ↔
      FollowsFiniteProjectedSSGM project trajectory radius subgradient noise bias ∧
        ∀ t : ℕ,
          FiniteSubgradientAt (sampleCost t) (trajectory t) (subgradient t) := by
  rfl

theorem followsFiniteProjectedSubgradientMethod_mem_of_projectionOnto
    {Coord : Type*} [Fintype Coord] {X : Set (Coord → ℝ)}
    {cost : (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    {subgradient noise bias : ℕ → Coord → ℝ}
    (hproject : ProjectionOnto X project)
    (hfollow :
      FollowsFiniteProjectedSubgradientMethod cost project trajectory radius
        subgradient noise bias)
    (h0 : trajectory 0 ∈ X) :
    ∀ t : ℕ, trajectory t ∈ X :=
  followsFiniteProjectedSSGM_mem_of_projectionOnto hproject hfollow.1 h0

theorem followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
    {Coord : Type*} [Fintype Coord] {X : Set (Coord → ℝ)}
    {sampleCost : ℕ → (Coord → ℝ) → ℝ}
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    {subgradient noise bias : ℕ → Coord → ℝ}
    (hproject : ProjectionOnto X project)
    (hfollow :
      FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
        trajectory radius subgradient noise bias)
    (h0 : trajectory 0 ∈ X) :
    ∀ t : ℕ, trajectory t ∈ X :=
  followsFiniteProjectedSSGM_mem_of_projectionOnto hproject hfollow.1 h0

/--
A finite-coordinate Model B raw response followed by projection has the shape of
a projected SSGM update with zero noise/bias and descent direction equal to the
negative normalized utility direction.
-/
theorem finiteProjectedSSGMUpdateAt_of_modelBFiniteResponseAt
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (q : SourceNorm)
    (project : (Coord → ℝ) → Coord → ℝ)
    (previous raw next gradient : Coord → ℝ) (radius : ℝ)
    (hresponse : ModelBFiniteResponseAt q previous radius gradient raw)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (fun i => -modelBFiniteNormalizedDirection q gradient i)
      (fun _ => 0) (fun _ => 0) next := by
  unfold FiniteProjectedSSGMUpdateAt Algorithm1ProjectedUpdate at *
  rw [hproject, hresponse]
  congr
  ext i
  ring

/--
At the `L1/L∞` endpoint, the source Model A raw sign response followed by
Algorithm 1's projection is exactly a projected subgradient update.  The
separate good-event hypothesis is needed only to establish that this raw point
is the Model A maximizer, not for this algebraic recurrence.
-/
theorem finiteProjectedSSGMUpdateAt_of_l1LinfRawResponse
    {Coord : Type*} [Fintype Coord]
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ)
    (hraw : raw = l1LinfRawResponse previous ideal radius)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (lpCostGradientCandidate 1 (fun i => previous i - ideal i))
      (fun _ => 0) (fun _ => 0) next := by
  unfold FiniteProjectedSSGMUpdateAt Algorithm1ProjectedUpdate at *
  rw [hproject, hraw]
  congr
  ext i
  rw [lpCostGradientCandidate_one_eq_unitSign]
  simp [l1LinfRawResponse]

/--
The corrected `L∞/L1` single-active-coordinate Model A response followed by
Algorithm 1's projection is a projected subgradient update on its good event.
-/
theorem finiteProjectedSSGMUpdateAt_of_linfL1SingleActiveRawResponse
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ) (i0 : Coord)
    (hraw : raw = linfL1SingleActiveRawResponse previous ideal radius i0)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (linfL1SingleActiveDirection previous ideal i0)
      (fun _ => 0) (fun _ => 0) next := by
  unfold FiniteProjectedSSGMUpdateAt Algorithm1ProjectedUpdate at *
  rw [hproject, hraw]
  congr
  ext i
  simp [linfL1SingleActiveRawResponse]

/-- The canonical corrected response has the corresponding projected subgradient-update form. -/
theorem finiteProjectedSSGMUpdateAt_of_linfL1CanonicalRawResponse
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ)
    (hraw : raw = linfL1CanonicalRawResponse previous ideal radius)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (linfL1SingleActiveDirection previous ideal
        (linfL1ActiveCoordinate previous ideal))
      (fun _ => 0) (fun _ => 0) next := by
  apply finiteProjectedSSGMUpdateAt_of_linfL1SingleActiveRawResponse project radius
    (linfL1ActiveCoordinate previous ideal)
  · simpa [linfL1CanonicalRawResponse] using hraw
  · exact hproject

/--
Theorem 2-specific bridge: when Model B moves in the utility-gradient direction,
the negative of the Appendix C.4 cost-gradient candidate, Lemma 3 removes the
normalization and the projected step is an SSGM update using the positive
cost-gradient candidate as the descent subgradient.
-/
theorem finiteProjectedSSGMUpdateAt_of_modelBFiniteResponseAt_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {previous ideal raw next : Coord → ℝ} (radius : ℝ)
    (hcoord : ∀ i, previous i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) previous radius
        (fun i => -lpCostGradientCandidate p (fun j => previous j - ideal j) i) raw)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project previous radius
      (lpCostGradientCandidate p (fun i => previous i - ideal i))
      (fun _ => 0) (fun _ => 0) next := by
  have hbase :=
    finiteProjectedSSGMUpdateAt_of_modelBFiniteResponseAt
      (q := SourceNorm.lp q) project previous raw next
      (fun i => -lpCostGradientCandidate p (fun j => previous j - ideal j) i) radius
      hresponse hproject
  simpa [modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self hdual hcoord]
    using hbase

/--
Whole-trajectory version of the Theorem 2 Model B-to-SSGM bridge.  Away from
the coordinate-equality bad events, sign-correct finite Holder-dual Model B
responses followed by projection generate exactly the finite projected SSGM
recurrence with the positive `Lp` cost-gradient candidate as the descent
subgradient and zero noise/bias.
-/
theorem followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSSGM project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  intro t
  exact finiteProjectedSSGMUpdateAt_of_modelBFiniteResponseAt_neg_lpCostGradientCandidate
    hdual project (radius (t + 1)) (hcoord t) (hresponse t) (hproject t)

/--
If the directions in the previous whole-trajectory Model B bridge are also
certified subgradients of a cost objective, the trajectory follows the finite
projected subgradient method.  The remaining paper-level convergence argument
can then focus on the stochastic/process hypotheses.
-/
theorem followsFiniteProjectedSubgradientMethod_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (cost : (Coord → ℝ) → ℝ)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1)))
    (hsubgradient :
      ∀ t : ℕ,
        FiniteSubgradientAt cost (trajectory t)
          (lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))) :
    FollowsFiniteProjectedSubgradientMethod cost project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  refine ⟨?_, hsubgradient⟩
  exact followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
    hdual project hcoord hresponse hproject

/--
Sample-cost version of the whole-trajectory Theorem 2 bridge.  For each sampled
ideal point, convexity plus the Lemma 3 derivative calculation certifies the
positive `Lp` cost-gradient candidate as a finite subgradient of that sample's
cost.  The remaining convergence theorem can then reason about these sampled
subgradients as stochastic inputs.
-/
theorem followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hconv :
      ∀ t : ℕ,
        ConvexOn ℝ Set.univ
          (fun y : Coord → ℝ =>
            AppliedModelingLib.FiniteDimensionalNorms.lp p
              (fun i => y i - ideal t i)))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  refine ⟨?_, ?_⟩
  · exact followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
      hdual project hcoord hresponse hproject
  · intro t
    exact finiteSubgradientAt_lpCostGradientCandidate_of_convexOn
      (HolderDualFinite.one_lt_left hdual) (hcoord t) (hconv t)

/--
Sample-cost Theorem 2 bridge with finite `Lp` convexity discharged.  This is the
paper-local reduction closest to the eventual stochastic approximation theorem:
Model B responses outside coordinate-equality bad events generate projected
sample subgradient steps for the sampled `Lp` costs.
-/
theorem followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses'
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hcoord : ∀ t i, trajectory t i ≠ ideal t i)
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  refine ⟨?_, ?_⟩
  · exact followsFiniteProjectedSSGM_of_modelBFiniteResponses_neg_lpCostGradientCandidate
      hdual project hcoord hresponse hproject
  · intro t
    exact finiteSubgradientAt_lpCostGradientCandidate
      (HolderDualFinite.one_lt_left hdual) (hcoord t)

/--
Bad-event-avoidance wrapper for the sample-cost Theorem 2 bridge.  The
coordinate-equality bad event is the paper's exceptional set for Lemma 3; once
the sampled ideals avoid it at every step, the Model B responses generate
projected sample subgradient steps for the sampled `Lp` costs.
-/
theorem followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {p q : ℝ} (hdual : HolderDualFinite p q)
    (project : (Coord → ℝ) → Coord → ℝ)
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
      project trajectory radius
      (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) := by
  exact followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses'
    hdual project
    (coordinate_noncollision_of_forall_notMem_coordinateEqualityBadEvent
      trajectory ideal havoid)
    hresponse hproject

/--
Feasible-projection wrapper for the bad-event Model B bridge.  Once the
projector maps into the feasible solution space and the initial point is
feasible, the same local hypotheses give both a projected sample-subgradient
recurrence and feasibility of every iterate.
-/
theorem followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hprojectOnto : ProjectionOnto E.solutionSpace project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory radius
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  have hfollow :
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory radius
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) :=
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent
      hdual project havoid hresponse hproject
  exact ⟨hfollow,
    followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
      hprojectOnto hfollow h0⟩

theorem followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace_of_normProjection
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ} {radius : ℕ → ℝ}
    (hprojectNorm : IsNormProjectionOnto E (SourceNorm.lp q) project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t) (radius (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory radius
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  exact
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace
      E hdual (projectionOnto_of_isNormProjectionOnto E (SourceNorm.lp q) hprojectNorm)
      h0 havoid hresponse hproject

namespace FiniteCoordinateIdealDistributionData

theorem lpCostGradientCandidate_lq_norm_eq_one_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      finiteCoordinateNorm (SourceNorm.lp q)
        (lpCostGradientCandidate p (fun i => x i - ideal i)) = 1 := by
  filter_upwards [D.coordinate_noncollision_ae x] with ideal hcoord
  exact lemma3_finite_holder_dual_gradient_candidate_norm_formula_impl hdual hcoord

theorem finiteSubgradientAt_lpCostGradientCandidate_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p : ℝ} (hp : 1 < p) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal i))
        x
        (lpCostGradientCandidate p (fun i => x i - ideal i)) := by
  filter_upwards [D.coordinate_noncollision_ae x] with ideal hcoord
  exact finiteSubgradientAt_lpCostGradientCandidate hp hcoord

theorem finiteSubgradientAt_lpCostGradientCandidate_one_ae
    {Coord : Type*} [Fintype Coord]
    (D : FiniteCoordinateIdealDistributionData Coord) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      FiniteSubgradientAt
        (fun y : Coord → ℝ =>
          AppliedModelingLib.FiniteDimensionalNorms.lp 1 (fun i => y i - ideal i))
        x
        (lpCostGradientCandidate 1 (fun i => x i - ideal i)) := by
  filter_upwards [D.coordinate_noncollision_ae x] with ideal hcoord
  exact finiteSubgradientAt_lpCostGradientCandidate_one hcoord

theorem modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂D.idealMeasure,
      modelBFiniteNormalizedDirection (SourceNorm.lp q)
        (fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i) =
          fun i => -lpCostGradientCandidate p (fun j => x j - ideal j) i := by
  filter_upwards [D.coordinate_noncollision_ae x] with ideal hcoord
  exact modelBFiniteNormalizedDirection_neg_lpCostGradientCandidate_eq_self
    hdual hcoord

theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance_ae
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (D : FiniteCoordinateIdealDistributionData Coord)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center : Coord → ℝ} {r : ℝ}
    (response : (Coord → ℝ) → Coord → ℝ)
    (hresponse :
      ∀ ideal,
        ModelBFiniteResponseAt (SourceNorm.lp q) center r
          (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
          (response ideal)) :
    ∀ᵐ ideal ∂D.idealMeasure,
      finiteCoordinateDistance (SourceNorm.lp q) (response ideal) center = |r| := by
  filter_upwards [D.coordinate_noncollision_ae center] with ideal hcoord
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_boundary_distance
    hdual hcoord (hresponse ideal)

end FiniteCoordinateIdealDistributionData

theorem finiteProjectedSampleSubgradientMethod_lpCost_modelB_with_ilvRadius_ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    {p q r0 : ℝ} (hdual : HolderDualFinite p q) (hr0 : 0 < r0)
    {project : (Coord → ℝ) → Coord → ℝ}
    {trajectory ideal raw : ℕ → Coord → ℝ}
    (hprojectNorm : IsNormProjectionOnto E (SourceNorm.lp q) project)
    (h0 : trajectory 0 ∈ E.solutionSpace)
    (havoid : ∀ t : ℕ, ideal t ∉ coordinateEqualityBadEvent (trajectory t))
    (hresponse :
      ∀ t : ℕ,
        ModelBFiniteResponseAt (SourceNorm.lp q) (trajectory t)
          (ilvRadius r0 (t + 1))
          (fun i => -lpCostGradientCandidate p
            (fun j => trajectory t j - ideal t j) i) (raw t))
    (hproject :
      ∀ t : ℕ, Algorithm1ProjectedUpdate project (raw t) (trajectory (t + 1))) :
    SSGMStepSizeConditions (ilvRadius r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - ideal t i))
        project trajectory (ilvRadius r0)
        (fun t => lpCostGradientCandidate p (fun i => trajectory t i - ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ, trajectory t ∈ E.solutionSpace := by
  refine ⟨algorithm1_radius_ssgmStepSizeConditions hr0, ?_⟩
  exact
    followsFiniteProjectedSampleSubgradientMethod_lpCost_of_modelBFiniteResponses_avoids_badEvent_mem_solutionSpace_of_normProjection
      E hdual hprojectNorm h0 havoid hresponse hproject

/--
Primitive pointwise Algorithm 1 trace source for the finite-coordinate Model B
route.  This record uses the paper-facing coordinate-noncollision statement
directly: at every sampled step, the selected ideal has no coordinate equal to
the current iterate.  The older bad-event formulation is derived from this
field below.
-/
structure FiniteModelBILVAlgorithm1PrimitiveTraceSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  voter : ℕ → Voter
  raw : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E (SourceNorm.lp q) project
  initial_feasible :
    E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈ E.solutionSpace
  coordinate_noncollision :
    ∀ t : ℕ, ∀ i : Coord,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
        E.ideal (voter t) i
  raw_update_formula :
    ∀ t : ℕ,
      raw t =
        fun i =>
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
            ilvRadius r0 (t + 1) *
              lpCostGradientCandidate p
                (fun j =>
                  E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t j -
                    E.ideal (voter t) j) i
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB (t + 1))

/--
Raw finite-coordinate semantics for the Model B branch of Algorithm 1.

The abstract source field `E.respondsAccordingTo modelB` is intentionally kept
separate from this data package. A future source-semantics pass can replace the
abstract response flag by constructing this trace from the paper's sampling and
response rules.  The source supplies the sign-correct coordinate update formula;
Holder duality and bad-event avoidance then derive the normalized Model B
response predicate consumed by the SSGM bridge.
-/
structure FiniteModelBILVAlgorithm1TraceSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  voter : ℕ → Voter
  raw : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E (SourceNorm.lp q) project
  initial_feasible :
    E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈ E.solutionSpace
  avoids_badEvent :
    ∀ t : ℕ,
      E.ideal (voter t) ∉
        coordinateEqualityBadEvent
          (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
  raw_update_formula :
    ∀ t : ℕ,
      raw t =
        fun i =>
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
            ilvRadius r0 (t + 1) *
              lpCostGradientCandidate p
                (fun j =>
                  E.trajectory (SourceNorm.lp q)
                      VoterResponseModel.modelB t j -
                    E.ideal (voter t) j) i
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB (t + 1))

def finiteModelBILVAlgorithm1TraceSource_of_primitive
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (S : FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0) :
    FiniteModelBILVAlgorithm1TraceSource E p q r0 where
  project := S.project
  voter := S.voter
  raw := S.raw
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  avoids_badEvent := by
    intro t
    exact
      (notMem_coordinateEqualityBadEvent_iff
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (E.ideal (S.voter t))).mpr (S.coordinate_noncollision t)
  raw_update_formula := S.raw_update_formula
  projected_update := S.projected_update

/--
Proof-facing finite-coordinate Model B trace.  This is derived from the raw
coordinate update source by the Holder-dual sign bridge.
-/
structure FiniteModelBILVTraceSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  voter : ℕ → Voter
  raw : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E (SourceNorm.lp q) project
  initial_feasible :
    E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈ E.solutionSpace
  avoids_badEvent :
    ∀ t : ℕ,
      E.ideal (voter t) ∉
        coordinateEqualityBadEvent
          (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
  modelB_response :
    ∀ t : ℕ,
      ModelBFiniteResponseAt (SourceNorm.lp q)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (ilvRadius r0 (t + 1))
        (fun i => -lpCostGradientCandidate p
          (fun j =>
            E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t j -
              E.ideal (voter t) j) i)
        (raw t)
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB (t + 1))

def finiteModelBILVTraceSource_of_algorithm1TraceSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (hdual : HolderDualFinite p q)
    (S : FiniteModelBILVAlgorithm1TraceSource E p q r0) :
    FiniteModelBILVTraceSource E p q r0 where
  project := S.project
  voter := S.voter
  raw := S.raw
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  avoids_badEvent := S.avoids_badEvent
  modelB_response := by
    intro t
    have hcoord :
        ∀ i,
          E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i ≠
            E.ideal (S.voter t) i :=
      (notMem_coordinateEqualityBadEvent_iff
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (E.ideal (S.voter t))).mp (S.avoids_badEvent t)
    exact
      (modelBFiniteResponseAt_neg_lpCostGradientCandidate_formula
        (Coord := Coord) hdual hcoord (ilvRadius r0 (t + 1))
        (S.raw t)).mpr (S.raw_update_formula t)
  projected_update := S.projected_update

structure FiniteModelBILVTrace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  voter : ℕ → Voter
  ideal : ℕ → Coord → ℝ
  raw : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E (SourceNorm.lp q) project
  initial_feasible :
    E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB 0 ∈ E.solutionSpace
  ideal_eq_selectedVoter :
    ∀ t : ℕ, ideal t = E.ideal (voter t)
  avoids_badEvent :
    ∀ t : ℕ,
      ideal t ∉
        coordinateEqualityBadEvent
          (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
  modelB_response :
    ∀ t : ℕ,
      ModelBFiniteResponseAt (SourceNorm.lp q)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t)
        (ilvRadius r0 (t + 1))
        (fun i => -lpCostGradientCandidate p
          (fun j =>
            E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t j -
              ideal t j) i)
        (raw t)
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB (t + 1))

def finiteModelBILVTrace_of_source
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (S : FiniteModelBILVTraceSource E p q r0) :
    FiniteModelBILVTrace E p q r0 where
  project := S.project
  voter := S.voter
  ideal := fun t => E.ideal (S.voter t)
  raw := S.raw
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  ideal_eq_selectedVoter := fun _ => rfl
  avoids_badEvent := S.avoids_badEvent
  modelB_response := S.modelB_response
  projected_update := S.projected_update

theorem FiniteModelBILVTrace.lpCost_eq_selectedVoter_lpCost
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0) :
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - T.ideal t i) =
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (T.voter t) i) := by
  intro t y
  rw [T.ideal_eq_selectedVoter t]

theorem FiniteModelBILVTrace.ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - T.ideal t i))
        T.project
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
        (ilvRadius r0)
        (fun t =>
          lpCostGradientCandidate p
            (fun i =>
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
                T.ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
          E.solutionSpace := by
  exact finiteProjectedSampleSubgradientMethod_lpCost_modelB_with_ilvRadius_ssgmInputs
    E hdual hr0 T.project_norm T.initial_feasible T.avoids_badEvent
    T.modelB_response T.projected_update

theorem FiniteModelBILVTrace.ssgmStepSizeConditions
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    SSGMStepSizeConditions (ilvRadius r0) :=
  (T.ssgmInputs hdual hr0).1

theorem FiniteModelBILVTrace.followsSampleSubgradientMethod
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    FollowsFiniteProjectedSampleSubgradientMethod
      (fun t y =>
        AppliedModelingLib.FiniteDimensionalNorms.lp p (fun i => y i - T.ideal t i))
      T.project
      (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
      (ilvRadius r0)
      (fun t =>
        lpCostGradientCandidate p
          (fun i =>
            E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
              T.ideal t i))
      (fun _t _i => 0) (fun _t _i => 0) :=
  (T.ssgmInputs hdual hr0).2.1

theorem FiniteModelBILVTrace.trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q r0 : ℝ}
    (T : FiniteModelBILVTrace E p q r0)
    (hdual : HolderDualFinite p q) (hr0 : 0 < r0) :
    ∀ t : ℕ,
      E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
        E.solutionSpace :=
  (T.ssgmInputs hdual hr0).2.2

/-- Source assumptions C1, C2, and C3 from Section 3. -/
def ConditionsC123 {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  E.solutionSpace_nonempty_bounded_closed_convex ∧
    E.uniqueIdealSolutions ∧
      E.idealDistribution_bounded_measurable_density

theorem ConditionsC123.solutionSpace_condition {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} (h : ConditionsC123 E) :
    E.solutionSpace_nonempty_bounded_closed_convex :=
  h.1

theorem ConditionsC123.uniqueIdealSolutions_condition {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} (h : ConditionsC123 E) :
    E.uniqueIdealSolutions :=
  h.2.1

theorem ConditionsC123.idealDistribution_bounded_measurable_density_condition
    {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} (h : ConditionsC123 E) :
    E.idealDistribution_bounded_measurable_density :=
  h.2.2

/--
Concrete reading of source condition C2: the designated ideal is feasible and
is the unique utility-maximizing solution for each voter.
-/
def HasUniqueIdealSolution {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ voter,
    E.ideal voter ∈ E.solutionSpace ∧
      (∀ x, x ∈ E.solutionSpace →
        E.utility voter x ≤ E.utility voter (E.ideal voter)) ∧
      ∀ x, x ∈ E.solutionSpace →
        E.utility voter x = E.utility voter (E.ideal voter) →
          x = E.ideal voter

/--
Source-side reading of the C1 convexity clause in a concrete Lean environment.
This is the direct paper-level source assumption used by the
projection-residual proof.
-/
structure C1ConvexSolutionSpaceSource {Voter Point : Type*}
    [AddCommMonoid Point] [Module ℝ Point]
    (E : ILVEnvironment Voter Point) where
  convex_solutionSpace : Convex ℝ E.solutionSpace

/--
Compatibility adapter for older proof-facing rows that phrase C1 as a
consequence of `ConditionsC123`.
-/
structure ConvexSolutionSpaceSource {Voter Point : Type*}
    [AddCommMonoid Point] [Module ℝ Point]
    (E : ILVEnvironment Voter Point) where
  convex_solutionSpace :
    ConditionsC123 E → Convex ℝ E.solutionSpace

def C1ConvexSolutionSpaceSource.toConvexSolutionSpaceSource
    {Voter Point : Type*} [AddCommMonoid Point] [Module ℝ Point]
    {E : ILVEnvironment Voter Point}
    (S : C1ConvexSolutionSpaceSource E) :
    ConvexSolutionSpaceSource E where
  convex_solutionSpace := fun _ => S.convex_solutionSpace

/--
Environment-indexed finite-coordinate C3 data.

The concrete probability law is the C3 content used by the finite-coordinate
formalization: it is a probability measure on ideal points with a bounded,
measurable density with respect to full-dimensional Lebesgue measure.  The
environment parameter keeps this data aligned with a particular paper model;
it does not add a second opaque C3 proposition.
-/
structure FiniteCoordinateC3Carrier
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  data : FiniteCoordinateIdealDistributionData Coord

def FiniteCoordinateC3Carrier.of_conditions
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteCoordinateIdealDistributionData Coord)
    (_hC : ConditionsC123 E) :
    FiniteCoordinateC3Carrier E :=
  { data := D }

theorem FiniteCoordinateC3Carrier.coordinate_noncollision_ae
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (C : FiniteCoordinateC3Carrier E) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂C.data.idealMeasure, ∀ i, x i ≠ ideal i :=
  C.data.coordinate_noncollision_ae x

/-- Source Definition 1: voter utility is `-||x - x_v||_p`. -/
def IsLpNormedUtilities {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p : SourceNorm) : Prop :=
  ∀ v x, E.utility v x = -E.normDistance p x (E.ideal v)

theorem modelAResponseAt_lpNormedUtilities_iff_normDistance_minimizer
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : IsLpNormedUtilities E p) :
    ModelAResponseAt E q center r voter response ↔
      NormDistanceMinimizerOn E p (E.ideal voter)
        (LocalNeighborhood E q center r) response := by
  constructor
  · intro h
    rcases h with ⟨hmem, hmax⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmax candidate hcandidate
    rw [hUtil voter candidate, hUtil voter response] at hle
    exact neg_le_neg_iff.mp hle
  · intro h
    rcases h with ⟨hmem, hmin⟩
    refine ⟨hmem, ?_⟩
    intro candidate hcandidate
    have hle := hmin candidate hcandidate
    rw [hUtil voter candidate, hUtil voter response]
    exact neg_le_neg hle

theorem normDistanceMinimizerOn_iff_isMinOn
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p : SourceNorm)
    (target : Point) (feasible : Set Point) (response : Point) :
    NormDistanceMinimizerOn E p target feasible response ↔
      response ∈ feasible ∧
        IsMinOn (fun candidate => E.normDistance p candidate target)
          feasible response := by
  rfl

theorem modelAResponseAt_lpNormedUtilities_iff_normDistance_isMinOn
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    (center : Point) (r : ℝ) (voter : Voter) (response : Point)
    (hUtil : IsLpNormedUtilities E p) :
    ModelAResponseAt E q center r voter response ↔
      response ∈ LocalNeighborhood E q center r ∧
        IsMinOn (fun candidate => E.normDistance p candidate (E.ideal voter))
          (LocalNeighborhood E q center r) response := by
  simpa [normDistanceMinimizerOn_iff_isMinOn] using
    modelAResponseAt_lpNormedUtilities_iff_normDistance_minimizer
      E p q center r voter response hUtil

theorem modelAResponseAt_lpNormedUtilities_normDistance_le_candidate
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    {center candidate response : Point} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcandidate : candidate ∈ LocalNeighborhood E q center r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p candidate (E.ideal voter) := by
  have hmin :=
    (modelAResponseAt_lpNormedUtilities_iff_normDistance_minimizer
      E p q center r voter response hUtil).mp hresponse
  exact hmin.2 candidate hcandidate

theorem modelAResponseAt_lpNormedUtilities_normDistance_le_center
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    {center response : Point} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcenter : center ∈ LocalNeighborhood E q center r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_candidate
    E p q hUtil hresponse hcenter

/--
The finite-coordinate interpretation of the abstract `normDistance` field for
an environment whose points are real coordinate vectors.
-/
def UsesFiniteCoordinateNormDistance
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  ∀ p x y, E.normDistance p x y = finiteCoordinateDistance p x y

/--
Finite `L2` norm projection is the identity on feasible raw points.  This is
the exact deterministic condition under which Algorithm 1's projection step
does not change the selected raw Model B response.
-/
theorem algorithm1ProjectedUpdate_eq_raw_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace) :
    next = raw := by
  have hmin :
      IsMinOn (fun x => E.normDistance SourceNorm.l2 x raw)
        E.solutionSpace next := by
    rw [hupdate]
    exact (hproject raw).2
  have hle :
      E.normDistance SourceNorm.l2 next raw ≤
        E.normDistance SourceNorm.l2 raw raw :=
    hmin hraw
  have hdist :
      finiteCoordinateDistance SourceNorm.l2 next raw ≤
        finiteCoordinateDistance SourceNorm.l2 raw raw := by
    simpa [hNorm SourceNorm.l2 next raw, hNorm SourceNorm.l2 raw raw] using hle
  have hnonneg : 0 ≤ finiteCoordinateDistance SourceNorm.l2 next raw :=
    finiteCoordinateDistance_l2_nonneg next raw
  have hzero :
      finiteCoordinateDistance SourceNorm.l2 next raw = 0 := by
    exact le_antisymm
      (by simpa [finiteCoordinateDistance_l2_self raw] using hdist)
      hnonneg
  exact (finiteCoordinateDistance_l2_eq_zero_iff next raw).mp hzero

theorem algorithm1ProjectedUpdate_increment_eq_raw_increment_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ}
    {center raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace) :
    ∀ i : Coord, next i - center i = raw i - center i := by
  intro i
  have hnext :
      next = raw :=
    algorithm1ProjectedUpdate_eq_raw_of_l2_normProjection_feasible
      hNorm hproject hupdate hraw
  rw [hnext]

theorem algorithm1ProjectedUpdate_increment_eq_selectedResponse_increment_of_l2_normProjection_feasible
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {project : (Coord → ℝ) → Coord → ℝ}
    {center raw next response : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hraw : raw ∈ E.solutionSpace)
    (hselected : raw = response) :
    ∀ i : Coord, next i - center i = response i - center i := by
  intro i
  have hinc :=
    algorithm1ProjectedUpdate_increment_eq_raw_increment_of_l2_normProjection_feasible
      (E := E) hNorm (center := center) hproject hupdate hraw i
  rw [hselected] at hinc
  exact hinc

/-- Algorithm 1 local query set specialized to concrete finite-coordinate distances. -/
theorem finiteCoordinate_localNeighborhood_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) (q : SourceNorm)
    (center candidate : Coord → ℝ) (r : ℝ) :
    candidate ∈ LocalNeighborhood E q center r ↔
      candidate ∈ E.solutionSpace ∧
        finiteCoordinateDistance q candidate center ≤ r := by
  simpa [LocalNeighborhood, hNorm q candidate center]

theorem finiteCoordinate_mem_localNeighborhood_self_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.l1 center r := by
  rw [finiteCoordinate_localNeighborhood_formula E hNorm]
  exact ⟨hcenter, by
    simpa [finiteCoordinateDistance_l1_self] using hr⟩

theorem finiteCoordinate_mem_localNeighborhood_self_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.l2 center r := by
  rw [finiteCoordinate_localNeighborhood_formula E hNorm]
  exact ⟨hcenter, by
    simpa [finiteCoordinateDistance_l2_self] using hr⟩

theorem finiteCoordinate_mem_localNeighborhood_self_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E SourceNorm.linfty center r := by
  rw [finiteCoordinate_localNeighborhood_formula E hNorm]
  exact ⟨hcenter, by
    simpa [finiteCoordinateDistance_linf_self] using hr⟩

theorem finiteCoordinate_mem_localNeighborhood_self_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : ℝ} (hp : 0 < p)
    {center : Coord → ℝ} {r : ℝ}
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    center ∈ LocalNeighborhood E (SourceNorm.lp p) center r := by
  rw [finiteCoordinate_localNeighborhood_formula E hNorm]
  exact ⟨hcenter, by
    simpa [finiteCoordinateDistance_lp_self_of_pos (p := p) hp] using hr⟩

theorem finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.l1 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p SourceNorm.l1 hUtil hresponse
    (finiteCoordinate_mem_localNeighborhood_self_l1 E hNorm hcenter hr)

theorem finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.l2 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p SourceNorm.l2 hUtil hresponse
    (finiteCoordinate_mem_localNeighborhood_self_l2 E hNorm hcenter hr)

theorem finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p SourceNorm.linfty hUtil hresponse
    (finiteCoordinate_mem_localNeighborhood_self_linf E hNorm hcenter hr)

theorem finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} {q : ℝ} (hq : 0 < q)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E (SourceNorm.lp q) center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p (SourceNorm.lp q) hUtil hresponse
    (finiteCoordinate_mem_localNeighborhood_self_lp E hNorm hq hcenter hr)

theorem modelAResponseAt_theorem1NormPair_lpNormedUtilities_normDistance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : SourceNorm} (hpq : Theorem1NormPair p q)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E p)
    (hresponse : ModelAResponseAt E q center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    E.normDistance p response (E.ideal voter) ≤
      E.normDistance p center (E.ideal voter) := by
  rcases hpq with hpq | hpq | hpq
  · rcases hpq with ⟨rfl, rfl⟩
    exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l2
      E hNorm hUtil hresponse hcenter hr
  · rcases hpq with ⟨rfl, rfl⟩
    exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_linf
      E hNorm hUtil hresponse hcenter hr
  · rcases hpq with ⟨rfl, rfl⟩
    exact finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l1
      E hNorm hUtil hresponse hcenter hr

theorem finiteCoordinate_modelAResponseAt_l1_linf_distance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.l1 response (E.ideal voter) ≤
      finiteCoordinateDistance SourceNorm.l1 center (E.ideal voter) := by
  have hle :
      E.normDistance SourceNorm.l1 response (E.ideal voter) ≤
        E.normDistance SourceNorm.l1 center (E.ideal voter) :=
    finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_linf
      E hNorm hUtil hresponse hcenter hr
  simpa [hNorm SourceNorm.l1 response (E.ideal voter),
    hNorm SourceNorm.l1 center (E.ideal voter)] using hle

theorem finiteCoordinate_modelAResponseAt_linf_l1_distance_le_center
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hresponse : ModelAResponseAt E SourceNorm.l1 center r voter response)
    (hcenter : center ∈ E.solutionSpace) (hr : 0 ≤ r) :
    finiteCoordinateDistance SourceNorm.linfty response (E.ideal voter) ≤
      finiteCoordinateDistance SourceNorm.linfty center (E.ideal voter) := by
  have hle :
      E.normDistance SourceNorm.linfty response (E.ideal voter) ≤
        E.normDistance SourceNorm.linfty center (E.ideal voter) :=
    finiteCoordinate_modelAResponseAt_lpNormedUtilities_normDistance_le_center_l1
      E hNorm hUtil hresponse hcenter hr
  simpa [hNorm SourceNorm.linfty response (E.ideal voter),
    hNorm SourceNorm.linfty center (E.ideal voter)] using hle

/--
Concrete finite-coordinate semantics for the Model A branch of Algorithm 1.

As with `FiniteModelBILVTrace`, this package is not derived from the abstract
`E.respondsAccordingTo modelA` flag.  It is the deterministic bridge target:
constructing this package from the source sampling/response semantics gives
feasibility of the environment trajectory and the one-step Model A distance
descent facts used by the remaining reductions.
-/
structure FiniteModelAILVTrace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (q : SourceNorm) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  voter : ℕ → Voter
  raw : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E q project
  initial_feasible :
    E.trajectory q VoterResponseModel.modelA 0 ∈ E.solutionSpace
  modelA_response :
    ∀ t : ℕ,
      ModelAResponseAt E q
        (E.trajectory q VoterResponseModel.modelA t)
        (ilvRadius r0 (t + 1)) (voter t) (raw t)
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory q VoterResponseModel.modelA (t + 1))

theorem FiniteModelAILVTrace.raw_mem_localNeighborhood
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) (t : ℕ) :
    T.raw t ∈
      LocalNeighborhood E q (E.trajectory q VoterResponseModel.modelA t)
        (ilvRadius r0 (t + 1)) :=
  (T.modelA_response t).1

theorem FiniteModelAILVTrace.raw_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) (t : ℕ) :
    T.raw t ∈ E.solutionSpace :=
  localNeighborhood_mem_solutionSpace (T.raw_mem_localNeighborhood t)

theorem FiniteModelAILVTrace.trajectory_mem_solutionSpace
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0) :
    ∀ t : ℕ, E.trajectory q VoterResponseModel.modelA t ∈ E.solutionSpace :=
  algorithm1ProjectedUpdates_mem_solutionSpace_of_normProjection
    T.project_norm T.initial_feasible T.projected_update

theorem FiniteModelAILVTrace.raw_normDistance_le_center_of_center_mem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q : SourceNorm} {r0 : ℝ}
    (T : FiniteModelAILVTrace E q r0)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (t : ℕ)
    (hcenter :
      E.trajectory q VoterResponseModel.modelA t ∈
        LocalNeighborhood E q
          (E.trajectory q VoterResponseModel.modelA t)
          (ilvRadius r0 (t + 1))) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p (E.trajectory q VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact modelAResponseAt_lpNormedUtilities_normDistance_le_center
    E p q hUtil (T.modelA_response t) hcenter

theorem FiniteModelAILVTrace.raw_normDistance_le_center_l1
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.l1 r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.l1 VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_of_center_mem hUtil t
    (finiteCoordinate_mem_localNeighborhood_self_l1 E hNorm
      (T.trajectory_mem_solutionSpace t)
      (ilvRadius_nonneg (le_of_lt hr0) (t + 1)))

theorem FiniteModelAILVTrace.raw_normDistance_le_center_l2
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.l2 r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_of_center_mem hUtil t
    (finiteCoordinate_mem_localNeighborhood_self_l2 E hNorm
      (T.trajectory_mem_solutionSpace t)
      (ilvRadius_nonneg (le_of_lt hr0) (t + 1)))

theorem FiniteModelAILVTrace.raw_normDistance_le_center_linf
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {r0 : ℝ}
    (T : FiniteModelAILVTrace E SourceNorm.linfty r0)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory SourceNorm.linfty VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_of_center_mem hUtil t
    (finiteCoordinate_mem_localNeighborhood_self_linf E hNorm
      (T.trajectory_mem_solutionSpace t)
      (ilvRadius_nonneg (le_of_lt hr0) (t + 1)))

theorem FiniteModelAILVTrace.raw_normDistance_le_center_lp
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {q r0 : ℝ}
    (T : FiniteModelAILVTrace E (SourceNorm.lp q) r0)
    (hNorm : UsesFiniteCoordinateNormDistance E) (hq : 0 < q)
    {p : SourceNorm} (hUtil : IsLpNormedUtilities E p)
    (hr0 : 0 < r0) (t : ℕ) :
    E.normDistance p (T.raw t) (E.ideal (T.voter t)) ≤
      E.normDistance p
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelA t)
        (E.ideal (T.voter t)) := by
  exact T.raw_normDistance_le_center_of_center_mem hUtil t
    (finiteCoordinate_mem_localNeighborhood_self_lp E hNorm hq
      (T.trajectory_mem_solutionSpace t)
      (ilvRadius_nonneg (le_of_lt hr0) (t + 1)))

/--
Deterministic finite-coordinate input package for the Theorem 2 SSGM route.

This is the certificate a future stochastic subgradient convergence theorem
should consume after the abstract source assumptions have been interpreted as
finite-coordinate norm, C3 density, and Model B trace data.
-/
structure Theorem2FiniteSSGMBridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) (p q : ℝ) where
  r0 : ℝ
  r0_pos : 0 < r0
  hNorm : UsesFiniteCoordinateNormDistance E
  c3 : FiniteCoordinateC3Carrier E
  trace : FiniteModelBILVTrace E p q r0

theorem Theorem2FiniteSSGMBridge.ssgmInputs
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q)
    (hdual : HolderDualFinite p q) :
    SSGMStepSizeConditions (ilvRadius B.r0) ∧
      FollowsFiniteProjectedSampleSubgradientMethod
        (fun t y =>
          AppliedModelingLib.FiniteDimensionalNorms.lp p
            (fun i => y i - B.trace.ideal t i))
        B.trace.project
        (E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB)
        (ilvRadius B.r0)
        (fun t =>
          lpCostGradientCandidate p
            (fun i =>
              E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t i -
                B.trace.ideal t i))
        (fun _t _i => 0) (fun _t _i => 0) ∧
      ∀ t : ℕ,
        E.trajectory (SourceNorm.lp q) VoterResponseModel.modelB t ∈
          E.solutionSpace :=
  B.trace.ssgmInputs hdual B.r0_pos

theorem Theorem2FiniteSSGMBridge.coordinate_noncollision_ae
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q) (x : Coord → ℝ) :
    ∀ᵐ ideal ∂B.c3.data.idealMeasure, ∀ i, x i ≠ ideal i :=
  B.c3.coordinate_noncollision_ae x

theorem Theorem2FiniteSSGMBridge.lpCost_eq_selectedVoter_lpCost
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {p q : ℝ}
    (B : Theorem2FiniteSSGMBridge E p q) :
    ∀ t : ℕ, ∀ y : Coord → ℝ,
      AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - B.trace.ideal t i) =
        AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun i => y i - E.ideal (B.trace.voter t) i) :=
  B.trace.lpCost_eq_selectedVoter_lpCost

/--
The Theorem 2 finite-coordinate Model B response is inside Algorithm 1's local
query set once projection/feasibility supplies membership in the solution space.
-/
theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hmem : response ∈ E.solutionSpace)
    (hcoord : ∀ i, center i ≠ ideal i)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    response ∈ LocalNeighborhood E (SourceNorm.lp q) center r := by
  rw [finiteCoordinate_localNeighborhood_formula E hNorm]
  exact ⟨hmem,
    modelBFiniteResponseAt_neg_lpCostGradientCandidate_within_radius
      hdual hr hcoord hresponse⟩

/--
Bad-event form of the one-step Model B local-neighborhood bridge.  This is the
one-step version of the trajectory-level bad-event exclusion used by Lemma 3.
-/
theorem modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood_of_notMem_badEvent
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {p q : ℝ} (hdual : HolderDualFinite p q)
    {center ideal response : Coord → ℝ} {r : ℝ}
    (hr : 0 ≤ r)
    (hmem : response ∈ E.solutionSpace)
    (havoid : ideal ∉ coordinateEqualityBadEvent center)
    (hresponse :
      ModelBFiniteResponseAt (SourceNorm.lp q) center r
        (fun i => -lpCostGradientCandidate p (fun j => center j - ideal j) i)
        response) :
    response ∈ LocalNeighborhood E (SourceNorm.lp q) center r := by
  exact modelBFiniteResponseAt_neg_lpCostGradientCandidate_mem_localNeighborhood
    E hNorm hdual hr hmem
    ((notMem_coordinateEqualityBadEvent_iff center ideal).mp havoid)
    hresponse

/--
Definition 1 specialized to concrete finite-coordinate distances.  This is the
main bridge from the paper's `M`-dimensional source formula to the abstract
environment field used by the theorem statements.
-/
theorem finiteCoordinate_lpNormedUtilities_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) (p : SourceNorm) :
    IsLpNormedUtilities E p ↔
      ∀ v x, E.utility v x = -finiteCoordinateDistance p x (E.ideal v) := by
  constructor
  · intro h v x
    simpa [hNorm p x (E.ideal v)] using h v x
  · intro h v x
    simpa [hNorm p x (E.ideal v)] using h v x

/--
Source-faithful finite-coordinate Model A realization of the `L1/L∞` sign
step.  The response is optimal over Algorithm 1's raw query ball; its
subsequent projection onto the solution space is a separate operation.
-/
theorem l1LinfRawResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|) :
    ModelARawResponseAt E SourceNorm.linfty center r voter
      (l1LinfRawResponse center ideal r) := by
  constructor
  · rw [mem_rawLocalNeighborhood_iff E]
    simpa [hNorm SourceNorm.linfty (l1LinfRawResponse center ideal r) center] using
      l1LinfRawResponse_linf_distance_le (center := center) (ideal := ideal) hr
  · intro candidate hcandidate
    rw [mem_rawLocalNeighborhood_iff E] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l1] at hUtil
    rw [hUtil voter candidate, hUtil voter (l1LinfRawResponse center ideal r), hideal]
    apply neg_le_neg
    apply l1LinfRawResponse_minimizes_l1_on_linfBall hr hgood
    simpa [hNorm SourceNorm.linfty candidate center] using hcandidate

/--
The coordinatewise clamp is an exact source Model A response for `L1` utility
and an `L∞` raw query ball, before Algorithm 1 applies its projection.
-/
theorem l1LinfBallResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r) :
    ModelARawResponseAt E SourceNorm.linfty center r voter
      (l1LinfBallResponse center ideal r) := by
  constructor
  · rw [mem_rawLocalNeighborhood_iff E]
    simpa [hNorm SourceNorm.linfty (l1LinfBallResponse center ideal r) center] using
      l1LinfBallResponse_linf_distance_le (center := center) (ideal := ideal) hr
  · intro candidate hcandidate
    rw [mem_rawLocalNeighborhood_iff E] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l1] at hUtil
    rw [hUtil voter candidate, hUtil voter (l1LinfBallResponse center ideal r), hideal]
    apply neg_le_neg
    apply l1LinfBallResponse_minimizes_l1_on_linfBall hr
    simpa [hNorm SourceNorm.linfty candidate center] using hcandidate

/--
The radial response is an exact source Model A response for `L2` utility and
an `L2` raw query ball, before Algorithm 1 applies its separate projection.
-/
theorem l2BallResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l2)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r) :
    ModelARawResponseAt E SourceNorm.l2 center r voter
      (l2BallResponse center ideal r) := by
  constructor
  · rw [mem_rawLocalNeighborhood_iff E]
    simpa [hNorm SourceNorm.l2 (l2BallResponse center ideal r) center] using
      l2BallResponse_l2_distance_le (center := center) (ideal := ideal) hr
  · intro candidate hcandidate
    rw [mem_rawLocalNeighborhood_iff E] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l2] at hUtil
    rw [hUtil voter candidate, hUtil voter (l2BallResponse center ideal r), hideal]
    apply neg_le_neg
    apply l2BallResponse_minimizes_l2_on_l2Ball hr
    simpa [hNorm SourceNorm.l2 candidate center] using hcandidate

/--
Corrected source Model A bridge for `L∞` utility and an `L1` raw query ball.
The active-coordinate gap hypotheses distinguish the ordinary exact step from
the rare crossing and near-tie cases, where Model A may choose another exact
minimizer.
-/
theorem linfL1SingleActiveRawResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal : Coord → ℝ} {r : ℝ} {i0 : Coord} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r)
    (hmax : ∀ i, |center i - ideal i| ≤ |center i0 - ideal i0|)
    (hnoncross : r ≤ |center i0 - ideal i0|)
    (hmargin : ∀ i, i ≠ i0 → |center i - ideal i| ≤
      |center i0 - ideal i0| - r) :
    ModelARawResponseAt E SourceNorm.l1 center r voter
      (linfL1SingleActiveRawResponse center ideal r i0) := by
  constructor
  · rw [mem_rawLocalNeighborhood_iff E]
    rw [hNorm SourceNorm.l1]
    exact linfL1SingleActiveRawResponse_l1_distance_le hr
  · intro candidate hcandidate
    rw [mem_rawLocalNeighborhood_iff E] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.linfty] at hUtil
    rw [hUtil voter candidate,
      hUtil voter (linfL1SingleActiveRawResponse center ideal r i0), hideal]
    apply neg_le_neg
    apply linfL1SingleActiveRawResponse_minimizes_linf_on_l1Ball
      hr hmax hnoncross hmargin
    simpa [hNorm SourceNorm.l1 candidate center] using hcandidate

/-- The canonical response is an exact raw Model A response off the corrected event. -/
theorem linfL1CanonicalRawResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    ModelARawResponseAt E SourceNorm.l1 center r voter
      (linfL1CanonicalRawResponse center ideal r) := by
  exact linfL1SingleActiveRawResponse_is_modelARawResponseAt hNorm hUtil
    hideal hr (linfL1ActiveCoordinate_is_max center ideal) hgood.1 hgood.2

/--
The Borel water-filled response is an exact source Model A response for
`L∞` utility and an `L1` raw query ball, including the corrected exceptional
crossing and near-tie cases.
-/
theorem linfL1WaterfillRawResponse_is_modelARawResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r) :
    ModelARawResponseAt E SourceNorm.l1 center r voter
      (linfL1WaterfillRawResponse center ideal r) := by
  constructor
  · rw [mem_rawLocalNeighborhood_iff E]
    simpa [hNorm SourceNorm.l1 (linfL1WaterfillRawResponse center ideal r) center] using
      linfL1WaterfillRawResponse_l1_distance_le center ideal hr
  · intro candidate hcandidate
    rw [mem_rawLocalNeighborhood_iff E] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.linfty] at hUtil
    rw [hUtil voter candidate, hUtil voter (linfL1WaterfillRawResponse center ideal r), hideal]
    apply neg_le_neg
    apply linfL1WaterfillRawResponse_minimizes_linf_on_l1Ball hr
    simpa [hNorm SourceNorm.l1 candidate center] using hcandidate

/--
Off the corrected exceptional event, every exact raw Model A response equals
the canonical single-active-coordinate response.  Thus no unspecified Model A
tie-breaking remains in the stochastic-subgradient reduction on that event.
-/
theorem modelARawResponseAt_linfL1_eq_canonicalResponse_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter response) :
    response = linfL1CanonicalRawResponse center ideal r := by
  have hcanonical := linfL1CanonicalRawResponse_is_modelARawResponseAt
    hNorm hUtil hideal hr.le hgood
  have hutility : E.utility voter (linfL1CanonicalRawResponse center ideal r) ≤
      E.utility voter response :=
    hresponse.2 _ hcanonical.1
  rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.linfty] at hUtil
  have hcost : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => response i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.linf
        (fun i => linfL1CanonicalRawResponse center ideal r i - ideal i) := by
    rw [hUtil voter (linfL1CanonicalRawResponse center ideal r),
      hUtil voter response, hideal] at hutility
    simpa [finiteCoordinateDistance, finiteCoordinateNorm] using (neg_le_neg hutility)
  have hresponse_ball :
      finiteCoordinateDistance SourceNorm.l1 response center ≤ r := by
    have hresponse_ball_E : E.normDistance SourceNorm.l1 response center ≤ r :=
      (mem_rawLocalNeighborhood_iff E SourceNorm.l1 center response r).mp hresponse.1
    simpa [hNorm SourceNorm.l1 response center] using hresponse_ball_E
  exact linfL1SingleActiveRawResponse_eq_of_linf_cost_le_on_l1Ball hr
    (linfL1ActiveCoordinate_is_max center ideal) hgood.1 hgood.2
    hresponse_ball (by simpa [linfL1CanonicalRawResponse] using hcost)

/-- On the corrected good event, the normalized arbitrary-response direction is the active subgradient. -/
theorem linfL1RawDirection_eq_canonicalDirection_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    linfL1RawDirection center raw r =
      linfL1SingleActiveDirection center ideal
        (linfL1ActiveCoordinate center ideal) := by
  have hraw := modelARawResponseAt_linfL1_eq_canonicalResponse_of_good
    hNorm hUtil hideal hr hgood hresponse
  ext i
  rw [linfL1RawDirection, hraw, linfL1CanonicalRawResponse,
    linfL1SingleActiveRawResponse]
  field_simp [hr.ne']
  ring

/--
Away from the corrected crossing-or-near-tie event, the Borel symmetric
active subgradient is the unique active-coordinate subgradient.
-/
theorem linfL1SymmetricActiveDirection_eq_singleActiveDirection_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    linfL1SymmetricActiveDirection center ideal =
      linfL1SingleActiveDirection center ideal
        (linfL1ActiveCoordinate center ideal) := by
  classical
  let i0 := linfL1ActiveCoordinate center ideal
  have hmax_eq : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) = |center i0 - ideal i0| := by
    exact finiteCoordinate_linf_eq_active_abs
      (linfL1ActiveCoordinate_is_max center ideal)
  have hnonzero : AppliedModelingLib.FiniteDimensionalNorms.linf
      (fun i => center i - ideal i) ≠ 0 := by
    rw [hmax_eq]
    exact ne_of_gt (lt_of_lt_of_le hr hgood.1)
  have hactive : linfL1ActiveCoordinates center ideal = {i0} := by
    apply Finset.ext
    intro i
    constructor
    · intro hi
      by_cases hieq : i = i0
      · simpa [hieq]
      · have hmem : |center i - ideal i| =
          AppliedModelingLib.FiniteDimensionalNorms.linf
            (fun j => center j - ideal j) :=
          (Finset.mem_filter.mp hi).2
        have heq : |center i - ideal i| = |center i0 - ideal i0| := by
          rw [hmem, hmax_eq]
        have hstrict : |center i - ideal i| < |center i0 - ideal i0| := by
          exact lt_of_le_of_lt (hgood.2 i (by simpa [i0] using hieq))
            (sub_lt_self _ hr)
        exact False.elim ((ne_of_lt hstrict) heq)
    · intro hi
      have hieq : i = i0 := by simpa using hi
      subst i
      exact linfL1ActiveCoordinate_mem_activeCoordinates center ideal
  rw [linfL1SymmetricActiveDirection]
  simp only [if_neg hnonzero]
  rw [hactive]
  funext i
  by_cases hi : i = i0 <;> simp [i0, linfL1SingleActiveDirection, hi]

/-- On the corrected good event, the raw direction equals the symmetric Borel subgradient. -/
theorem linfL1RawDirection_eq_symmetricDirection_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    linfL1RawDirection center raw r =
      linfL1SymmetricActiveDirection center ideal := by
  rw [linfL1RawDirection_eq_canonicalDirection_of_good
    hNorm hUtil hideal hr hgood hresponse]
  symm
  exact linfL1SymmetricActiveDirection_eq_singleActiveDirection_of_good hr hgood

/-- The symmetric-direction perturbation is zero on the corrected good event. -/
theorem linfL1RawDirectionSymmetricPerturbation_eq_zero_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    linfL1RawDirectionSymmetricPerturbation center ideal raw r = 0 := by
  unfold linfL1RawDirectionSymmetricPerturbation
  rw [linfL1RawDirection_eq_symmetricDirection_of_good
    hNorm hUtil hideal hr hgood hresponse]
  ext i
  simp

/--
For the concrete water-filled response, corrected goodness forces the unique
single-active optimizer; this statement is purely finite-dimensional and does
not depend on an ambient voting environment.
-/
theorem linfL1WaterfillRawResponse_eq_canonicalResponse_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    linfL1WaterfillRawResponse center ideal r =
      linfL1CanonicalRawResponse center ideal r := by
  apply linfL1SingleActiveRawResponse_eq_of_linf_cost_le_on_l1Ball hr
    (linfL1ActiveCoordinate_is_max center ideal) hgood.1 hgood.2
  · exact linfL1WaterfillRawResponse_l1_distance_le center ideal hr.le
  · apply linfL1WaterfillRawResponse_minimizes_linf_on_l1Ball hr.le
    exact linfL1SingleActiveRawResponse_l1_distance_le hr.le

/-- The normalized water-filled direction is symmetric-active off the corrected event. -/
theorem linfL1WaterfillRawDirection_eq_symmetricDirection_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    linfL1RawDirection center (linfL1WaterfillRawResponse center ideal r) r =
      linfL1SymmetricActiveDirection center ideal := by
  rw [linfL1WaterfillRawResponse_eq_canonicalResponse_of_good hr hgood,
    linfL1SymmetricActiveDirection_eq_singleActiveDirection_of_good hr hgood]
  ext i
  rw [linfL1RawDirection, linfL1CanonicalRawResponse,
    linfL1SingleActiveRawResponse]
  field_simp [hr.ne']
  ring

/-- The concrete water-filled symmetric perturbation vanishes on the corrected good event. -/
theorem linfL1WaterfillRawDirectionSymmetricPerturbation_eq_zero_of_good
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {center ideal : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r) :
    linfL1RawDirectionSymmetricPerturbation
      center ideal (linfL1WaterfillRawResponse center ideal r) r = 0 := by
  unfold linfL1RawDirectionSymmetricPerturbation
  rw [linfL1WaterfillRawDirection_eq_symmetricDirection_of_good hr hgood]
  ext i
  simp

/-- The normalized raw direction is the symmetric sampled subgradient plus its perturbation. -/
theorem linfL1RawDirection_eq_symmetricDirection_add_perturbation
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal raw : Coord → ℝ) (r : ℝ) :
    linfL1RawDirection center raw r = fun i =>
      linfL1SymmetricActiveDirection center ideal i +
        linfL1RawDirectionSymmetricPerturbation center ideal raw r i := by
  ext i
  simp only [linfL1RawDirectionSymmetricPerturbation]
  ring

/--
Corrected Appendix Lemma 2, Part A for an arbitrary exact Model A response:
outside the crossing-or-near-tie event, its normalized raw displacement is a
valid `L∞` sample-cost subgradient.  No tie-breaking rule is needed because
the local minimizer is unique on this event.
-/
theorem finiteSubgradientAt_linfL1RawDirection_of_notMem_correctedBadEvent
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : ideal ∉ linfL1CorrectedBadEvent center r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    FiniteSubgradientAt
      (fun y : Coord → ℝ =>
        AppliedModelingLib.FiniteDimensionalNorms.linf (fun i => y i - ideal i))
      center (linfL1RawDirection center raw r) := by
  have hgood' : LinfL1CorrectedGood center ideal r := by
    simpa [linfL1CorrectedBadEvent] using hgood
  rw [linfL1RawDirection_eq_canonicalDirection_of_good
    hNorm hUtil hideal hr hgood' hresponse]
  exact finiteSubgradientAt_linfL1SingleActiveDirection_of_max
    (linfL1ActiveCoordinate_is_max center ideal)

/-- The corrected perturbation is zero on the corrected good event. -/
theorem linfL1RawDirectionSubgradientPerturbation_eq_zero_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    linfL1RawDirectionSubgradientPerturbation center ideal raw r = 0 := by
  unfold linfL1RawDirectionSubgradientPerturbation
  rw [linfL1RawDirection_eq_canonicalDirection_of_good
    hNorm hUtil hideal hr hgood hresponse]
  ext i
  simp

/-- The arbitrary raw direction is the canonical sample subgradient plus its rare perturbation. -/
theorem linfL1RawDirection_eq_canonicalDirection_add_perturbation
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (center ideal raw : Coord → ℝ) (r : ℝ) :
    linfL1RawDirection center raw r = fun i =>
      linfL1SingleActiveDirection center ideal (linfL1ActiveCoordinate center ideal) i +
        linfL1RawDirectionSubgradientPerturbation center ideal raw r i := by
  ext i
  simp only [linfL1RawDirectionSubgradientPerturbation]
  ring

/-- Every exact raw Model A response supplies the uniform corrected perturbation bound. -/
theorem linfL1RawResponse_perturbation_l2Sq_le_four_card
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {center ideal raw : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hr : 0 < r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw) :
    AppliedModelingLib.FiniteDimensionalNorms.l2Sq
      (linfL1RawDirectionSubgradientPerturbation center ideal raw r) ≤
      4 * Fintype.card Coord := by
  apply linfL1RawDirectionSubgradientPerturbation_l2Sq_le_four_card hr
  have hraw_ball_E : E.normDistance SourceNorm.l1 raw center ≤ r :=
    (mem_rawLocalNeighborhood_iff E SourceNorm.l1 center raw r).mp hresponse.1
  simpa [hNorm SourceNorm.l1 raw center] using hraw_ball_E

/--
The actual Model A response and subsequent projection have the canonical
`L∞/L1` projected-subgradient form whenever the corrected good event holds.
-/
theorem finiteProjectedSSGMUpdateAt_of_modelARawResponseAt_linfL1_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    {center ideal raw next : Coord → ℝ} {r : ℝ} {voter : Voter}
    {project : (Coord → ℝ) → Coord → ℝ}
    (hideal : E.ideal voter = ideal)
    (hr : 0 < r)
    (hgood : LinfL1CorrectedGood center ideal r)
    (hresponse : ModelARawResponseAt E SourceNorm.l1 center r voter raw)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project center r
      (linfL1SingleActiveDirection center ideal
        (linfL1ActiveCoordinate center ideal))
      (fun _ => 0) (fun _ => 0) next := by
  apply finiteProjectedSSGMUpdateAt_of_linfL1CanonicalRawResponse project r
  · exact modelARawResponseAt_linfL1_eq_canonicalResponse_of_good
      hNorm hUtil hideal hr hgood hresponse
  · exact hproject

/--
On the source slab-good event, every exact raw Model A `L1/L∞` response is
the coordinate-sign response.  This removes any tie-breaking ambiguity from
the appendix's Model A-to-subgradient step.
-/
theorem modelARawResponseAt_l1Linf_eq_signResponse_of_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    {center ideal response : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|)
    (hresponse : ModelARawResponseAt E SourceNorm.linfty center r voter response) :
    response = l1LinfRawResponse center ideal r := by
  have hraw_ball : l1LinfRawResponse center ideal r ∈
      RawLocalNeighborhood E SourceNorm.linfty center r := by
    rw [mem_rawLocalNeighborhood_iff E]
    simpa [hNorm SourceNorm.linfty (l1LinfRawResponse center ideal r) center] using
      l1LinfRawResponse_linf_distance_le (center := center) (ideal := ideal) hr
  have hutility : E.utility voter (l1LinfRawResponse center ideal r) ≤
      E.utility voter response :=
    hresponse.2 _ hraw_ball
  rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l1] at hUtil
  have hcost : AppliedModelingLib.FiniteDimensionalNorms.l1
      (fun i => response i - ideal i) ≤
      AppliedModelingLib.FiniteDimensionalNorms.l1
        (fun i => l1LinfRawResponse center ideal r i - ideal i) := by
    rw [hUtil voter (l1LinfRawResponse center ideal r), hUtil voter response, hideal] at hutility
    simpa [finiteCoordinateDistance, finiteCoordinateNorm] using (neg_le_neg hutility)
  have hresponse_ball :
      finiteCoordinateDistance SourceNorm.linfty response center ≤ r := by
    have hresponse_ball_E : E.normDistance SourceNorm.linfty response center ≤ r :=
      (mem_rawLocalNeighborhood_iff E SourceNorm.linfty center response r).mp hresponse.1
    simpa [hNorm SourceNorm.linfty response center] using hresponse_ball_E
  exact l1LinfRawResponse_eq_of_l1_cost_le_on_linfBall hr hgood hresponse_ball hcost

/--
The source raw Model A response, its separate Algorithm 1 projection, and the
slab-good event yield the exact `L1` projected stochastic-subgradient update.
-/
theorem finiteProjectedSSGMUpdateAt_of_modelARawResponseAt_l1Linf_good
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    {center ideal raw next : Coord → ℝ} {r : ℝ} {voter : Voter}
    {project : (Coord → ℝ) → Coord → ℝ}
    (hideal : E.ideal voter = ideal)
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|)
    (hresponse : ModelARawResponseAt E SourceNorm.linfty center r voter raw)
    (hproject : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectedSSGMUpdateAt project center r
      (lpCostGradientCandidate 1 (fun i => center i - ideal i))
      (fun _ => 0) (fun _ => 0) next := by
  apply finiteProjectedSSGMUpdateAt_of_l1LinfRawResponse project r
  · exact modelARawResponseAt_l1Linf_eq_signResponse_of_good
      hNorm hUtil hideal hr hgood hresponse
  · exact hproject

/--
Conditional finite-coordinate Model A realization of the source `L1/L∞`
sign-step argument.  The feasibility premise is explicit: C1 convexity alone
does not imply that this coordinatewise step remains in an arbitrary convex
solution space.
-/
theorem l1LinfRawResponse_is_modelAResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    {center ideal : Coord → ℝ} {r : ℝ} {voter : Voter}
    (hideal : E.ideal voter = ideal)
    (hraw_mem : l1LinfRawResponse center ideal r ∈ E.solutionSpace)
    (hr : 0 ≤ r)
    (hgood : ∀ i, r ≤ |center i - ideal i|) :
    ModelAResponseAt E SourceNorm.linfty center r voter
      (l1LinfRawResponse center ideal r) := by
  constructor
  · rw [finiteCoordinate_localNeighborhood_formula E hNorm]
    exact ⟨hraw_mem, l1LinfRawResponse_linf_distance_le hr⟩
  · intro candidate hcandidate
    rw [finiteCoordinate_localNeighborhood_formula E hNorm] at hcandidate
    rw [finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l1] at hUtil
    rw [hUtil voter candidate, hUtil voter (l1LinfRawResponse center ideal r), hideal]
    apply neg_le_neg
    exact l1LinfRawResponse_minimizes_l1_on_linfBall hr hgood hcandidate.2

/-- Definition 1 specialized to the finite-coordinate `L1` formula. -/
theorem finiteCoordinate_l1NormedUtilities_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.l1 ↔
      ∀ v x, E.utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.l1
          (fun m => x m - E.ideal v m) := by
  simpa [finiteCoordinateDistance, finiteCoordinateNorm] using
    finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l1

/-- Definition 1 specialized to the finite-coordinate `L2` formula. -/
theorem finiteCoordinate_l2NormedUtilities_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.l2 ↔
      ∀ v x, E.utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.l2
          (fun m => x m - E.ideal v m) := by
  simpa [finiteCoordinateDistance, finiteCoordinateNorm] using
    finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.l2

/-- Definition 1 specialized to the finite-coordinate `L∞` formula. -/
theorem finiteCoordinate_linfNormedUtilities_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) :
    IsLpNormedUtilities E SourceNorm.linfty ↔
      ∀ v x, E.utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.linf
          (fun m => x m - E.ideal v m) := by
  simpa [finiteCoordinateDistance, finiteCoordinateNorm] using
    finiteCoordinate_lpNormedUtilities_formula E hNorm SourceNorm.linfty

/-- Definition 1 specialized to the finite-coordinate finite-`Lp` formula. -/
theorem finiteCoordinate_lpRealNormedUtilities_formula
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (hNorm : UsesFiniteCoordinateNormDistance E) (p : ℝ) :
    IsLpNormedUtilities E (SourceNorm.lp p) ↔
      ∀ v x, E.utility v x =
        -AppliedModelingLib.FiniteDimensionalNorms.lp p
          (fun m => x m - E.ideal v m) := by
  simpa [finiteCoordinateDistance, finiteCoordinateNorm] using
    finiteCoordinate_lpNormedUtilities_formula E hNorm (SourceNorm.lp p)

/--
Data for the weighted-Euclidean utility formula in source Definition 2.  The
subspace distances stand for `||x^k - x_v^k||_2`; the final proof layer should
replace this abstract component distance with finite-dimensional Euclidean
coordinates.
-/
structure WeightedEuclideanStructure
    (Voter Point Component : Type*) where
  components : Finset Component
  weight : Voter → Component → ℝ
  weightNorm2 : Voter → ℝ
  componentDistance : Component → Point → Voter → ℝ

/--
Finite-coordinate joint voter data for Definition 2.  One sample contains the
entire nonnegative weight vector and ideal point; their dependence within a
voter is retained, while the canonical process later draws these joint samples
independently over time.
-/
structure WeightedEuclideanJointSampleData
    (Coord Component : Type*) [Fintype Coord] [Fintype Component] where
  jointMeasure : Measure ((Component → ℝ) × (Coord → ℝ))
  probability : IsProbabilityMeasure jointMeasure
  densityBound : ℝ≥0∞
  densityBound_ne_top : densityBound ≠ ⊤
  hasBoundedDensity :
    AppliedModelingLib.Probability.HasBoundedDensity
      ((volume : Measure (Component → ℝ)).prod (volume : Measure (Coord → ℝ)))
      jointMeasure densityBound
  /-- The paper states that the joint voter density is measurable, not merely
  that the resulting measure has a bounded-density representation. -/
  joint_density_measurable :
    ∃ density : ((Component → ℝ) × (Coord → ℝ)) → ℝ≥0∞,
      Measurable density ∧
        jointMeasure =
          ((volume : Measure (Component → ℝ)).prod (volume : Measure (Coord → ℝ))).withDensity
            density ∧
          ∀ᵐ sample ∂((volume : Measure (Component → ℝ)).prod
            (volume : Measure (Coord → ℝ))), density sample ≤ densityBound
  idealDistribution : FiniteCoordinateIdealDistributionData Coord
  ideal_marginal : Measure.map Prod.snd jointMeasure = idealDistribution.idealMeasure
  weightSet : Set (Component → ℝ)
  weightSet_nonempty : weightSet.Nonempty
  weightSet_bounded : Bornology.IsBounded weightSet
  weightSet_closed : IsClosed weightSet
  weightSet_convex : Convex ℝ weightSet
  weightSet_nonnegative : ∀ weight, weight ∈ weightSet → ∀ k, 0 ≤ weight k
  weight_ae_mem_set : ∀ᵐ sample ∂jointMeasure, sample.1 ∈ weightSet
  weight_nonzero_ae : ∀ᵐ sample ∂jointMeasure, sample.1 ≠ 0
  component_nonempty : Nonempty Component
  coordinate_nonempty : Nonempty Coord
  componentBlock : Component → Finset Coord
  componentBlocks_nonempty : ∀ k, (componentBlock k).Nonempty
  componentBlocks_disjoint : ∀ k l, k ≠ l →
    Disjoint (componentBlock k) (componentBlock l)
  componentBlocks_cover : ∀ i, ∃ k, i ∈ componentBlock k

namespace WeightedEuclideanJointSampleData

/-- The weight vector carried by one joint Definition 2 sample. -/
def sampleWeight
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ((Component → ℝ) × (Coord → ℝ)) → Component → ℝ :=
  fun sample => sample.1

/-- The Euclidean normalization of the weight vector in one joint sample. -/
noncomputable def sampleWeightNorm2
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ((Component → ℝ) × (Coord → ℝ)) → ℝ :=
  fun sample => AppliedModelingLib.FiniteDimensionalNorms.l2 (sampleWeight D sample)

/-- The common full ideal vector, restricted later to the relevant component block. -/
def sampleIdeal
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ((Component → ℝ) × (Coord → ℝ)) → Component → Coord → ℝ :=
  fun sample _ => sample.2

theorem sampleWeight_nonnegative_ae
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ∀ᵐ sample ∂D.jointMeasure, ∀ k, 0 ≤ D.sampleWeight sample k := by
  filter_upwards [D.weight_ae_mem_set] with sample hmem
  exact D.weightSet_nonnegative sample.1 hmem

theorem sampleWeightNorm2_sq
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component)
    (sample : (Component → ℝ) × (Coord → ℝ)) :
    ∑ k, D.sampleWeight sample k ^ 2 = D.sampleWeightNorm2 sample ^ 2 := by
  calc
    (∑ k, D.sampleWeight sample k ^ 2) =
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq (D.sampleWeight sample) :=
      (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_eq_sum_sq _).symm
    _ = D.sampleWeightNorm2 sample ^ 2 := by
      simpa [sampleWeightNorm2] using
        (AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq
          (D.sampleWeight sample)).symm

theorem sampleWeightNorm2_pos_ae
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ∀ᵐ sample ∂D.jointMeasure, 0 < D.sampleWeightNorm2 sample := by
  filter_upwards [D.weight_nonzero_ae] with sample hnonzero
  apply AppliedModelingLib.FiniteDimensionalNorms.normL2_pos_of_exists_ne_zero
  by_contra hnot
  apply hnonzero
  funext k
  by_contra hk
  exact hnot ⟨k, hk⟩

theorem normalizedWeight_nonnegative_ae
    {Coord Component : Type*} [Fintype Coord] [Fintype Component]
    (D : WeightedEuclideanJointSampleData Coord Component) :
    ∀ᵐ sample ∂D.jointMeasure, ∀ k,
      0 ≤ D.sampleWeight sample k / D.sampleWeightNorm2 sample := by
  filter_upwards [D.sampleWeight_nonnegative_ae, D.sampleWeightNorm2_pos_ae]
    with sample hweight hnorm
  intro k
  exact div_nonneg (hweight k) hnorm.le

end WeightedEuclideanJointSampleData

/-- Source Definition 2 formula: `- sum_k w_v^k / ||w_v||_2 * ||x^k-x_v^k||_2`. -/
noncomputable def weightedEuclideanUtilityFormula
    {Voter Point Component : Type*}
    (W : WeightedEuclideanStructure Voter Point Component)
    (v : Voter) (x : Point) : ℝ :=
  -W.components.sum
    (fun k => (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v)

theorem weightedEuclideanUtilityFormula_eq_neg_sum
    {Voter Point Component : Type*}
    (W : WeightedEuclideanStructure Voter Point Component)
    (v : Voter) (x : Point) :
    weightedEuclideanUtilityFormula W v x =
      -W.components.sum
        (fun k =>
          (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  rfl

/-- Source Definition 2 as a predicate over the paper utility function. -/
def IsWeightedEuclideanUtilitiesWith
    {Voter Point Component : Type*}
    (E : ILVEnvironment Voter Point)
    (W : WeightedEuclideanStructure Voter Point Component) : Prop :=
  ∀ v x, E.utility v x = weightedEuclideanUtilityFormula W v x

theorem IsWeightedEuclideanUtilitiesWith.utility_eq_formula
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (h : IsWeightedEuclideanUtilitiesWith E W)
    (v : Voter) (x : Point) :
    E.utility v x = weightedEuclideanUtilityFormula W v x :=
  h v x

theorem IsWeightedEuclideanUtilitiesWith.utility_eq_neg_sum
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (h : IsWeightedEuclideanUtilitiesWith E W)
    (v : Voter) (x : Point) :
    E.utility v x =
      -W.components.sum
        (fun k =>
          (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  simpa [weightedEuclideanUtilityFormula] using h.utility_eq_formula v x

theorem IsWeightedEuclideanUtilitiesWith.intro_formula
    {Voter Point Component : Type*}
    {E : ILVEnvironment Voter Point}
    {W : WeightedEuclideanStructure Voter Point Component}
    (hformula :
      ∀ v x, E.utility v x = weightedEuclideanUtilityFormula W v x) :
    IsWeightedEuclideanUtilitiesWith E W :=
  hformula

/-- Data for source Definition 3, decomposability across coordinates. -/
structure DecomposableStructure
    (Voter Point Coord : Type*) where
  coords : Finset Coord
  coordinate : Coord → Point → ℝ
  coordinateUtility : Coord → Voter → ℝ → ℝ
  /-- Source Definition 3: each one-coordinate voter utility is concave. -/
  coordinateUtilitiesConcave :
    ∀ coordinate voter, ConcaveOn ℝ Set.univ (coordinateUtility coordinate voter)

/-- Source Definition 3 formula: `sum_m f_v^m(x^m)`. -/
noncomputable def decomposableUtilityFormula
    {Voter Point Coord : Type*}
    (D : DecomposableStructure Voter Point Coord)
    (v : Voter) (x : Point) : ℝ :=
  D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x))

theorem decomposableUtilityFormula_eq_sum
    {Voter Point Coord : Type*}
    (D : DecomposableStructure Voter Point Coord)
    (v : Voter) (x : Point) :
    decomposableUtilityFormula D v x =
      D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  rfl

/-- Source Definition 3 as a predicate over the paper utility function. -/
def IsDecomposableUtilitiesWith
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) : Prop :=
  ∀ v x, E.utility v x = decomposableUtilityFormula D v x

theorem IsDecomposableUtilitiesWith.coordinateUtilitiesConcave
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D) :
    ∀ coordinate voter, ConcaveOn ℝ Set.univ (D.coordinateUtility coordinate voter) :=
  D.coordinateUtilitiesConcave

theorem IsDecomposableUtilitiesWith.utility_eq_formula
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D)
    (v : Voter) (x : Point) :
    E.utility v x = decomposableUtilityFormula D v x :=
  h v x

theorem IsDecomposableUtilitiesWith.utility_eq_sum
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (h : IsDecomposableUtilitiesWith E D)
    (v : Voter) (x : Point) :
    E.utility v x =
      D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  simpa [decomposableUtilityFormula] using h.utility_eq_formula v x

theorem IsDecomposableUtilitiesWith.intro_formula
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (hformula : ∀ v x, E.utility v x = decomposableUtilityFormula D v x) :
    IsDecomposableUtilitiesWith E D :=
  hformula

/--
Source-side deterministic data for Proposition 1's weighted-Euclidean `L2`
Algorithm 1 route.  The source supplies a positive paper radius and the concrete
projected update equation plus sample-subgradient certificates; Lean derives the
proof-facing SSGM recurrence and step-size hypotheses from these fields.
-/
structure WeightedEuclideanL2SSGMTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (_W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  sampleCost : ℕ → (Coord → ℝ) → ℝ
  subgradient : ℕ → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  sampleCost_eq_neg_utility :
    ∀ t : ℕ, ∀ x : Coord → ℝ,
      sampleCost t x = -E.utility (selectedVoter t) x
  projected_update :
    ∀ t : ℕ,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project
          (fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (subgradient t i + noise t i + bias t i))
  sample_subgradient :
    ∀ t : ℕ,
      FiniteSubgradientAt (sampleCost t)
        (E.trajectory SourceNorm.l2 model t) (subgradient t)

/--
Component-level source for Proposition 1's weighted-Euclidean `L2` branch.
Compared with `WeightedEuclideanL2SSGMTraceSource`, this record does not assume
the sampled direction is already a subgradient of the whole weighted sample
cost.  It supplies component subgradients and nonnegative paper weights; Lean
combines them into the whole-sample subgradient below.
-/
structure WeightedEuclideanL2ComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  componentGradient : ℕ → Component → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  coefficient_nonneg :
    ∀ t : ℕ, ∀ k, k ∈ W.components →
      0 ≤ W.weight (selectedVoter t) k / W.weightNorm2 (selectedVoter t)
  component_subgradient :
    ∀ t : ℕ, ∀ k, k ∈ W.components →
      FiniteSubgradientAt
        (fun x : Coord → ℝ => W.componentDistance k x (selectedVoter t))
        (E.trajectory SourceNorm.l2 model t) (componentGradient t k)
  projected_update :
    ∀ t : ℕ,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project
          (fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (W.components.sum
                    (fun k =>
                      (W.weight (selectedVoter t) k /
                          W.weightNorm2 (selectedVoter t)) *
                        componentGradient t k i) +
                  noise t i + bias t i))

/--
The finite-coordinate algebra behind Definition 2's normalized weighted
direction.  Disjoint coordinate blocks and unit component directions turn the
coefficient square-sum condition into an exact Euclidean unit-norm identity.
-/
theorem weightedEuclidean_l2_direction_norm_eq_one_of_coordinate_blocks
    {Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (components : Finset Component) (coefficient : Component → ℝ)
    (componentGradient : Component → Coord → ℝ)
    (hdisjoint :
      ∀ i k l, k ∈ components → l ∈ components → k ≠ l →
        componentGradient k i = 0 ∨ componentGradient l i = 0)
    (hunit : ∀ k, k ∈ components →
      finiteCoordinateNorm SourceNorm.l2 (componentGradient k) = 1)
    (hweights : ∑ k ∈ components, coefficient k ^ 2 = 1) :
    finiteCoordinateNorm SourceNorm.l2
      (fun i => components.sum (fun k => coefficient k * componentGradient k i)) = 1 := by
  rw [finiteCoordinateNorm_l2]
  apply AppliedModelingLib.FiniteDimensionalNorms.l2_finset_weighted_sum_eq_one_of_coordinatewise_disjoint
    components coefficient componentGradient hdisjoint
  · intro k hk
    calc
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq (componentGradient k) =
          AppliedModelingLib.FiniteDimensionalNorms.l2 (componentGradient k) ^ 2 :=
        (AppliedModelingLib.FiniteDimensionalNorms.normL2_sq_eq_normL2Sq _).symm
      _ = 1 := by
        rw [← finiteCoordinateNorm_l2, hunit k hk]
        norm_num
  · exact hweights

/--
The preceding block calculation specialized to Definition 2's coefficients.
The explicit nonzero and squared-norm equations are the normalization facts
needed to interpret `weightNorm2` as the Euclidean norm of the weight vector.
-/
theorem weightedEuclidean_l2_normalized_direction_norm_eq_one_of_coordinate_blocks
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) (v : Voter)
    (componentGradient : Component → Coord → ℝ)
    (hdisjoint :
      ∀ i k l, k ∈ W.components → l ∈ W.components → k ≠ l →
        componentGradient k i = 0 ∨ componentGradient l i = 0)
    (hunit : ∀ k, k ∈ W.components →
      finiteCoordinateNorm SourceNorm.l2 (componentGradient k) = 1)
    (hweightNorm_ne_zero : W.weightNorm2 v ≠ 0)
    (hweightNorm_sq :
      ∑ k ∈ W.components, W.weight v k ^ 2 = W.weightNorm2 v ^ 2) :
    finiteCoordinateNorm SourceNorm.l2
      (fun i => W.components.sum (fun k =>
        (W.weight v k / W.weightNorm2 v) * componentGradient k i)) = 1 := by
  apply weightedEuclidean_l2_direction_norm_eq_one_of_coordinate_blocks
    W.components (fun k => W.weight v k / W.weightNorm2 v)
    componentGradient hdisjoint hunit
  have hweightNorm_sq_ne_zero : W.weightNorm2 v ^ 2 ≠ 0 :=
    pow_ne_zero _ hweightNorm_ne_zero
  calc
    (∑ k ∈ W.components, (W.weight v k / W.weightNorm2 v) ^ 2) =
        ∑ k ∈ W.components, W.weight v k ^ 2 / W.weightNorm2 v ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _hk
      field_simp
    _ = (∑ k ∈ W.components, W.weight v k ^ 2) / W.weightNorm2 v ^ 2 := by
      rw [Finset.sum_div]
    _ = 1 := by
      rw [hweightNorm_sq, div_self hweightNorm_sq_ne_zero]

/--
Definition 2's normalized weighted direction has Euclidean quantity one when
its component distances are Euclidean distances on disjoint coordinate blocks.
-/
theorem weightedEuclidean_l2_normalized_block_direction_norm_eq_one
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) (v : Voter)
    (block : Component → Finset Coord) (ideal : Component → Coord → ℝ)
    (x : Coord → ℝ)
    (hblocks : ∀ k l, k ∈ W.components → l ∈ W.components → k ≠ l →
      Disjoint (block k) (block l))
    (hnonzero : ∀ k, k ∈ W.components →
      ∃ i, i ∈ block k ∧ x i ≠ ideal k i)
    (hweightNorm_ne_zero : W.weightNorm2 v ≠ 0)
    (hweightNorm_sq :
      ∑ k ∈ W.components, W.weight v k ^ 2 = W.weightNorm2 v ^ 2) :
    finiteCoordinateNorm SourceNorm.l2
      (fun i => W.components.sum (fun k =>
        (W.weight v k / W.weightNorm2 v) *
          l2BlockDistanceNormalizedGradient (block k) x (ideal k) i)) = 1 := by
  apply weightedEuclidean_l2_normalized_direction_norm_eq_one_of_coordinate_blocks
    W v (fun k => l2BlockDistanceNormalizedGradient (block k) x (ideal k))
  · exact l2BlockDistanceNormalizedGradients_coordinatewise_disjoint
      W.components block x ideal hblocks
  · intro k hk
    rw [finiteCoordinateNorm_l2]
    exact l2BlockDistanceNormalizedGradient_l2_eq_one
      (block k) x (ideal k) (hnonzero k hk)
  · exact hweightNorm_ne_zero
  · exact hweightNorm_sq

/--
Concrete component-distance trace source for Proposition 1.  This version
expands each weighted-Euclidean component distance as a finite `L2` distance to
an explicit component ideal, and derives the component subgradient certificates
from the local finite-dimensional L2 subgradient theorem.
-/
structure WeightedEuclideanL2ConcreteComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  componentIdeal : Component → Voter → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  coefficient_nonneg :
    ∀ t : ℕ, ∀ k, k ∈ W.components →
      0 ≤ W.weight (selectedVoter t) k / W.weightNorm2 (selectedVoter t)
  component_distance_eq_l2 :
    ∀ t : ℕ, ∀ k, k ∈ W.components → ∀ x : Coord → ℝ,
      W.componentDistance k x (selectedVoter t) =
        finiteCoordinateDistance SourceNorm.l2 x
          (componentIdeal k (selectedVoter t))
  component_noncollision :
    ∀ t : ℕ, ∀ k, k ∈ W.components → ∀ i : Coord,
      E.trajectory SourceNorm.l2 model t i ≠
        componentIdeal k (selectedVoter t) i
  projected_update :
    ∀ t : ℕ,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project
          (fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (W.components.sum
                    (fun k =>
                      (W.weight (selectedVoter t) k /
                          W.weightNorm2 (selectedVoter t)) *
                        lpCostGradientCandidate 2
                          (fun j =>
                            E.trajectory SourceNorm.l2 model t j -
                              componentIdeal k (selectedVoter t) j) i) +
                  noise t i + bias t i))

noncomputable def weightedEuclideanL2ComponentTraceSource_of_concreteComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2ConcreteComponentTraceSource E W model r0) :
    WeightedEuclideanL2ComponentTraceSource E W model r0 where
  project := S.project
  selectedVoter := S.selectedVoter
  componentGradient := fun t k =>
    lpCostGradientCandidate 2
      (fun i =>
        E.trajectory SourceNorm.l2 model t i -
          S.componentIdeal k (S.selectedVoter t) i)
  noise := S.noise
  bias := S.bias
  r0_pos := S.r0_pos
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  coefficient_nonneg := S.coefficient_nonneg
  component_subgradient := by
    intro t k hk
    have hsub :
        FiniteSubgradientAt
          (fun y : Coord → ℝ =>
            finiteCoordinateDistance SourceNorm.l2 y
              (S.componentIdeal k (S.selectedVoter t)))
          (E.trajectory SourceNorm.l2 model t)
          (lpCostGradientCandidate 2
            (fun i =>
              E.trajectory SourceNorm.l2 model t i -
                S.componentIdeal k (S.selectedVoter t) i)) :=
      finiteSubgradientAt_l2DistanceGradientCandidate
        (fun i => S.component_noncollision t k hk i)
    simpa [S.component_distance_eq_l2 t k hk] using hsub
  projected_update := S.projected_update

/--
Source-faithful component trace for Definition 2: each component distance is
the Euclidean distance on its own finite coordinate block, and its direction is
extended by zero on all other coordinates.
-/
structure WeightedEuclideanL2BlockComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  componentBlock : Component → Finset Coord
  componentIdeal : Component → Voter → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  componentBlocks_disjoint :
    ∀ k l, k ∈ W.components → l ∈ W.components → k ≠ l →
      Disjoint (componentBlock k) (componentBlock l)
  weightNorm2_ne_zero :
    ∀ t : ℕ, W.weightNorm2 (selectedVoter t) ≠ 0
  weightNorm2_sq :
    ∀ t : ℕ,
      ∑ k ∈ W.components, W.weight (selectedVoter t) k ^ 2 =
        W.weightNorm2 (selectedVoter t) ^ 2
  coefficient_nonneg :
    ∀ t : ℕ, ∀ k, k ∈ W.components →
      0 ≤ W.weight (selectedVoter t) k / W.weightNorm2 (selectedVoter t)
  component_distance_eq_block_l2 :
    ∀ t : ℕ, ∀ k, k ∈ W.components → ∀ x : Coord → ℝ,
      W.componentDistance k x (selectedVoter t) =
        finiteCoordinateBlockL2Distance (componentBlock k) x
          (componentIdeal k (selectedVoter t))
  component_noncollision :
    ∀ t : ℕ, ∀ k, k ∈ W.components →
      ∃ i, i ∈ componentBlock k ∧
        E.trajectory SourceNorm.l2 model t i ≠
          componentIdeal k (selectedVoter t) i
  projected_update :
    ∀ t : ℕ,
      E.trajectory SourceNorm.l2 model (t + 1) =
        project
          (fun i =>
            E.trajectory SourceNorm.l2 model t i -
              ilvRadius r0 (t + 1) *
                (W.components.sum
                    (fun k =>
                      (W.weight (selectedVoter t) k /
                          W.weightNorm2 (selectedVoter t)) *
                        l2BlockDistanceNormalizedGradient (componentBlock k)
                          (E.trajectory SourceNorm.l2 model t)
                          (componentIdeal k (selectedVoter t)) i) +
                  noise t i + bias t i))

noncomputable def weightedEuclideanL2ComponentTraceSource_of_blockComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2BlockComponentTraceSource E W model r0) :
    WeightedEuclideanL2ComponentTraceSource E W model r0 where
  project := S.project
  selectedVoter := S.selectedVoter
  componentGradient := fun t k =>
    l2BlockDistanceNormalizedGradient (S.componentBlock k)
      (E.trajectory SourceNorm.l2 model t)
      (S.componentIdeal k (S.selectedVoter t))
  noise := S.noise
  bias := S.bias
  r0_pos := S.r0_pos
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  coefficient_nonneg := S.coefficient_nonneg
  component_subgradient := by
    intro t k hk
    have hsub :
        FiniteSubgradientAt
          (fun x : Coord → ℝ =>
            finiteCoordinateBlockL2Distance (S.componentBlock k) x
              (S.componentIdeal k (S.selectedVoter t)))
          (E.trajectory SourceNorm.l2 model t)
          (l2BlockDistanceNormalizedGradient (S.componentBlock k)
            (E.trajectory SourceNorm.l2 model t)
            (S.componentIdeal k (S.selectedVoter t))) :=
      finiteSubgradientAt_blockL2DistanceNormalizedGradient
        (S.componentBlock k) (E.trajectory SourceNorm.l2 model t)
        (S.componentIdeal k (S.selectedVoter t))
        (S.component_noncollision t k hk)
    simpa only [S.component_distance_eq_block_l2 t k hk] using hsub
  projected_update := S.projected_update

/-- Every component direction in the source-faithful block trace has `L2` quantity one. -/
theorem WeightedEuclideanL2BlockComponentTraceSource.componentGradient_l2_eq_one
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2BlockComponentTraceSource E W model r0)
    (t : ℕ) (k : Component) (hk : k ∈ W.components) :
    finiteCoordinateNorm SourceNorm.l2
      (l2BlockDistanceNormalizedGradient (S.componentBlock k)
        (E.trajectory SourceNorm.l2 model t)
        (S.componentIdeal k (S.selectedVoter t))) = 1 := by
  rw [finiteCoordinateNorm_l2]
  exact l2BlockDistanceNormalizedGradient_l2_eq_one
    (S.componentBlock k) (E.trajectory SourceNorm.l2 model t)
    (S.componentIdeal k (S.selectedVoter t))
    (S.component_noncollision t k hk)

/-- The source-faithful block trace has a unit normalized weighted direction at every step. -/
theorem WeightedEuclideanL2BlockComponentTraceSource.weightedDirection_l2_eq_one
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2BlockComponentTraceSource E W model r0) (t : ℕ) :
    finiteCoordinateNorm SourceNorm.l2
      (fun i => W.components.sum (fun k =>
        (W.weight (S.selectedVoter t) k /
            W.weightNorm2 (S.selectedVoter t)) *
          l2BlockDistanceNormalizedGradient (S.componentBlock k)
            (E.trajectory SourceNorm.l2 model t)
            (S.componentIdeal k (S.selectedVoter t)) i)) = 1 := by
  apply weightedEuclidean_l2_normalized_block_direction_norm_eq_one
    W (S.selectedVoter t) S.componentBlock
    (fun k => S.componentIdeal k (S.selectedVoter t))
    (E.trajectory SourceNorm.l2 model t)
  · exact S.componentBlocks_disjoint
  · exact S.component_noncollision t
  · exact S.weightNorm2_ne_zero t
  · exact S.weightNorm2_sq t

noncomputable def weightedEuclideanL2SSGMTraceSource_of_componentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    (S : WeightedEuclideanL2ComponentTraceSource E W model r0) :
    WeightedEuclideanL2SSGMTraceSource E W model r0 where
  project := S.project
  selectedVoter := S.selectedVoter
  sampleCost := fun t x =>
    W.components.sum
      (fun k =>
        (W.weight (S.selectedVoter t) k /
            W.weightNorm2 (S.selectedVoter t)) *
          W.componentDistance k x (S.selectedVoter t))
  subgradient := fun t i =>
    W.components.sum
      (fun k =>
        (W.weight (S.selectedVoter t) k /
            W.weightNorm2 (S.selectedVoter t)) *
          S.componentGradient t k i)
  noise := S.noise
  bias := S.bias
  r0_pos := S.r0_pos
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  sampleCost_eq_neg_utility := by
    intro t x
    have hutility := hW.utility_eq_neg_sum (S.selectedVoter t) x
    linarith
  projected_update := S.projected_update
  sample_subgradient := by
    intro t
    exact
      finiteSubgradientAt_finset_nonneg_weighted_sum
        W.components
        (fun k hk => S.coefficient_nonneg t k hk)
        (fun k hk => S.component_subgradient t k hk)

/--
The source-faithful block trace instantiates the deterministic sampled
subgradient recurrence for the weighted-Euclidean branch of Proposition 1.
-/
noncomputable def weightedEuclideanL2SSGMTraceSource_of_blockComponentTraceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    (S : WeightedEuclideanL2BlockComponentTraceSource E W model r0) :
    WeightedEuclideanL2SSGMTraceSource E W model r0 :=
  weightedEuclideanL2SSGMTraceSource_of_componentTraceSource hW
    (weightedEuclideanL2ComponentTraceSource_of_blockComponentTraceSource S)

/--
Proof-facing deterministic data for Proposition 1's weighted-Euclidean `L2`
Algorithm 1 route after the raw trace source has been converted to the
sample-subgradient method predicate.
-/
structure WeightedEuclideanL2SSGMSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (_W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  sampleCost : ℕ → (Coord → ℝ) → ℝ
  subgradient : ℕ → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  r0_pos : 0 < r0
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  sampleCost_eq_neg_utility :
    ∀ t : ℕ, ∀ x : Coord → ℝ,
      sampleCost t x = -E.utility (selectedVoter t) x
  follows :
    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
      (E.trajectory SourceNorm.l2 model) (ilvRadius r0)
      subgradient noise bias

def weightedEuclideanL2SSGMSource_of_traceSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMTraceSource E W model r0) :
    WeightedEuclideanL2SSGMSource E W model r0 where
  project := S.project
  selectedVoter := S.selectedVoter
  sampleCost := S.sampleCost
  subgradient := S.subgradient
  noise := S.noise
  bias := S.bias
  r0_pos := S.r0_pos
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  sampleCost_eq_neg_utility := S.sampleCost_eq_neg_utility
  follows := by
    refine ⟨?_, S.sample_subgradient⟩
    intro t
    exact (finiteProjectedSSGMUpdateAt_formula
      S.project (E.trajectory SourceNorm.l2 model t) (ilvRadius r0 (t + 1))
      (S.subgradient t) (S.noise t) (S.bias t)
      (E.trajectory SourceNorm.l2 model (t + 1))).mpr
      (S.projected_update t)

theorem WeightedEuclideanL2SSGMSource.trajectory_mem_solutionSpace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (S : WeightedEuclideanL2SSGMSource E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
    (projectionOnto_of_isNormProjectionOnto E SourceNorm.l2 S.project_norm)
    S.follows S.initial_feasible

/--
Concrete SSGM-input carrier for Proposition 1's weighted-Euclidean `L2`
branch.  This package records the deterministic reduction target after the
paper radius has been converted into the step-size conditions consumed by the
future SSGM convergence theorem.
-/
structure WeightedEuclideanL2SSGMInputs
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) (r0 : ℝ) where
  weighted : IsWeightedEuclideanUtilitiesWith E W
  project : (Coord → ℝ) → Coord → ℝ
  selectedVoter : ℕ → Voter
  sampleCost : ℕ → (Coord → ℝ) → ℝ
  subgradient : ℕ → Coord → ℝ
  noise : ℕ → Coord → ℝ
  bias : ℕ → Coord → ℝ
  project_norm : IsNormProjectionOnto E SourceNorm.l2 project
  initial_feasible :
    E.trajectory SourceNorm.l2 model 0 ∈ E.solutionSpace
  sampleCost_eq_neg_utility :
    ∀ t : ℕ, ∀ x : Coord → ℝ,
      sampleCost t x = -E.utility (selectedVoter t) x
  step_sizes : SSGMStepSizeConditions (ilvRadius r0)
  follows :
    FollowsFiniteProjectedSampleSubgradientMethod sampleCost project
      (E.trajectory SourceNorm.l2 model) (ilvRadius r0)
      subgradient noise bias

def weightedEuclideanL2SSGMInputs_of_source
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    (S : WeightedEuclideanL2SSGMSource E W model r0) :
    WeightedEuclideanL2SSGMInputs E W model r0 where
  weighted := hW
  project := S.project
  selectedVoter := S.selectedVoter
  sampleCost := S.sampleCost
  subgradient := S.subgradient
  noise := S.noise
  bias := S.bias
  project_norm := S.project_norm
  initial_feasible := S.initial_feasible
  sampleCost_eq_neg_utility := S.sampleCost_eq_neg_utility
  step_sizes := ilvRadius_ssgmStepSizeConditions S.r0_pos
  follows := S.follows

theorem WeightedEuclideanL2SSGMInputs.trajectory_mem_solutionSpace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (C : WeightedEuclideanL2SSGMInputs E W model r0) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  followsFiniteProjectedSampleSubgradientMethod_mem_of_projectionOnto
    (projectionOnto_of_isNormProjectionOnto E SourceNorm.l2 C.project_norm)
    C.follows C.initial_feasible

theorem WeightedEuclideanL2SSGMInputs.ssgmStepSizeConditions
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel} {r0 : ℝ}
    (C : WeightedEuclideanL2SSGMInputs E W model r0) :
    SSGMStepSizeConditions (ilvRadius r0) :=
  C.step_sizes

/--
The minimization objective corresponding to the paper's social-welfare
maximization target.
-/
noncomputable def socialCostObjective
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) : (Coord → ℝ) → ℝ :=
  fun x => -E.societalUtility x

theorem socialCostObjective_isMinOn_iff_societalUtility_isMaxOn
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) (x : Coord → ℝ) :
    IsMinOn (socialCostObjective E) E.solutionSpace x ↔
      IsMaxOn E.societalUtility E.solutionSpace x := by
  constructor
  · intro hmin
    rw [isMaxOn_iff]
    intro y hy
    have h := (isMinOn_iff.mp hmin) y hy
    dsimp [socialCostObjective] at h
    linarith
  · intro hmax
    rw [isMinOn_iff]
    intro y hy
    have h := (isMaxOn_iff.mp hmax) y hy
    dsimp [socialCostObjective]
    linarith

/--
Source-level social optimum formula for Proposition 1 before conversion to the
proof-facing minimization objective.  The paper states social optima as feasible
maximizers of societal utility; Lean derives the equivalent minimizer statement
for `socialCostObjective`.
-/
structure WeightedEuclideanSocialObjectiveFormulaSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (_W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) where
  mem_socialOptimal_iff_societalUtility_isMaxOn :
    ∀ x : Coord → ℝ,
      x ∈ E.socialOptimal ↔
        x ∈ E.solutionSpace ∧
          IsMaxOn E.societalUtility E.solutionSpace x

/--
Source-level target-identification formula for Proposition 1.  It records the
weighted-Euclidean objective and the exact statement that its feasible minimizers
are the paper's social optima.
-/
structure WeightedEuclideanSocialObjectiveSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (_W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) where
  objective : (Coord → ℝ) → ℝ
  mem_socialOptimal_iff :
    ∀ x : Coord → ℝ,
      x ∈ E.socialOptimal ↔
        x ∈ E.solutionSpace ∧ IsMinOn objective E.solutionSpace x

/--
Deterministic target-identification carrier for Proposition 1.  It isolates
the proof that the weighted-Euclidean objective minimized by the SSGM layer has
exactly the paper's social-optimal set.
-/
structure WeightedEuclideanSocialObjectiveBridge
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component) where
  weighted : IsWeightedEuclideanUtilitiesWith E W
  objective : (Coord → ℝ) → ℝ
  minimizers_eq_socialOptimal :
    {x | x ∈ E.solutionSpace ∧ IsMinOn objective E.solutionSpace x} =
      E.socialOptimal

def weightedEuclideanSocialObjectiveBridge_of_source
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (hW : IsWeightedEuclideanUtilitiesWith E W)
    (S : WeightedEuclideanSocialObjectiveSource E W) :
    WeightedEuclideanSocialObjectiveBridge E W where
  weighted := hW
  objective := S.objective
  minimizers_eq_socialOptimal := by
    ext x
    exact (S.mem_socialOptimal_iff x).symm

noncomputable def weightedEuclideanSocialObjectiveSource_of_formulaSource
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (S : WeightedEuclideanSocialObjectiveFormulaSource E W) :
    WeightedEuclideanSocialObjectiveSource E W where
  objective := socialCostObjective E
  mem_socialOptimal_iff := by
    intro x
    constructor
    · intro hx
      rcases (S.mem_socialOptimal_iff_societalUtility_isMaxOn x).mp hx with
        ⟨hxsol, hmax⟩
      exact
        ⟨hxsol,
          (socialCostObjective_isMinOn_iff_societalUtility_isMaxOn E x).mpr
            hmax⟩
    · rintro ⟨hxsol, hmin⟩
      exact
        (S.mem_socialOptimal_iff_societalUtility_isMaxOn x).mpr
          ⟨hxsol,
            (socialCostObjective_isMinOn_iff_societalUtility_isMaxOn E x).mp
              hmin⟩

theorem WeightedEuclideanSocialObjectiveBridge.mem_socialOptimal_iff
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    (C : WeightedEuclideanSocialObjectiveBridge E W) {x : Coord → ℝ} :
    x ∈ E.socialOptimal ↔
      x ∈ E.solutionSpace ∧ IsMinOn C.objective E.solutionSpace x := by
  rw [← C.minimizers_eq_socialOptimal]
  rfl

/--
Deterministic target-identification carrier for Proposition 2.  It records the
coordinate-wise median-set formula that the decomposable-utility proof must
derive from the source distribution.
-/
structure DecomposableMedianSetSource
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) where
  coordinateMedianSet : Coord → Set ℝ
  mem_medianSet_iff :
    ∀ x : Point,
      x ∈ E.medianSet ↔
        ∀ m, m ∈ D.coords →
          D.coordinate m x ∈ coordinateMedianSet m

/--
Deterministic target-identification carrier for Proposition 2.  It records the
coordinate-wise median-set formula after it has been connected to a
decomposable-utility source instance.
-/
structure DecomposableMedianCarrier
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) where
  decomposable : IsDecomposableUtilitiesWith E D
  coordinateMedianSet : Coord → Set ℝ
  medianSet_formula :
    E.medianSet =
      {x | ∀ m, m ∈ D.coords →
        D.coordinate m x ∈ coordinateMedianSet m}

/--
Concrete median-set source semantics imply the target-identification carrier by
set extensionality.  This keeps the paper-specific median formula visible
instead of hiding it inside `DecomposableMedianCarrier`.
-/
def decomposableMedianCarrier_of_medianSetSource
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (hD : IsDecomposableUtilitiesWith E D)
    (S : DecomposableMedianSetSource E D) :
    DecomposableMedianCarrier E D where
  decomposable := hD
  coordinateMedianSet := S.coordinateMedianSet
  medianSet_formula := by
    ext x
    exact S.mem_medianSet_iff x

theorem DecomposableMedianCarrier.mem_medianSet_iff
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (C : DecomposableMedianCarrier E D) {x : Point} :
    x ∈ E.medianSet ↔
      ∀ m, m ∈ D.coords →
        D.coordinate m x ∈ C.coordinateMedianSet m := by
  rw [C.medianSet_formula]
  rfl

/--
Local-response bridge target for Proposition 2.  The future proof must show
that a Model A `L∞` response to decomposable utilities is coordinate-wise
optimal over the corresponding one-dimensional query windows.
-/
structure DecomposableLinfLocalResponseBridge
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) where
  decomposable : IsDecomposableUtilitiesWith E D
  coordinate_response_optimal :
    ∀ {center response : Point} {r : ℝ} {voter : Voter},
      ModelAResponseAt E SourceNorm.linfty center r voter response →
        ∀ m, m ∈ D.coords →
          IsMaxOn
            (fun z : ℝ => D.coordinateUtility m voter z)
            {z | ∃ candidate,
              candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
                D.coordinate m candidate = z}
            (D.coordinate m response)

/--
Coordinate-replacement semantics for the decomposable/`L∞` Proposition 2
source proof.

It says that, inside one local `L∞` query, any feasible value of one coordinate
can replace that coordinate of a response while leaving all other decomposable
coordinates unchanged and staying feasible.  This is the missing product-box
fact needed to turn a global Model A maximizer of a decomposable sum into
coordinatewise one-dimensional maximizers.
-/
structure DecomposableLinfCoordinateReplacement
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) where
  replace : Point → Coord → ℝ → Point
  replace_mem_local :
    ∀ {center response : Point} {r : ℝ} {voter : Voter}
      (_hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
      {m : Coord} {z : ℝ},
      m ∈ D.coords →
        z ∈ {z | ∃ candidate,
          candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
            D.coordinate m candidate = z} →
          replace response m z ∈ LocalNeighborhood E SourceNorm.linfty center r
  replace_coordinate_self :
    ∀ (response : Point) {m : Coord} {z : ℝ},
      m ∈ D.coords →
        D.coordinate m (replace response m z) = z
  replace_coordinate_other :
    ∀ (response : Point) {m : Coord} {z : ℝ} {l : Coord},
      l ∈ D.coords →
        l ≠ m →
          D.coordinate l (replace response m z) =
            D.coordinate l response

/--
Concrete product-coordinate solution-space semantics for the finite-coordinate
Proposition 2 route.  This is the source-space fact used by the paper's
dimension-by-dimension `L∞` proof sketch: replacing one coordinate of a feasible
point by the same coordinate from another feasible point remains feasible.
-/
structure FiniteCoordinateProductBoxSolutionSpaceSource
    {Voter Coord : Type*} [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  coordinate_update_mem_solutionSpace :
    ∀ {x y : Coord → ℝ},
      x ∈ E.solutionSpace →
        y ∈ E.solutionSpace →
          ∀ m : Coord, Function.update x m (y m) ∈ E.solutionSpace

/--
Concrete finite-coordinate source data that yields
`DecomposableLinfCoordinateReplacement` when decomposable coordinates are the
ambient coordinate projections.  Feasibility comes from explicit product-box
solution-space semantics, rather than from a query-specific local update field.
-/
structure FiniteCoordinateLinfCoordinateReplacementSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (D : DecomposableStructure Voter (Coord → ℝ) Coord) where
  normDistance : UsesFiniteCoordinateNormDistance E
  productBox : FiniteCoordinateProductBoxSolutionSpaceSource E
  coordinate_eq :
    ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m

/--
Finite-coordinate `L∞` box semantics imply the coordinate-replacement property
used by the Proposition 2 local response proof.
-/
noncomputable def decomposableLinfCoordinateReplacement_of_finiteCoordinate
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (S : FiniteCoordinateLinfCoordinateReplacementSource E D) :
    DecomposableLinfCoordinateReplacement E D where
  replace response m z := Function.update response m z
  replace_mem_local := by
    intro center response r voter hresponse m z hm hz
    rcases hz with ⟨candidate, hcandidate_mem, hcandidate_coord⟩
    have hz_eq : z = candidate m := by
      rw [← hcandidate_coord, S.coordinate_eq m hm candidate]
    refine ⟨?_, ?_⟩
    · simpa [hz_eq] using
        S.productBox.coordinate_update_mem_solutionSpace
          hresponse.1.1 hcandidate_mem.1 m
    have hresponse_dist :
        finiteCoordinateDistance SourceNorm.linfty response center ≤ r := by
      simpa [S.normDistance SourceNorm.linfty response center] using
        hresponse.1.2
    have hcandidate_dist :
        finiteCoordinateDistance SourceNorm.linfty candidate center ≤ r := by
      simpa [S.normDistance SourceNorm.linfty candidate center] using
        hcandidate_mem.2
    have hfinite :
        finiteCoordinateDistance SourceNorm.linfty
          (Function.update response m z) center ≤ r := by
      apply finiteCoordinateDistance_linf_le_of_forall_coord_abs_le
      intro i
      by_cases hi : i = m
      · have hz_eq : z = candidate i := by
          rw [hi]
          simpa [S.coordinate_eq m hm candidate] using hcandidate_coord.symm
        simp [Function.update, hi, hz_eq]
        exact le_trans
          (finiteCoordinateDistance_linf_coord_abs_le candidate center m)
          hcandidate_dist
      · rw [Function.update_of_ne hi]
        exact le_trans
          (finiteCoordinateDistance_linf_coord_abs_le response center i)
          hresponse_dist
    simpa [S.normDistance SourceNorm.linfty
      (Function.update response m z) center] using hfinite
  replace_coordinate_self := by
    intro response m z hm
    simp [S.coordinate_eq m hm (Function.update response m z)]
  replace_coordinate_other := by
    intro response m z l hl hne
    simp [S.coordinate_eq l hl (Function.update response m z),
      S.coordinate_eq l hl response, Function.update_of_ne hne]

/--
Derive Proposition 2's local coordinatewise response bridge from decomposable
utilities plus the product-coordinate replacement semantics of an `L∞` query.
-/
noncomputable def decomposableLinfLocalResponseBridge_of_coordinateReplacement
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (hD : IsDecomposableUtilitiesWith E D)
    (R : DecomposableLinfCoordinateReplacement E D) :
    DecomposableLinfLocalResponseBridge E D where
  decomposable := hD
  coordinate_response_optimal := by
    classical
    intro center response r voter hresponse m hm z hz
    let replacement := R.replace response m z
    have hreplacement_mem :
        replacement ∈ LocalNeighborhood E SourceNorm.linfty center r := by
      exact R.replace_mem_local hresponse hm hz
    have hutility_le :
        E.utility voter replacement ≤ E.utility voter response :=
      hresponse.2 replacement hreplacement_mem
    have hsum_le :
        D.coords.sum
            (fun l => D.coordinateUtility l voter
              (D.coordinate l replacement)) ≤
          D.coords.sum
            (fun l => D.coordinateUtility l voter
              (D.coordinate l response)) := by
      simpa [hD.utility_eq_sum voter replacement,
        hD.utility_eq_sum voter response] using hutility_le
    let rest : ℝ :=
      (D.coords.erase m).sum
        (fun l => D.coordinateUtility l voter (D.coordinate l response))
    have hleft :
        D.coords.sum
            (fun l => D.coordinateUtility l voter
              (D.coordinate l replacement)) =
          D.coordinateUtility m voter z + rest := by
      rw [← D.coords.add_sum_erase
        (fun l => D.coordinateUtility l voter (D.coordinate l replacement)) hm]
      congr 1
      · simp [replacement, R.replace_coordinate_self response hm]
      · dsimp [rest]
        apply Finset.sum_congr rfl
        intro l hl
        have hl' := Finset.mem_erase.mp hl
        rw [R.replace_coordinate_other response hl'.2 hl'.1]
    have hright :
        D.coords.sum
            (fun l => D.coordinateUtility l voter
              (D.coordinate l response)) =
          D.coordinateUtility m voter (D.coordinate m response) + rest := by
      rw [← D.coords.add_sum_erase
        (fun l => D.coordinateUtility l voter (D.coordinate l response)) hm]
    have hsum_le' :
        D.coordinateUtility m voter z + rest ≤
          D.coordinateUtility m voter (D.coordinate m response) + rest := by
      simpa [hleft, hright] using hsum_le
    exact (add_le_add_iff_right rest).mp hsum_le'

theorem DecomposableLinfLocalResponseBridge.coordinate_response_isMaxOn
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (C : DecomposableLinfLocalResponseBridge E D)
    {center response : Point} {r : ℝ} {voter : Voter}
    (hresponse : ModelAResponseAt E SourceNorm.linfty center r voter response)
    (m : Coord) (hm : m ∈ D.coords) :
    IsMaxOn
      (fun z : ℝ => D.coordinateUtility m voter z)
      {z | ∃ candidate,
        candidate ∈ LocalNeighborhood E SourceNorm.linfty center r ∧
          D.coordinate m candidate = z}
      (D.coordinate m response) :=
  C.coordinate_response_optimal hresponse m hm

/-- Paper shorthand: ILV converges w.p. 1 to the societal optimum. -/
def ILVConvergesToSocietalOptimal {Voter Point : Type*}
    (E : ILVEnvironment Voter Point)
    (q : SourceNorm) (model : VoterResponseModel) : Prop :=
  E.convergesWithProbabilityOne (E.trajectory q model) E.socialOptimal

/--
Outcome-indexed formulation of Algorithm 1/2 convergence to a social optimum.
Unlike the legacy abstract environment predicate, this statement explicitly
exhibits the probability space and the random trajectory whose almost-sure
limit is socially optimal.
-/
def OutcomeIndexedILVConvergesToSocietalOptimal
    {Voter Omega Point : Type*} [MeasurableSpace Omega] [TopologicalSpace Point]
    (E : ILVEnvironment Voter Point) (mu : Measure Omega)
    (trajectory : ℕ → Omega → Point) : Prop :=
  AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
    mu trajectory E.socialOptimal

/-- Outcome-indexed formulation of convergence to the Proposition 2 median set. -/
def OutcomeIndexedILVConvergesToMedianSet
    {Voter Omega Point : Type*} [MeasurableSpace Omega] [TopologicalSpace Point]
    (E : ILVEnvironment Voter Point) (mu : Measure Omega)
    (trajectory : ℕ → Omega → Point) : Prop :=
  AppliedModelingLib.Optimization.OutcomeIndexedConvergesToSet
    mu trajectory E.medianSet

/-- Paper shorthand: ILV converges w.p. 1 to the median set. -/
def ILVConvergesToMedianSet {Voter Point : Type*}
    (E : ILVEnvironment Voter Point)
    (q : SourceNorm) (model : VoterResponseModel) : Prop :=
  E.convergesWithProbabilityOne (E.trajectory q model) E.medianSet

/-- Paper shorthand: a specific trajectory converges to a point. -/
def ILVTrajectoryConvergesTo {Voter Point : Type*}
    (E : ILVEnvironment Voter Point)
    (q : SourceNorm) (model : VoterResponseModel) (xstar : Point) : Prop :=
  E.convergesToPoint (E.trajectory q model) xstar

/-- Directional equilibrium condition `G(x*) = 0`. -/
def IsDirectionalEquilibrium {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (xstar : Point) : Prop :=
  E.directionalField xstar = E.zeroDirection

/--
Theorem 3's source-defined normalized gradient.  The paper prints the quotient
`grad f_v(x) / ||grad f_v(x)||_2`; when that gradient is zero, the approved
source-definedness convention uses the zero direction instead.
-/
noncomputable def theorem3NormalizedGradientDirection
    {Voter Point : Type*} (E : ILVEnvironment Voter Point)
    (voter : Voter) (x : Point) : Point := by
  classical
  exact if E.utilityGradient voter x = E.zeroDirection then E.zeroDirection else
    E.scalarDirection
      ((E.normDistance SourceNorm.l2
        (E.utilityGradient voter x) E.zeroDirection)⁻¹)
      (E.utilityGradient voter x)

/--
Theorem 3 source formula for the normalized-gradient directional field,
including the explicit zero-gradient branch.

The generic `Point` type is the paper's continuous decision space.  The
environment supplies the source gradient, scalar multiplication, and voter
expectation operations so the paper-facing theorem can expose the displayed
formula without choosing a finite-coordinate representation.
-/
def Theorem3DirectionalFieldFormula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ x : Point,
    E.directionalField x =
      E.voterExpectation
        (fun voter => theorem3NormalizedGradientDirection E voter x)

/--
Finite-coordinate weighted expectation used by the concrete Theorem 3 analytic
model.  This is the finite-support specialization of the paper's voter
expectation operator.
-/
noncomputable def finiteVoterExpectation
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord]
    (weight : Voter → ℝ) (value : Voter → Coord → ℝ) : Coord → ℝ :=
  fun i => ∑ voter : Voter, weight voter * value voter i

/-- Scalar multiplication of a finite-coordinate direction. -/
def finiteScalarDirection
    {Coord : Type*} (a : ℝ) (x : Coord → ℝ) : Coord → ℝ :=
  fun i => a * x i

/-- Finite-coordinate dot product used by the Theorem 3 drift projection. -/
def finiteDot {Coord : Type*} [Fintype Coord]
    (x y : Coord → ℝ) : ℝ :=
  ∑ i : Coord, x i * y i

/--
Concrete finite-coordinate normalized-gradient directional field from Theorem 3:
`G(x) = E_v[∇u_v(x) / ||∇u_v(x)||₂]`.
-/
noncomputable def finiteTheorem3DirectionalField
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) : Coord → ℝ :=
  finiteVoterExpectation weight
    (fun voter =>
      modelBFiniteNormalizedDirection SourceNorm.l2
        (utilityGradient voter x))

/--
Coordinate expansion of the concrete Theorem 3 directional field in terms of
Model B's finite normalized direction.
-/
theorem finiteTheorem3DirectionalField_coord_eq_modelBNormalizedExpectation
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) (i : Coord) :
    finiteTheorem3DirectionalField weight utilityGradient x i =
      ∑ voter : Voter,
        weight voter *
          modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x) i := by
  simp [finiteTheorem3DirectionalField, finiteVoterExpectation]

/--
Expected signed raw Model B coordinate increment equals the signed coordinate
of `r * G(x)` for the concrete finite Theorem 3 directional field.
-/
theorem finiteTheorem3DirectionalField_expected_signed_modelB_coord_increment
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) (i : Coord) (a r : ℝ) :
    (∑ voter : Voter,
      weight voter *
        (a * (r *
          modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x) i))) =
      a * (r * finiteTheorem3DirectionalField weight utilityGradient x i) := by
  rw [finiteTheorem3DirectionalField_coord_eq_modelBNormalizedExpectation]
  calc
    (∑ voter : Voter,
      weight voter *
        (a * (r *
          modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x) i)))
        =
          ∑ voter : Voter,
            (a * r) *
              (weight voter *
                modelBFiniteNormalizedDirection SourceNorm.l2
                  (utilityGradient voter x) i) := by
          apply Finset.sum_congr rfl
          intro voter _hvoter
          ring
    _ =
        (a * r) *
          (∑ voter : Voter,
            weight voter *
              modelBFiniteNormalizedDirection SourceNorm.l2
                (utilityGradient voter x) i) := by
          rw [Finset.mul_sum]
    _ =
        a * (r *
          ∑ voter : Voter,
            weight voter *
              modelBFiniteNormalizedDirection SourceNorm.l2
                (utilityGradient voter x) i) := by
          ring

/--
Response-form version of
`finiteTheorem3DirectionalField_expected_signed_modelB_coord_increment`.
-/
theorem finiteTheorem3DirectionalField_expected_signed_modelB_response_increment
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    {x : Coord → ℝ} {response : Voter → Coord → ℝ}
    (i : Coord) (a r : ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 x r
          (utilityGradient voter x) (response voter)) :
    (∑ voter : Voter,
      weight voter * (a * (response voter i - x i))) =
      a * (r * finiteTheorem3DirectionalField weight utilityGradient x i) := by
  calc
    (∑ voter : Voter,
      weight voter * (a * (response voter i - x i)))
        =
          ∑ voter : Voter,
            weight voter *
              (a * (r *
                modelBFiniteNormalizedDirection SourceNorm.l2
                  (utilityGradient voter x) i)) := by
          apply Finset.sum_congr rfl
          intro voter _hvoter
          rw [modelBFiniteResponseAt_coord_increment i (hresponse voter)]
    _ =
        a * (r * finiteTheorem3DirectionalField weight utilityGradient x i) :=
          finiteTheorem3DirectionalField_expected_signed_modelB_coord_increment
            weight utilityGradient x i a r

/--
Finite-sum version of the expected raw Model B increment identity, matching the
accumulated expected term in the Appendix C.6 proof.
-/
theorem finiteTheorem3DirectionalField_expected_signed_modelB_response_increment_sum
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (i : Coord) (a : ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter)) :
    ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          weight voter * (a * (response t voter i - center t i))) =
        ∑ t ∈ Finset.range n,
          a * (radius t *
            finiteTheorem3DirectionalField weight utilityGradient
              (center t) i) := by
  intro n
  apply Finset.sum_congr rfl
  intro t _ht
  exact
    finiteTheorem3DirectionalField_expected_signed_modelB_response_increment
      (weight := weight) (utilityGradient := utilityGradient)
      (x := center t) (response := response t) i a (radius t)
      (hresponse t)

/--
The concrete finite-coordinate Theorem 3 operations make the source
directional-field formula definitional rather than an abstract premise.
-/
structure FiniteTheorem3DirectionalFieldModel
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  weight : Voter → ℝ
  weight_nonneg : ∀ voter, 0 ≤ weight voter
  weight_sum : (∑ voter : Voter, weight voter) = 1
  utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ
  utilityGradient_eq :
    E.utilityGradient = utilityGradient
  scalarDirection_eq :
    E.scalarDirection = finiteScalarDirection
  voterExpectation_eq :
    E.voterExpectation = finiteVoterExpectation weight
  directionalField_eq :
    E.directionalField =
      finiteTheorem3DirectionalField weight utilityGradient
  zeroDirection_eq :
    E.zeroDirection = fun _ => 0
  normDistance_l2_zero_eq :
    ∀ g : Coord → ℝ,
      E.normDistance SourceNorm.l2 g E.zeroDirection =
        finiteCoordinateNorm SourceNorm.l2 g

theorem theorem3DirectionalFieldFormula_of_finiteDirectionalFieldModel
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) :
    Theorem3DirectionalFieldFormula E := by
  classical
  intro x
  rw [M.directionalField_eq, M.voterExpectation_eq]
  funext i
  simp only [finiteTheorem3DirectionalField, finiteVoterExpectation]
  apply Finset.sum_congr rfl
  intro voter _
  rw [theorem3NormalizedGradientDirection]
  simp only [M.utilityGradient_eq, M.scalarDirection_eq, M.zeroDirection_eq]
  by_cases hzero : M.utilityGradient voter x = 0
  · have hzero' : M.utilityGradient voter x = (fun _ : Coord => 0) := by
      simpa using hzero
    rw [if_pos hzero']
    simp [modelBFiniteNormalizedDirection, hzero]
  · have hzero' : M.utilityGradient voter x ≠ (fun _ : Coord => 0) := by
      simpa using hzero
    have hnorm :
        E.normDistance SourceNorm.l2 (M.utilityGradient voter x)
          (fun _ : Coord => 0) =
          finiteCoordinateNorm SourceNorm.l2 (M.utilityGradient voter x) := by
      simpa [M.zeroDirection_eq] using
        M.normDistance_l2_zero_eq (M.utilityGradient voter x)
    rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hzero]
    rw [if_neg hzero', hnorm]
    simp [finiteScalarDirection, div_eq_mul_inv]
    apply Or.inl
    ring

/--
Theorem 3's population directional field.  The paper samples a voter from a
population distribution and writes its directional field as an expectation;
this definition is the finite-dimensional, measure-theoretic reading of that
display.  It is deliberately distinct from the older finite-support helper:
the voter type need not be finite.

The zero-gradient convention is inherited from
`modelBFiniteNormalizedDirection`: a voter with zero gradient contributes the
zero direction rather than invoking an undefined quotient.
-/
noncomputable def populationTheorem3DirectionalField
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (population : Measure Voter)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) : Coord → ℝ :=
  fun i => ∫ voter,
    modelBFiniteNormalizedDirection SourceNorm.l2
      (utilityGradient voter x) i ∂population

/--
Measure/population source semantics for Theorem 3.  This is the paper's
`E_v[∇f_v(x) / ‖∇f_v(x)‖₂]` model, not a finite-voter specialization.  The
integrability field makes the displayed expectation mathematically meaningful
rather than relying on Lean's totalized integral.
-/
structure PopulationTheorem3DirectionalFieldModel
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  population : Measure Voter
  population_probability : IsProbabilityMeasure population
  utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ
  utilityGradient_eq : E.utilityGradient = utilityGradient
  utilityGradient_source_subgradient :
    ∀ voter x,
      FiniteSourceSubgradientAt (E.utility voter) x (utilityGradient voter x)
  scalarDirection_eq : E.scalarDirection = finiteScalarDirection
  zeroDirection_eq : E.zeroDirection = fun _ => 0
  normDistance_l2_zero_eq :
    ∀ g : Coord → ℝ,
      E.normDistance SourceNorm.l2 g E.zeroDirection =
        finiteCoordinateNorm SourceNorm.l2 g
  normalized_gradient_integrable :
    ∀ x i,
      Integrable
        (fun voter =>
          modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x) i)
        population
  directionalField_eq :
    E.directionalField =
      populationTheorem3DirectionalField population utilityGradient
  voterExpectation_normalized_eq :
    ∀ x,
      E.voterExpectation (fun voter => theorem3NormalizedGradientDirection E voter x) =
        populationTheorem3DirectionalField population utilityGradient x

/--
The population model realizes the paper's displayed directional-field formula.
The proof only unfolds the source-defined zero-gradient branch; it does not
replace the population integral with a finite sum.
-/
theorem theorem3DirectionalFieldFormula_of_populationDirectionalFieldModel
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : PopulationTheorem3DirectionalFieldModel E) :
    Theorem3DirectionalFieldFormula E := by
  intro x
  rw [M.directionalField_eq, M.voterExpectation_normalized_eq]

/--
The finite-dimensional scalar projection of the population Theorem 3 field is
the corresponding population integral.  This is the measure-theoretic
replacement for the old finite-voter weighted-sum identity; it uses only the
coordinate integrability required by the population source model.
-/
theorem populationTheorem3DirectionalField_finiteDot_eq_integral
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (population : Measure Voter)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x a : Coord → ℝ)
    (hintegrable :
      ∀ i,
        Integrable
          (fun voter =>
            modelBFiniteNormalizedDirection SourceNorm.l2
              (utilityGradient voter x) i)
          population) :
    finiteDot a (populationTheorem3DirectionalField population utilityGradient x) =
      ∫ voter,
        finiteDot a
          (modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x)) ∂population := by
  simp only [finiteDot, populationTheorem3DirectionalField]
  rw [MeasureTheory.integral_finset_sum]
  · exact Finset.sum_congr rfl fun i _ => by
      simpa [mul_comm] using
        (MeasureTheory.integral_mul_const (a i)
          (fun voter =>
            modelBFiniteNormalizedDirection SourceNorm.l2
              (utilityGradient voter x) i)).symm
  · intro i _
    exact (hintegrable i).const_mul (a i)

/--
The literal Model B raw response used by the population Theorem 3 route.  Its
zero-gradient branch is inherited from `modelBFiniteNormalizedDirection`, so
this definition remains source-defined at a stationary individual utility.
-/
noncomputable def populationTheorem3ModelBRawResponse
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) (r : ℝ) (voter : Voter) : Coord → ℝ :=
  fun i => x i + r *
    modelBFiniteNormalizedDirection SourceNorm.l2
      (utilityGradient voter x) i

theorem populationTheorem3ModelBRawResponse_is_modelBFiniteResponseAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) (r : ℝ) (voter : Voter) :
    ModelBFiniteResponseAt SourceNorm.l2 x r (utilityGradient voter x)
      (populationTheorem3ModelBRawResponse utilityGradient x r voter) := by
  rw [modelBFiniteResponseAt_formula]
  rfl

/--
The scalar expected raw-response increment is the step radius times the scalar
projection of the measure/population directional field.  This is the exact
integral analogue of the finite-weight identity used in the former adapter.
-/
theorem populationTheorem3_expected_finiteDot_modelB_raw_increment
    {Voter Coord : Type*} [MeasurableSpace Voter] [Fintype Coord] [Nonempty Coord]
    (population : Measure Voter)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x a : Coord → ℝ) (r : ℝ)
    (hintegrable :
      ∀ i,
        Integrable
          (fun voter =>
            modelBFiniteNormalizedDirection SourceNorm.l2
              (utilityGradient voter x) i)
          population) :
    (∫ voter,
      finiteDot a
        (fun i =>
          populationTheorem3ModelBRawResponse utilityGradient x r voter i - x i)
        ∂population) =
      r * finiteDot a
        (populationTheorem3DirectionalField population utilityGradient x) := by
  have hresponse :
      (fun voter =>
        finiteDot a
          (fun i =>
            populationTheorem3ModelBRawResponse utilityGradient x r voter i - x i)) =
        fun voter =>
          r * finiteDot a
            (modelBFiniteNormalizedDirection SourceNorm.l2
              (utilityGradient voter x)) := by
    funext voter
    simp only [populationTheorem3ModelBRawResponse]
    unfold finiteDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hresponse, MeasureTheory.integral_const_mul]
  congr 1
  exact (populationTheorem3DirectionalField_finiteDot_eq_integral
    population utilityGradient x a hintegrable).symm

/--
If two real coordinates have the same strict sign and the second has magnitude
at least `ε`, then a nonnegative step in the second coordinate makes at least
`|a| * ε * r` signed progress in the `a` direction.
-/
theorem signed_step_lower_bound_of_same_sign_abs
    {a b r ε : ℝ}
    (hr : 0 ≤ r)
    (hεle : ε ≤ |b|)
    (hsign : 0 < a * b) :
    |a| * ε * r ≤ a * (r * b) := by
  have habs_eq : |a| * |b| = a * b := by
    have hprod_abs : |a * b| = a * b := abs_of_pos hsign
    simpa [abs_mul] using hprod_abs
  have hscaled :
      |a| * ε ≤ |a| * |b| :=
    mul_le_mul_of_nonneg_left hεle (abs_nonneg a)
  have hscaled_r :
      |a| * ε * r ≤ |a| * |b| * r :=
    mul_le_mul_of_nonneg_right hscaled hr
  calc
    |a| * ε * r ≤ |a| * |b| * r := hscaled_r
    _ = a * (r * b) := by
      rw [habs_eq]
      ring

/--
Paper-radius specialization of
`signed_step_lower_bound_of_same_sign_abs`.
-/
theorem signed_ilvRadius_step_lower_bound_of_coordinate_drift
    {r0 a b ε : ℝ} (hr0 : 0 < r0) (t : ℕ)
    (hεle : ε ≤ |b|)
    (hsign : 0 < a * b) :
    |a| * ε * ilvRadius r0 (t + 1) ≤
      a * (ilvRadius r0 (t + 1) * b) := by
  exact signed_step_lower_bound_of_same_sign_abs
    (ilvRadius_nonneg (le_of_lt hr0) (t + 1)) hεle hsign

/--
Sequence form of the C.6 signed-coordinate lower bound.  Once a coordinate's
directional field keeps the same sign and magnitude along the tail trajectory,
each expected paper-radius coordinate increment has a uniform signed lower
bound.
-/
theorem signed_ilvRadius_step_lower_bound_of_coordinate_drift_sequence
    {r0 a ε : ℝ} {b : ℕ → ℝ} (hr0 : 0 < r0)
    (hdrift : ∀ n : ℕ, ε < |b n| ∧ 0 < a * b n) :
    ∀ n : ℕ,
      |a| * ε * ilvRadius r0 (n + 1) ≤
        a * (ilvRadius r0 (n + 1) * b n) := by
  intro n
  exact signed_ilvRadius_step_lower_bound_of_coordinate_drift
    hr0 n (le_of_lt (hdrift n).1) (hdrift n).2

/--
Accumulated expected-coordinate version of the C.6 signed drift lower bound.
The only inputs are the paper-radius schedule and the fixed-sign, fixed-magnitude
coordinate drift along the tail trajectory.
-/
theorem signed_expected_coordinate_sum_lower_bound_of_drift_sequence
    {r0 a ε : ℝ} {b : ℕ → ℝ} (hr0 : 0 < r0)
    (hdrift : ∀ n : ℕ, ε < |b n| ∧ 0 < a * b n) :
    ∀ n : ℕ,
      |a| * ε *
          (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1)) ≤
        ∑ t ∈ Finset.range n,
          a * (ilvRadius r0 (t + 1) * b t) := by
  intro n
  calc
    |a| * ε * (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
        = (|a| * ε) *
            (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1)) := by
          ring
    _ = ∑ t ∈ Finset.range n,
          (|a| * ε) * ilvRadius r0 (t + 1) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ t ∈ Finset.range n,
          a * (ilvRadius r0 (t + 1) * b t) := by
          exact Finset.sum_le_sum fun t _ht => by
            have hstep :=
              signed_ilvRadius_step_lower_bound_of_coordinate_drift_sequence
                (r0 := r0) (a := a) (ε := ε) (b := b) hr0 hdrift t
            simpa [mul_assoc] using hstep

/-- Monotonicity of nonnegative paper-radius partial sums under a finite shift. -/
theorem ilvRadius_sum_range_mono_add {r0 : ℝ} (hr0 : 0 < r0)
    (n T : ℕ) :
    (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1)) ≤
      ∑ t ∈ Finset.range (n + T), ilvRadius r0 (t + 1) := by
  have hsubset : Finset.range n ⊆ Finset.range (n + T) := by
    intro t ht
    exact Finset.mem_range.mpr
      (lt_of_lt_of_le (Finset.mem_range.mp ht) (Nat.le_add_right n T))
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (by
        intro t _htn _htbig
        exact ilvRadius_nonneg (le_of_lt hr0) (t + 1))

/--
Finite-dot/scalar analogue of
`signed_expected_coordinate_sum_lower_bound_of_drift_sequence`: if every
expected scalar drift term is at least `c`, then the accumulated expected drift
dominates `c` times the paper-radius partial sum.
-/
theorem finiteDot_expected_sum_lower_bound_of_drift_sequence
    {r0 c : ℝ} {b : ℕ → ℝ} (hr0 : 0 < r0)
    (hdrift : ∀ n : ℕ, c ≤ b n) :
    ∀ n : ℕ,
      c * (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1)) ≤
        ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1) * b t := by
  intro n
  calc
    c * (∑ t ∈ Finset.range n, ilvRadius r0 (t + 1))
        = ∑ t ∈ Finset.range n, c * ilvRadius r0 (t + 1) := by
          rw [Finset.mul_sum]
    _ = ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1) * c := by
          apply Finset.sum_congr rfl
          intro t _ht
          ring
    _ ≤ ∑ t ∈ Finset.range n, ilvRadius r0 (t + 1) * b t := by
          exact Finset.sum_le_sum fun t _ht =>
            mul_le_mul_of_nonneg_left (hdrift t)
              (ilvRadius_nonneg (le_of_lt hr0) (t + 1))

/--
Scalar form of the deterministic drift contradiction behind Theorem 3.  If a
projection of the trajectory converges to a finite value but is bounded below by
a positive multiple of tail radius partial sums that diverge to infinity, then
the hypotheses are inconsistent.
-/
theorem scalar_convergence_contradiction_of_accumulated_drift
    {s : ℕ → ℝ} {limit base c : ℝ} {radiusTail : ℕ → ℝ}
    (hc : 0 < c)
    (hradius :
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radiusTail t)
        Filter.atTop Filter.atTop)
    (hlower :
      ∀ n : ℕ,
        base + c * (∑ t ∈ Finset.range n, radiusTail t) ≤ s n)
    (hconv : Filter.Tendsto s Filter.atTop (nhds limit)) :
    False := by
  have hscaled :
      Filter.Tendsto
        (fun n : ℕ => c * (∑ t ∈ Finset.range n, radiusTail t))
        Filter.atTop Filter.atTop :=
    hradius.const_mul_atTop hc
  have hshifted :
      Filter.Tendsto
        (fun n : ℕ => base + c * (∑ t ∈ Finset.range n, radiusTail t))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.tendsto_atTop.1 hscaled (b - base)] with n hn
    linarith
  have hs_atTop : Filter.Tendsto s Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hlower hshifted
  exact not_tendsto_atTop_of_tendsto_nhds hconv hs_atTop

/--
Telescoping form of the deterministic drift step in Theorem 3.  If each
one-step scalar projection increases by at least `c * r_t`, then after `n`
steps it is bounded below by the initial projection plus the accumulated
radius-weighted drift.
-/
theorem scalar_accumulated_drift_lower_bound_of_one_step
    {s radiusTail : ℕ → ℝ} {c : ℝ}
    (hstep : ∀ t : ℕ, c * radiusTail t ≤ s (t + 1) - s t) :
    ∀ n : ℕ,
      s 0 + c * (∑ t ∈ Finset.range n, radiusTail t) ≤ s n := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hstepn := hstep n
      rw [Finset.sum_range_succ]
      calc
        s 0 + c * ((∑ t ∈ Finset.range n, radiusTail t) + radiusTail n)
            = (s 0 + c * (∑ t ∈ Finset.range n, radiusTail t)) +
                c * radiusTail n := by
              ring
        _ ≤ s n + c * radiusTail n := by
              linarith
        _ ≤ s n + (s (n + 1) - s n) := by
              linarith
        _ = s (n + 1) := by
              ring

/-- Exact telescoping identity for a scalar tail of a sequence. -/
theorem scalar_tail_displacement_eq_sum_increments
    (s : ℕ → ℝ) (N n : ℕ) :
    s (n + N) - s N =
      ∑ t ∈ Finset.range n, (s (t + 1 + N) - s (t + N)) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih]
      ring

/--
Coordinate form of `scalar_tail_displacement_eq_sum_increments`, matching the
Appendix C.6 line that expands `x_τ - x_t` as a sum of one-step movements.
-/
theorem finiteCoordinate_tail_coord_displacement_eq_sum_increments
    {Coord : Type*} (trajectory : ℕ → Coord → ℝ) (i : Coord)
    (N n : ℕ) :
    trajectory (n + N) i - trajectory N i =
      ∑ t ∈ Finset.range n,
        (trajectory (t + 1 + N) i - trajectory (t + N) i) := by
  exact scalar_tail_displacement_eq_sum_increments
    (fun t => trajectory t i) N n

/--
Signed coordinate telescoping around a putative limit `xstar`.  This isolates
the deterministic identity under the C.6 random-increment/concentration layer.
-/
theorem signed_finiteCoordinate_tail_displacement_eq_base_add_sum_increments
    {Coord : Type*} (trajectory : ℕ → Coord → ℝ)
    (a : ℝ) (xstar : Coord → ℝ) (i : Coord) (N n : ℕ) :
    a * (trajectory (n + N) i - xstar i) =
      a * (trajectory N i - xstar i) +
        ∑ t ∈ Finset.range n,
          a * (trajectory (t + 1 + N) i - trajectory (t + N) i) := by
  have htel :=
    finiteCoordinate_tail_coord_displacement_eq_sum_increments
      trajectory i N n
  calc
    a * (trajectory (n + N) i - xstar i)
        = a * (trajectory N i - xstar i) +
            a * (trajectory (n + N) i - trajectory N i) := by
          ring
    _ = a * (trajectory N i - xstar i) +
          a * (∑ t ∈ Finset.range n,
            (trajectory (t + 1 + N) i - trajectory (t + N) i)) := by
          rw [htel]
    _ = a * (trajectory N i - xstar i) +
          ∑ t ∈ Finset.range n,
            a * (trajectory (t + 1 + N) i - trajectory (t + N) i) := by
          rw [Finset.mul_sum]

/--
Analytic drift semantics sufficient to prove Theorem 3's deterministic step
without the older black-box `modelB_l2_nonzero_drift_contradiction` field.

The key source-facing obligation is `nonzero_drift_accumulates`: from a nonzero
field at a putative limit, Model B plus uniform continuity supplies a scalar
projection and a positive margin whose accumulated radius-weighted progress
would force that scalar projection to diverge.
-/
structure Theorem3AnalyticDriftSemantics
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) where
  radiusTail : Point → ℕ → ℝ
  projection : Point → Point → ℝ
  radiusTail_partial_sums_tendsto_atTop :
    ∀ xstar : Point,
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radiusTail xstar t)
        Filter.atTop Filter.atTop
  projection_converges :
    ∀ {xstar : Point},
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
        Filter.Tendsto
          (fun n : ℕ =>
            projection xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
          Filter.atTop (nhds (projection xstar xstar))
  nonzero_drift_accumulates :
    ∀ {xstar : Point},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c baseValue, 0 < c ∧
                  ∀ n : ℕ,
                    baseValue +
                        c * (∑ t ∈ Finset.range n, radiusTail xstar t) ≤
                      projection xstar
                        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n)

/-- Finite-dimensional Cauchy-Schwarz for the paper-local finite dot product. -/
theorem finiteDot_abs_le_l2_mul_l2
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x y : Coord → ℝ) :
    |finiteDot x y| ≤
      finiteCoordinateNorm SourceNorm.l2 x *
        finiteCoordinateNorm SourceNorm.l2 y := by
  have hsq :
      finiteDot x y ^ 2 ≤
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq x *
          AppliedModelingLib.FiniteDimensionalNorms.l2Sq y := by
    simpa [finiteDot, AppliedModelingLib.FiniteDimensionalNorms.l2Sq] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (s := (Finset.univ : Finset Coord)) (f := x) (g := y))
  calc
    |finiteDot x y|
        ≤ Real.sqrt
            (AppliedModelingLib.FiniteDimensionalNorms.l2Sq x *
              AppliedModelingLib.FiniteDimensionalNorms.l2Sq y) := by
          exact Real.abs_le_sqrt hsq
    _ =
        finiteCoordinateNorm SourceNorm.l2 x *
          finiteCoordinateNorm SourceNorm.l2 y := by
          rw [finiteCoordinateNorm_l2, finiteCoordinateNorm_l2,
            AppliedModelingLib.FiniteDimensionalNorms.l2,
            AppliedModelingLib.FiniteDimensionalNorms.l2,
            Real.sqrt_mul
              (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x)]

/--
Increment form of finite-dimensional Cauchy-Schwarz.  This is the deterministic
boundedness bridge used before applying Hoeffding/Azuma to finite-dot selected
raw increments.
-/
theorem finiteDot_increment_abs_le_l2_mul_distance
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a x y : Coord → ℝ) :
    |finiteDot a (fun i => y i - x i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a *
        finiteCoordinateDistance SourceNorm.l2 y x := by
  simpa [finiteCoordinateDistance] using
    finiteDot_abs_le_l2_mul_l2 a (fun i => y i - x i)

/--
Bound finite-dot increments by any certified `L2` step bound.  This is the
deterministic bounded-increment shape used before the selected-voter
Hoeffding/Azuma argument.
-/
theorem finiteDot_increment_abs_le_l2_mul_stepBound
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a x y : Coord → ℝ) {R : ℝ}
    (hstep : finiteCoordinateDistance SourceNorm.l2 y x ≤ R) :
    |finiteDot a (fun i => y i - x i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a * R := by
  exact
    (finiteDot_increment_abs_le_l2_mul_distance a x y).trans
      (mul_le_mul_of_nonneg_left hstep
        (by
          simpa [finiteCoordinateDistance] using
            finiteCoordinateDistance_l2_nonneg a (fun _ => 0)))

theorem finiteDot_modelB_response_increment_abs_le_l2_mul_radius
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a center gradient response : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (hresponse :
      ModelBFiniteResponseAt SourceNorm.l2 center r gradient response) :
    |finiteDot a (fun i => response i - center i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a * r := by
  exact finiteDot_increment_abs_le_l2_mul_stepBound a center response
    (modelBFiniteResponseAt_l2_within_radius hr hresponse)

theorem finiteDot_response_increment_abs_le_l2_mul_radius_of_stepBound
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a center response : Coord → ℝ) {r : ℝ}
    (hstep : finiteCoordinateDistance SourceNorm.l2 response center ≤ r) :
    |finiteDot a (fun i => response i - center i)| ≤
      finiteCoordinateNorm SourceNorm.l2 a * r := by
  exact finiteDot_increment_abs_le_l2_mul_stepBound a center response hstep

theorem finiteDot_centered_response_increment_mem_Icc_of_stepBound
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (response : Voter → Coord → ℝ)
    (hstep :
      ∀ voter : Voter,
        finiteCoordinateDistance SourceNorm.l2 (response voter) center ≤ r)
    (selected : Voter) :
    finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * r)) := by
  let value : Voter → ℝ :=
    fun voter => finiteDot a (fun i => response voter i - center i)
  have hB :
      0 ≤ finiteCoordinateNorm SourceNorm.l2 a * r := by
    exact mul_nonneg (finiteCoordinateNorm_l2_nonneg a) hr
  have hvalue :
      ∀ voter : Voter,
        |value voter| ≤ finiteCoordinateNorm SourceNorm.l2 a * r := by
    intro voter
    exact
      finiteDot_response_increment_abs_le_l2_mul_radius_of_stepBound
        a center (response voter) (hstep voter)
  simpa [value] using
    (AppliedModelingLib.FiniteSum.weighted_centered_value_mem_Icc_of_abs_le_bound
      weight value hweight_nonneg hweight_sum hvalue hB selected)

theorem finiteDot_centered_response_increment_abs_le_of_stepBound
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (response : Voter → Coord → ℝ)
    (hstep :
      ∀ voter : Voter,
        finiteCoordinateDistance SourceNorm.l2 (response voter) center ≤ r)
    (selected : Voter) :
    |finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * r) := by
  exact abs_le.mpr
    (finiteDot_centered_response_increment_mem_Icc_of_stepBound
      weight hweight_nonneg hweight_sum a center hr response hstep selected)

theorem finiteDot_centered_response_increment_mem_Icc_sequence_of_stepBound
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hstep :
      ∀ t voter,
        finiteCoordinateDistance SourceNorm.l2 (response t voter) (center t) ≤
          radius t)
    (t : ℕ) :
    finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) := by
  exact finiteDot_centered_response_increment_mem_Icc_of_stepBound
    weight hweight_nonneg hweight_sum a (center t) (hradius_nonneg t)
    (response t) (hstep t) (sampledVoter t)

theorem finiteDot_centered_response_increment_abs_le_sequence_of_stepBound
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hstep :
      ∀ t voter,
        finiteCoordinateDistance SourceNorm.l2 (response t voter) (center t) ≤
          radius t)
    (t : ℕ) :
    |finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t) := by
  exact abs_le.mpr
    (finiteDot_centered_response_increment_mem_Icc_sequence_of_stepBound
      weight hweight_nonneg hweight_sum a center radius hradius_nonneg
      response sampledVoter hstep t)

theorem finiteDot_modelB_centered_response_increment_mem_Icc
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter))
    (selected : Voter) :
    finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * r)) := by
  let value : Voter → ℝ :=
    fun voter => finiteDot a (fun i => response voter i - center i)
  have hB :
      0 ≤ finiteCoordinateNorm SourceNorm.l2 a * r := by
    have ha_nonneg : 0 ≤ finiteCoordinateNorm SourceNorm.l2 a := by
      simpa [finiteCoordinateDistance] using
        (finiteCoordinateDistance_l2_nonneg a (fun _ : Coord => 0))
    exact mul_nonneg ha_nonneg hr
  have hvalue :
      ∀ voter : Voter,
        |value voter| ≤ finiteCoordinateNorm SourceNorm.l2 a * r := by
    intro voter
    exact finiteDot_modelB_response_increment_abs_le_l2_mul_radius
      a center (utilityGradient voter) (response voter) hr (hresponse voter)
  simpa [value] using
    (AppliedModelingLib.FiniteSum.weighted_centered_value_mem_Icc_of_abs_le_bound
      weight value hweight_nonneg hweight_sum hvalue hB selected)

theorem abs_le_of_mem_Icc_neg {x c : ℝ}
    (h : x ∈ Set.Icc (-c) c) :
    |x| ≤ c := by
  exact abs_le.mpr h

theorem finiteDot_modelB_centered_response_increment_abs_le
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter))
    (selected : Voter) :
    |finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * r) := by
  exact abs_le_of_mem_Icc_neg
    (finiteDot_modelB_centered_response_increment_mem_Icc
      weight hweight_nonneg hweight_sum a center hr utilityGradient response
      hresponse selected)

theorem finiteDot_modelB_centered_response_increment_mem_Icc_sequence
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i)) ∈
      Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) := by
  exact finiteDot_modelB_centered_response_increment_mem_Icc
    weight hweight_nonneg hweight_sum a (center t) (hradius_nonneg t)
    (fun voter => utilityGradient voter (center t)) (response t)
    (hresponse t) (sampledVoter t)

theorem finiteDot_modelB_centered_response_increment_abs_le_sequence
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    |finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t) := by
  exact abs_le_of_mem_Icc_neg
    (finiteDot_modelB_centered_response_increment_mem_Icc_sequence
      weight hweight_nonneg hweight_sum a center radius hradius_nonneg
      utilityGradient response sampledVoter hresponse t)

theorem finiteDot_modelB_centered_response_increment_mem_Icc_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i)) ∈
      Set.Icc
        (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))))
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))) := by
  exact finiteDot_modelB_centered_response_increment_mem_Icc_sequence
    weight hweight_nonneg hweight_sum a center
    (fun t => ilvRadius r0 (t + 1))
    (fun t => ilvRadius_nonneg (le_of_lt hr0) (t + 1))
    utilityGradient response sampledVoter hresponse t

theorem finiteDot_modelB_centered_response_increment_abs_le_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) ≤ 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (sampledVoter : ℕ → Voter)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    |finiteDot a (fun i => response t (sampledVoter t) i - center t i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response t voter i - center t i))| ≤
      2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1)) := by
  exact abs_le_of_mem_Icc_neg
    (finiteDot_modelB_centered_response_increment_mem_Icc_ilvRadius
      weight hweight_nonneg hweight_sum a center hr0 utilityGradient response
      sampledVoter hresponse t)

theorem finiteDot_modelB_centered_response_increment_ilvRadius_bound_nonneg
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) {r0 : ℝ} (hr0 : 0 < r0) (t : ℕ) :
    0 ≤ 2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1)) := by
  exact mul_nonneg (by norm_num)
    (mul_nonneg (finiteCoordinateNorm_l2_nonneg a)
      (ilvRadius_nonneg (le_of_lt hr0) (t + 1)))

theorem finiteDot_modelB_centered_response_increment_ilvRadius_bound_sq_summable
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) (r0 : ℝ) :
    Summable
      (fun t : ℕ =>
        (2 * (finiteCoordinateNorm SourceNorm.l2 a * ilvRadius r0 (t + 1))) ^ 2) := by
  have hsummable :
      Summable
        (fun t : ℕ =>
          (2 * finiteCoordinateNorm SourceNorm.l2 a) ^ 2 *
            (ilvRadius r0 (t + 1)) ^ 2) :=
    (ilvRadius_sq_summable r0).mul_left
      ((2 * finiteCoordinateNorm SourceNorm.l2 a) ^ 2)
  refine hsummable.congr ?_
  intro t
  ring

/-- Infinite product law for the paper's independent weighted voter draws. -/
noncomputable def theorem3FiniteWeightedVoterSequenceMeasure
    {Voter : Type*} [Fintype Voter] [MeasurableSpace Voter]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1) :
    Measure (ℕ → Voter) :=
  Measure.infinitePi
    (fun _ : ℕ =>
      (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure)

/--
Finite weighted voter sampling centers the scalar response increment exactly.
This is the finite-distribution mean-zero ingredient paired with the interval
bound above before applying Hoeffding/Azuma.
-/
theorem finiteDot_modelB_centered_response_increment_pmfExp_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ) :
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one))
        (fun selected : Voter =>
          finiteDot a (fun i => response selected i - center i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response voter i - center i))) =
      0 := by
  let μ : PMF Voter :=
    AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
      (by simpa [hweight_sum] using zero_lt_one)
  let value : Voter → ℝ :=
    fun voter => finiteDot a (fun i => response voter i - center i)
  have hmean :
      AppliedModelingLib.pmfExp μ value =
        ∑ voter : Voter, weight voter * value voter := by
    simpa [μ, value] using
      (AppliedModelingLib.finiteWeightedPMF_pmfExp_eq_weighted_sum_of_sum_eq_one
        (weight := weight) (hweight_nonneg := hweight_nonneg)
        (hsum := hweight_sum) (f := value))
  have hcentered :
      AppliedModelingLib.pmfExp μ
          (fun selected : Voter =>
            value selected -
              (∑ voter : Voter, weight voter * value voter)) = 0 := by
    calc
      AppliedModelingLib.pmfExp μ
          (fun selected : Voter =>
            value selected -
              (∑ voter : Voter, weight voter * value voter))
          =
            AppliedModelingLib.pmfExp μ value -
              AppliedModelingLib.pmfExp μ
                (fun _selected : Voter =>
                  ∑ voter : Voter, weight voter * value voter) := by
              rw [AppliedModelingLib.pmfExp_sub]
      _ =
          (∑ voter : Voter, weight voter * value voter) -
            (∑ voter : Voter, weight voter * value voter) := by
            rw [hmean]
            simp [AppliedModelingLib.pmfExp_const]
      _ = 0 := by ring
  simpa [μ, value] using hcentered

theorem finiteDot_modelB_centered_response_increment_pmfExp_eq_zero_sequence
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (t : ℕ) :
    AppliedModelingLib.pmfExp
        (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one))
        (fun selected : Voter =>
          finiteDot a (fun i => response t selected i - center t i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response t voter i - center t i))) =
      0 := by
  exact finiteDot_modelB_centered_response_increment_pmfExp_eq_zero
    weight hweight_nonneg hweight_sum a (center t) (response t)

/--
Integral form of the finite weighted centered-increment identity.  This is the
same finite voter-sampling fact as
`finiteDot_modelB_centered_response_increment_pmfExp_eq_zero`, expressed using
`PMF.toMeasure` for compatibility with measure/kernel concentration APIs.
-/
theorem finiteDot_modelB_centered_response_increment_integral_toMeasure_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ)
    (response : Voter → Coord → ℝ) :
    ∫ selected : Voter,
        (finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)))
      ∂(AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one)).toMeasure =
      0 := by
  let μ : PMF Voter :=
    AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
      (by simpa [hweight_sum] using zero_lt_one)
  let X : Voter → ℝ :=
    fun selected =>
      finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i))
  have hpmf : AppliedModelingLib.pmfExp μ X = 0 := by
    simpa [μ, X] using
      finiteDot_modelB_centered_response_increment_pmfExp_eq_zero
        weight hweight_nonneg hweight_sum a center response
  have hintegral : (∫ selected : Voter, X selected ∂μ.toMeasure) =
      AppliedModelingLib.pmfExp μ X := by
    simpa [AppliedModelingLib.pmfExp] using (PMF.integral_eq_sum μ X)
  calc
    ∫ selected : Voter,
        (finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)))
      ∂(AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
          (by simpa [hweight_sum] using zero_lt_one)).toMeasure
        = ∫ selected : Voter, X selected ∂μ.toMeasure := by
            rfl
    _ = AppliedModelingLib.pmfExp μ X := hintegral
    _ = 0 := hpmf

/--
One-step finite selected-voter input for the bounded-centered Hoeffding bridge:
under Model B responses, the centered scalar finite-dot increment is uniformly
bounded, and under the finite weighted voter law it has mean zero.
-/
theorem finiteDot_modelB_centered_response_increment_mem_Icc_and_integral_toMeasure_eq_zero
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter)) :
    (∀ selected : Voter,
      finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)) ∈
        Set.Icc (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))
          (2 * (finiteCoordinateNorm SourceNorm.l2 a * r))) ∧
      ∫ selected : Voter,
          (finiteDot a (fun i => response selected i - center i) -
            (∑ voter : Voter,
              weight voter *
                finiteDot a (fun i => response voter i - center i)))
        ∂(AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
            (by simpa [hweight_sum] using zero_lt_one)).toMeasure =
        0 := by
  constructor
  · intro selected
    exact finiteDot_modelB_centered_response_increment_mem_Icc
      weight hweight_nonneg (by exact le_of_eq hweight_sum) a center hr
      utilityGradient response hresponse selected
  · exact
      finiteDot_modelB_centered_response_increment_integral_toMeasure_eq_zero
        weight hweight_nonneg hweight_sum a center response

/--
Sub-Gaussian one-step consequence of the deterministic finite selected-voter
bound and centering.  This is the finite-law Hoeffding input for a single raw
Model B finite-dot increment.
-/
theorem finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a center : Coord → ℝ) {r : ℝ}
    (hr : 0 ≤ r)
    (utilityGradient : Voter → Coord → ℝ)
    (response : Voter → Coord → ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 center r
          (utilityGradient voter) (response voter)) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response selected i - center i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response voter i - center i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * r)))‖₊ / 2) ^ 2)
      (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  let μ : PMF Voter :=
    AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
      (by simpa [hweight_sum] using zero_lt_one)
  let X : Voter → ℝ :=
    fun selected =>
      finiteDot a (fun i => response selected i - center i) -
        (∑ voter : Voter,
          weight voter * finiteDot a (fun i => response voter i - center i))
  let lower : ℝ := -(2 * (finiteCoordinateNorm SourceNorm.l2 a * r))
  let upper : ℝ := 2 * (finiteCoordinateNorm SourceNorm.l2 a * r)
  have hbundle :
      (∀ selected : Voter, X selected ∈ Set.Icc lower upper) ∧
        ∫ selected : Voter, X selected ∂μ.toMeasure = 0 := by
    simpa [μ, X, lower, upper] using
      finiteDot_modelB_centered_response_increment_mem_Icc_and_integral_toMeasure_eq_zero
        weight hweight_nonneg hweight_sum a center hr utilityGradient response
        hresponse
  have hmeas : AEMeasurable X μ.toMeasure :=
    (measurable_of_finite X).aemeasurable
  have hbound : ∀ᵐ selected ∂μ.toMeasure, X selected ∈ Set.Icc lower upper :=
    Filter.Eventually.of_forall hbundle.1
  have hmean : ∫ selected : Voter, X selected ∂μ.toMeasure = 0 :=
    hbundle.2
  simpa [μ, X, lower, upper] using
    (ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := μ.toMeasure) (X := X) (a := lower) (b := upper)
      hmeas hbound hmean)

/--
Sequence form of
`finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure`.
This packages the one-step finite weighted voter law for a time-indexed Model B
response trace.
-/
theorem finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_sequence
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (hradius_nonneg : ∀ t : ℕ, 0 ≤ radius t)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response t selected i - center t i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response t voter i - center t i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a * radius t)))‖₊ / 2) ^ 2)
      (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  exact
    finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure
      weight hweight_nonneg hweight_sum a (center t) (hradius_nonneg t)
      (fun voter => utilityGradient voter (center t)) (response t)
      (hresponse t)

/--
ILV-radius specialization of the time-indexed finite selected-voter
sub-Gaussian input.
-/
theorem finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_ilvRadius
    {Voter Coord : Type*} [Fintype Voter] [DecidableEq Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    (a : Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    {r0 : ℝ} (hr0 : 0 < r0)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t)
          (ilvRadius r0 (t + 1))
          (utilityGradient voter (center t)) (response t voter))
    (t : ℕ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun selected : Voter =>
        finiteDot a (fun i => response t selected i - center t i) -
          (∑ voter : Voter,
            weight voter *
              finiteDot a (fun i => response t voter i - center t i)))
      ((‖(2 * (finiteCoordinateNorm SourceNorm.l2 a *
            ilvRadius r0 (t + 1))) -
          (-(2 * (finiteCoordinateNorm SourceNorm.l2 a *
            ilvRadius r0 (t + 1))))‖₊ / 2) ^ 2)
      (AppliedModelingLib.finiteWeightedPMF weight hweight_nonneg
        (by simpa [hweight_sum] using zero_lt_one)).toMeasure := by
  exact
    finiteDot_modelB_centered_response_increment_hasSubgaussianMGF_toMeasure_sequence
      weight hweight_nonneg hweight_sum a center
      (fun t => ilvRadius r0 (t + 1))
      (fun t => ilvRadius_nonneg (le_of_lt hr0) (t + 1))
      utilityGradient response hresponse t

/--
Finite-dot version of the expected raw Model B increment identity.  This is the
scalar-projection analogue of
`finiteTheorem3DirectionalField_expected_signed_modelB_response_increment` and
matches the projection-progress route for Theorem 3.
-/
theorem finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    {x : Coord → ℝ} {response : Voter → Coord → ℝ}
    (a : Coord → ℝ) (r : ℝ)
    (hresponse :
      ∀ voter : Voter,
        ModelBFiniteResponseAt SourceNorm.l2 x r
          (utilityGradient voter x) (response voter)) :
    (∑ voter : Voter,
      weight voter * finiteDot a (fun i => response voter i - x i)) =
      r * finiteDot a
        (finiteTheorem3DirectionalField weight utilityGradient x) := by
  unfold finiteDot
  calc
    (∑ voter : Voter,
      weight voter *
        ∑ i : Coord, a i * (response voter i - x i))
        =
          ∑ voter : Voter,
            ∑ i : Coord,
              weight voter * (a i * (response voter i - x i)) := by
          apply Finset.sum_congr rfl
          intro voter _hvoter
          rw [Finset.mul_sum]
    _ =
        ∑ i : Coord,
          ∑ voter : Voter,
            weight voter * (a i * (response voter i - x i)) := by
          rw [Finset.sum_comm]
    _ =
        ∑ i : Coord,
          a i *
            (r * finiteTheorem3DirectionalField weight utilityGradient x i) := by
          apply Finset.sum_congr rfl
          intro i _hi
          exact
            finiteTheorem3DirectionalField_expected_signed_modelB_response_increment
              (weight := weight) (utilityGradient := utilityGradient)
              (x := x) (response := response) i (a i) r hresponse
    _ =
        r *
          ∑ i : Coord,
            a i * finiteTheorem3DirectionalField weight utilityGradient x i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          ring

theorem finiteTheorem3DirectionalField_expected_finiteDot_modelBNormalizedDirection
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (x : Coord → ℝ) (a : Coord → ℝ) :
    (∑ voter : Voter,
      weight voter *
        finiteDot a
          (modelBFiniteNormalizedDirection SourceNorm.l2
            (utilityGradient voter x))) =
      finiteDot a
        (finiteTheorem3DirectionalField weight utilityGradient x) := by
  unfold finiteDot
  calc
    (∑ voter : Voter,
      weight voter *
        ∑ i : Coord,
          a i *
            modelBFiniteNormalizedDirection SourceNorm.l2
              (utilityGradient voter x) i)
        =
          ∑ voter : Voter,
            ∑ i : Coord,
              weight voter *
                (a i *
                  modelBFiniteNormalizedDirection SourceNorm.l2
                    (utilityGradient voter x) i) := by
          apply Finset.sum_congr rfl
          intro voter _hvoter
          rw [Finset.mul_sum]
    _ =
        ∑ i : Coord,
          ∑ voter : Voter,
            weight voter *
              (a i *
                modelBFiniteNormalizedDirection SourceNorm.l2
                  (utilityGradient voter x) i) := by
          rw [Finset.sum_comm]
    _ =
        ∑ i : Coord,
          a i *
            ∑ voter : Voter,
              weight voter *
                modelBFiniteNormalizedDirection SourceNorm.l2
                  (utilityGradient voter x) i := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro voter _hvoter
          ring
    _ =
        ∑ i : Coord,
          a i * finiteTheorem3DirectionalField weight utilityGradient x i := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [finiteTheorem3DirectionalField_coord_eq_modelBNormalizedExpectation]

/--
Finite-sum version of the finite-dot expected raw Model B increment identity.
This is the scalar accumulated expectation term needed by finite-dot
Hoeffding/projection-progress variants of Theorem 3.
-/
theorem finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    (weight : Voter → ℝ)
    (utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (center : ℕ → Coord → ℝ)
    (radius : ℕ → ℝ)
    (response : ℕ → Voter → Coord → ℝ)
    (a : Coord → ℝ)
    (hresponse :
      ∀ t voter,
        ModelBFiniteResponseAt SourceNorm.l2 (center t) (radius t)
          (utilityGradient voter (center t)) (response t voter)) :
    ∀ n : ℕ,
      (∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response t voter i - center t i)) =
        ∑ t ∈ Finset.range n,
          radius t *
            finiteDot a
              (finiteTheorem3DirectionalField weight utilityGradient
                (center t)) := by
  intro n
  apply Finset.sum_congr rfl
  intro t _ht
  exact
    finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment
      (weight := weight) (utilityGradient := utilityGradient)
      (x := center t) (response := response t) a (radius t)
      (hresponse t)

/--
Finite-coordinate normal-cone condition for an `L2` projection.  The intended
future source is the Euclidean nearest-point theorem for a closed convex
solution space; this local predicate exposes only the deterministic inequality
needed by the Theorem 3 drift argument.
-/
def FiniteProjectionNormalConeAt
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (raw next : Coord → ℝ) : Prop :=
  ∀ z, z ∈ X →
    finiteDot (fun i => raw i - next i) (fun i => z i - next i) ≤ 0

/--
The analytically sufficient feasibility condition for using a fixed direction
in the projection residual argument: a positive step of some size from the
projected point stays in the feasible set.
-/
def FiniteFeasibleDirectionAt
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (point direction : Coord → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ (fun i => point i + η * direction i) ∈ X

/--
Projected/constrained reading of a directional-field equilibrium at a boundary:
there is no positive step from the current point along the displayed direction
that remains in the feasible set.

This predicate is deliberately weaker than `G(x*) = 0`.  It is the local
geometric alternative needed when the projected Algorithm 1 trace reaches a
boundary where the aggregate direction is not feasible.
-/
def FiniteProjectedDirectionalEquilibriumAt
    {Coord : Type*} [Fintype Coord]
    (X : Set (Coord → ℝ)) (point direction : Coord → ℝ) : Prop :=
  ¬ FiniteFeasibleDirectionAt X point direction

/-- In the full finite-coordinate space, every direction is feasible. -/
theorem finiteFeasibleDirectionAt_univ
    {Coord : Type*} [Fintype Coord]
    (point direction : Coord → ℝ) :
    FiniteFeasibleDirectionAt (Set.univ : Set (Coord → ℝ))
      point direction := by
  exact ⟨1, by norm_num, by simp⟩

/--
Convex averaging for a common finite-coordinate step.  If each voter-specific
step from `point` by the same positive radius stays feasible, then the
weighted expected step also stays feasible.
-/
theorem finiteVoterExpectation_convex_step_mem
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord]
    {X : Set (Coord → ℝ)} (hX : Convex ℝ X)
    {point : Coord → ℝ} {η : ℝ}
    {weight : Voter → ℝ} (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {dir : Voter → Coord → ℝ}
    (hpointwise :
      ∀ voter : Voter, (fun i => point i + η * dir voter i) ∈ X) :
    (fun i => point i + η * finiteVoterExpectation weight dir i) ∈ X := by
  classical
  have hsum_mem :
      (∑ voter : Voter,
        weight voter • (fun i => point i + η * dir voter i)) ∈ X := by
    exact
      hX.sum_mem
        (t := (Finset.univ : Finset Voter))
        (w := weight)
        (z := fun voter => fun i => point i + η * dir voter i)
        (by
          intro voter _hvoter
          exact hweight_nonneg voter)
        (by simpa using hweight_sum)
        (by
          intro voter _hvoter
          exact hpointwise voter)
  have hsum_eq :
      (∑ voter : Voter,
        weight voter • (fun i => point i + η * dir voter i)) =
        fun i => point i + η * finiteVoterExpectation weight dir i := by
    funext i
    calc
      (∑ voter : Voter,
          weight voter • (fun i => point i + η * dir voter i)) i
          = ∑ voter : Voter,
              weight voter * (point i + η * dir voter i) := by
            simp
      _ =
          ∑ voter : Voter,
            (weight voter * point i + weight voter * (η * dir voter i)) := by
            apply Finset.sum_congr rfl
            intro voter _hvoter
            ring
      _ =
          (∑ voter : Voter, weight voter) * point i +
            η * (∑ voter : Voter, weight voter * dir voter i) := by
            rw [Finset.sum_add_distrib]
            congr 1
            · rw [← Finset.sum_mul]
            · rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro voter _hvoter
              ring
      _ = point i + η * finiteVoterExpectation weight dir i := by
            rw [hweight_sum]
            simp [finiteVoterExpectation]
  simpa [hsum_eq] using hsum_mem

theorem finiteFeasibleDirectionAt_finiteVoterExpectation_of_common_step
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord]
    {X : Set (Coord → ℝ)} (hX : Convex ℝ X)
    {point : Coord → ℝ} {η : ℝ}
    {weight : Voter → ℝ} (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {dir : Voter → Coord → ℝ}
    (hη : 0 < η)
    (hpointwise :
      ∀ voter : Voter, (fun i => point i + η * dir voter i) ∈ X) :
    FiniteFeasibleDirectionAt X point
      (finiteVoterExpectation weight dir) :=
  ⟨η, hη,
    finiteVoterExpectation_convex_step_mem
      hX hweight_nonneg hweight_sum hpointwise⟩

theorem finiteProjectionNormalConeAt_of_firstOrder_segmentInequality
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next : Coord → ℝ}
    (hsegment :
      ∀ z, z ∈ X →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          finiteDot (fun i => raw i - next i) (fun i => z i - next i) ≤
            (ε / 2) *
              finiteDot (fun i => z i - next i) (fun i => z i - next i)) :
    FiniteProjectionNormalConeAt X raw next := by
  intro z hz
  let d := finiteDot (fun i => raw i - next i) (fun i => z i - next i)
  let B := finiteDot (fun i => z i - next i) (fun i => z i - next i)
  by_contra hnot
  have hdpos : 0 < d := lt_of_not_ge hnot
  have hBnonneg : 0 ≤ B := by
    unfold B finiteDot
    exact Finset.sum_nonneg fun i _hi => by
      nlinarith [sq_nonneg (z i - next i)]
  by_cases hBzero : B = 0
  · have hseg := hsegment z hz 1 (by norm_num) (by norm_num)
    change d ≤ (1 / 2) * B at hseg
    nlinarith
  · have hBpos : 0 < B := lt_of_le_of_ne hBnonneg (Ne.symm hBzero)
    let ε : ℝ := min 1 (d / B)
    have hεpos : 0 < ε := by
      exact lt_min (by norm_num) (div_pos hdpos hBpos)
    have hεle1 : ε ≤ 1 := min_le_left _ _
    have hεle : ε ≤ d / B := min_le_right _ _
    have hmul : ε * B ≤ d := by
      have hmul' := mul_le_mul_of_nonneg_right hεle (le_of_lt hBpos)
      have hdiv_mul : d / B * B = d := by
        field_simp [ne_of_gt hBpos]
      nlinarith
    have hupper : (ε / 2) * B ≤ d / 2 := by
      nlinarith
    have hseg := hsegment z hz ε hεpos hεle1
    change d ≤ (ε / 2) * B at hseg
    nlinarith

theorem finiteProjection_firstOrder_segmentInequality_of_l2_normProjection
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    ∀ z, z ∈ E.solutionSpace →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        finiteDot (fun i => raw i - next i) (fun i => z i - next i) ≤
          (ε / 2) *
            finiteDot (fun i => z i - next i) (fun i => z i - next i) := by
  intro z hz ε hεpos hεle
  have hupdate_eq : next = project raw := hupdate
  let y : Coord → ℝ := fun i => (1 - ε) * next i + ε * z i
  have hnext : next ∈ E.solutionSpace := by
    simpa [hupdate_eq] using (hproject raw).1
  have hmin :
      IsMinOn (fun x => E.normDistance SourceNorm.l2 x raw)
        E.solutionSpace next := by
    simpa [hupdate_eq] using (hproject raw).2
  have hy : y ∈ E.solutionSpace := by
    have hcomb :=
      (convex_iff_add_mem.mp hconv) hnext hz
        (sub_nonneg.mpr hεle) (le_of_lt hεpos) (by ring)
    simpa [y, smul_eq_mul] using hcomb
  have hdistE :
      E.normDistance SourceNorm.l2 next raw ≤
        E.normDistance SourceNorm.l2 y raw :=
    hmin hy
  have hdist :
      finiteCoordinateDistance SourceNorm.l2 next raw ≤
        finiteCoordinateDistance SourceNorm.l2 y raw := by
    simpa [hNorm SourceNorm.l2 next raw, hNorm SourceNorm.l2 y raw]
      using hdistE
  have hsq :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => next i - raw i) ≤
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => y i - raw i) := by
    rw [finiteCoordinateDistance, finiteCoordinateNorm,
      AppliedModelingLib.FiniteDimensionalNorms.l2] at hdist
    exact
      (Real.sqrt_le_sqrt_iff
        (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg
          (fun i => y i - raw i))).mp hdist
  have hquad :
      AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => y i - raw i) =
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
            (fun i => next i - raw i) -
          2 * ε *
            finiteDot (fun i => raw i - next i) (fun i => z i - next i) +
          ε ^ 2 *
            finiteDot (fun i => z i - next i) (fun i => z i - next i) := by
    unfold AppliedModelingLib.FiniteDimensionalNorms.l2Sq finiteDot y
    rw [Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hquad] at hsq
  nlinarith

theorem finiteProjectionNormalConeAt_of_l2_normProjection
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ} {raw next : Coord → ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next) :
    FiniteProjectionNormalConeAt E.solutionSpace raw next := by
  exact
    finiteProjectionNormalConeAt_of_firstOrder_segmentInequality
      (X := E.solutionSpace)
      (finiteProjection_firstOrder_segmentInequality_of_l2_normProjection
        hNorm hconv hproject hupdate)

theorem finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : FiniteFeasibleDirectionAt X next direction) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 := by
  rcases hfeasible with ⟨η, hηpos, hηmem⟩
  have hcone := hnormal (fun i => next i + η * direction i) hηmem
  have hrewrite :
      finiteDot (fun i => raw i - next i)
          (fun i => (next i + η * direction i) - next i) =
        η * finiteDot direction (fun i => raw i - next i) := by
    unfold finiteDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hscaled :
      η * finiteDot direction (fun i => raw i - next i) ≤ 0 := by
    rw [← hrewrite]
    exact hcone
  nlinarith

theorem finiteDot_projection_residual_nonpos_of_feasible_direction
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)} {raw next direction : Coord → ℝ}
    (hnormal : FiniteProjectionNormalConeAt X raw next)
    (hfeasible : (fun i => next i + direction i) ∈ X) :
    finiteDot direction (fun i => raw i - next i) ≤ 0 := by
  have hfeasibleAt : FiniteFeasibleDirectionAt X next direction :=
    ⟨1, by norm_num, by simpa using hfeasible⟩
  exact
    finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
      hnormal hfeasibleAt

theorem finiteDot_projection_residual_sum_nonpos_of_feasible_direction
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {raw next : ℕ → Coord → ℝ} {direction : Coord → ℝ}
    (hnormal : ∀ t : ℕ, FiniteProjectionNormalConeAt X (raw t) (next t))
    (hfeasible : ∀ t : ℕ, (fun i => next t i + direction i) ∈ X) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot direction (fun i => raw t i - next t i) ≤ 0 := by
  intro n
  rw [← Finset.sum_const_zero]
  exact Finset.sum_le_sum fun t _ht =>
    finiteDot_projection_residual_nonpos_of_feasible_direction
      (hnormal t) (hfeasible t)

theorem finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {raw next : ℕ → Coord → ℝ} {direction : Coord → ℝ}
    (hnormal : ∀ t : ℕ, FiniteProjectionNormalConeAt X (raw t) (next t))
    (hfeasible : ∀ t : ℕ, FiniteFeasibleDirectionAt X (next t) direction) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot direction (fun i => raw t i - next t i) ≤ 0 := by
  intro n
  rw [← Finset.sum_const_zero]
  exact Finset.sum_le_sum fun t _ht =>
    finiteDot_projection_residual_nonpos_of_feasibleDirectionAt
      (hnormal t) (hfeasible t)

theorem finiteDot_step_progress_of_projection_normalCone
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {previous raw next direction : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hraw : raw = fun i => previous i + r * direction i)
    (hprevious : previous ∈ X)
    (hnormal : FiniteProjectionNormalConeAt X raw next) :
    (1 / r) *
        finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
      finiteDot direction (fun i => next i - previous i) := by
  have hcone := hnormal previous hprevious
  have hrewrite :
      finiteDot (fun i => raw i - next i) (fun i => previous i - next i) =
        finiteDot (fun i => next i - previous i)
            (fun i => next i - previous i) -
          r * finiteDot direction (fun i => next i - previous i) := by
    subst raw
    unfold finiteDot
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hrewrite] at hcone
  have hle :
      finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
        r * finiteDot direction (fun i => next i - previous i) := by
    linarith
  have hle' :
      finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
        finiteDot direction (fun i => next i - previous i) * r := by
    simpa [mul_comm] using hle
  have hdiv :
      finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) / r ≤
        finiteDot direction (fun i => next i - previous i) :=
    (div_le_iff₀ hr).mpr hle'
  simpa [div_eq_mul_inv, one_div, mul_comm, mul_left_comm, mul_assoc] using hdiv

theorem finiteDot_self_eq_l2Sq
    {Coord : Type*} [Fintype Coord] (x : Coord → ℝ) :
    finiteDot x x = AppliedModelingLib.FiniteDimensionalNorms.l2Sq x := by
  simp [finiteDot, AppliedModelingLib.FiniteDimensionalNorms.l2Sq, pow_two]

theorem finiteDot_self_eq_finiteCoordinateNorm_l2_sq
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ) :
    finiteDot x x = finiteCoordinateNorm SourceNorm.l2 x ^ 2 := by
  rw [finiteDot_self_eq_l2Sq, finiteCoordinateNorm_l2,
    AppliedModelingLib.FiniteDimensionalNorms.l2]
  exact (Real.sq_sqrt
    (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x)).symm

theorem finiteDot_self_nonneg
    {Coord : Type*} [Fintype Coord] (x : Coord → ℝ) :
    0 ≤ finiteDot x x := by
  rw [finiteDot_self_eq_l2Sq]
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg x

theorem finiteDot_step_progress_nonneg_of_projection_normalCone
    {Coord : Type*} [Fintype Coord]
    {X : Set (Coord → ℝ)}
    {previous raw next direction : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hraw : raw = fun i => previous i + r * direction i)
    (hprevious : previous ∈ X)
    (hnormal : FiniteProjectionNormalConeAt X raw next) :
    0 ≤ finiteDot direction (fun i => next i - previous i) := by
  have hprogress :=
    finiteDot_step_progress_of_projection_normalCone
      (X := X) (previous := previous) (raw := raw) (next := next)
      (direction := direction) (r := r) hr hraw hprevious hnormal
  have hleft_nonneg :
      0 ≤
        (1 / r) *
          finiteDot (fun i => next i - previous i)
            (fun i => next i - previous i) := by
    exact mul_nonneg (div_nonneg zero_le_one (le_of_lt hr))
      (finiteDot_self_nonneg (fun i => next i - previous i))
  exact le_trans hleft_nonneg hprogress

theorem finiteDot_step_progress_of_l2_normProjection
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ}
    {previous raw next direction : Coord → ℝ} {r : ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hr : 0 < r)
    (hraw : raw = fun i => previous i + r * direction i)
    (hprevious : previous ∈ E.solutionSpace) :
    (1 / r) *
        finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
      finiteDot direction (fun i => next i - previous i) := by
  exact
    finiteDot_step_progress_of_projection_normalCone
      (X := E.solutionSpace) hr hraw hprevious
      (finiteProjectionNormalConeAt_of_l2_normProjection
        hNorm hconv hproject hupdate)

theorem exists_coord_ne_zero_of_ne_zero
    {Coord : Type*} {x : Coord → ℝ}
    (hx : x ≠ fun _ => 0) :
    ∃ i : Coord, x i ≠ 0 := by
  by_contra h
  apply hx
  funext i
  exact not_not.mp (not_exists.mp h i)

theorem finiteDot_modelBFiniteNormalizedDirection_eq_inv_mul
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (gradient direction : Coord → ℝ) :
    finiteDot (modelBFiniteNormalizedDirection SourceNorm.l2 gradient)
        direction =
      (finiteCoordinateNorm SourceNorm.l2 gradient)⁻¹ *
        finiteDot gradient direction := by
  by_cases hgradient : gradient = 0
  · subst gradient
    simp [finiteDot, modelBFiniteNormalizedDirection]
  · rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
    unfold finiteDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    change (gradient i / finiteCoordinateNorm SourceNorm.l2 gradient) * direction i = _
    rw [div_eq_mul_inv]
    ring

theorem finiteDot_gradient_normalizedDirection_eq_norm
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {gradient : Coord → ℝ}
    (hgradient : gradient ≠ fun _ => 0) :
    finiteDot gradient
        (modelBFiniteNormalizedDirection SourceNorm.l2 gradient) =
      finiteCoordinateNorm SourceNorm.l2 gradient := by
  have hpos : 0 < finiteCoordinateNorm SourceNorm.l2 gradient :=
    finiteCoordinateNorm_l2_pos_of_exists_ne_zero
      (exists_coord_ne_zero_of_ne_zero hgradient)
  have hsq :
      finiteCoordinateNorm SourceNorm.l2 gradient ^ 2 =
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq gradient := by
    rw [finiteCoordinateNorm_l2, AppliedModelingLib.FiniteDimensionalNorms.l2]
    exact Real.sq_sqrt
      (AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_nonneg gradient)
  calc
    finiteDot gradient
        (modelBFiniteNormalizedDirection SourceNorm.l2 gradient)
        =
          (finiteCoordinateNorm SourceNorm.l2 gradient)⁻¹ *
            finiteDot gradient gradient := by
          rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
          unfold finiteDot
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          change gradient i * (gradient i / finiteCoordinateNorm SourceNorm.l2 gradient) = _
          rw [div_eq_mul_inv]
          ring
    _ =
          (finiteCoordinateNorm SourceNorm.l2 gradient)⁻¹ *
            (finiteCoordinateNorm SourceNorm.l2 gradient ^ 2) := by
          rw [finiteDot_self_eq_l2Sq, hsq]
    _ = finiteCoordinateNorm SourceNorm.l2 gradient := by
          field_simp [hpos.ne']

theorem modelBFiniteNormalizedDirection_l2_norm_eq_one_of_ne_zero
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {gradient : Coord → ℝ}
    (hgradient : gradient ≠ fun _ => 0) :
    finiteCoordinateNorm SourceNorm.l2
        (modelBFiniteNormalizedDirection SourceNorm.l2 gradient) = 1 := by
  have hpos : 0 < finiteCoordinateNorm SourceNorm.l2 gradient :=
    finiteCoordinateNorm_l2_pos_of_exists_ne_zero
      (exists_coord_ne_zero_of_ne_zero hgradient)
  have hdir :
      modelBFiniteNormalizedDirection SourceNorm.l2 gradient =
        fun i => (finiteCoordinateNorm SourceNorm.l2 gradient)⁻¹ *
          gradient i := by
    rw [modelBFiniteNormalizedDirection_of_ne_zero _ _ hgradient]
    funext i
    rw [div_eq_mul_inv]
    ring
  rw [hdir, finiteCoordinateNorm_l2_smul, abs_of_pos (inv_pos.mpr hpos)]
  field_simp [hpos.ne']

theorem finiteDot_l2Sq_sub_radius_normalized_le_of_progress
    {Coord : Type*} [Fintype Coord]
    (direction displacement : Coord → ℝ) {r β : ℝ}
    (hr : 0 ≤ r)
    (hstep_sq : finiteDot displacement displacement ≤ r ^ 2)
    (hdirection_sq : finiteDot direction direction ≤ 1)
    (hprogress :
      (1 - β) * r ≤ finiteDot direction displacement) :
    finiteDot (fun i => displacement i - r * direction i)
        (fun i => displacement i - r * direction i) ≤
      2 * β * r ^ 2 := by
  have hquad :
      finiteDot (fun i => displacement i - r * direction i)
          (fun i => displacement i - r * direction i) =
        finiteDot displacement displacement -
          2 * r * finiteDot direction displacement +
          r ^ 2 * finiteDot direction direction := by
    unfold finiteDot
    calc
      ∑ i : Coord,
          (displacement i - r * direction i) *
            (displacement i - r * direction i)
          =
        ∑ i : Coord,
          (displacement i * displacement i -
            2 * r * (direction i * displacement i) +
            r ^ 2 * (direction i * direction i)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
      _ =
        (∑ i : Coord, displacement i * displacement i) -
          (∑ i : Coord, 2 * r * (direction i * displacement i)) +
          (∑ i : Coord, r ^ 2 * (direction i * direction i)) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ =
        (∑ i : Coord, displacement i * displacement i) -
          2 * r * (∑ i : Coord, direction i * displacement i) +
          r ^ 2 * (∑ i : Coord, direction i * direction i) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  have hprogress_scaled :
      2 * r * ((1 - β) * r) ≤
        2 * r * finiteDot direction displacement := by
    exact mul_le_mul_of_nonneg_left hprogress (by nlinarith)
  have hdirection_scaled :
      r ^ 2 * finiteDot direction direction ≤ r ^ 2 * 1 := by
    exact mul_le_mul_of_nonneg_left hdirection_sq (sq_nonneg r)
  rw [hquad]
  nlinarith

theorem finiteDot_abs_le_l2_mul_of_self_le_sq
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a e : Coord → ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (he : finiteDot e e ≤ B ^ 2) :
    |finiteDot a e| ≤ finiteCoordinateNorm SourceNorm.l2 a * B := by
  have hnorme : finiteCoordinateNorm SourceNorm.l2 e ≤ B := by
    have hs :
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq e ≤ B ^ 2 := by
      simpa [finiteDot_self_eq_l2Sq] using he
    have hsqrt :
        Real.sqrt (AppliedModelingLib.FiniteDimensionalNorms.l2Sq e) ≤
          Real.sqrt (B ^ 2) :=
      Real.sqrt_le_sqrt hs
    calc
      finiteCoordinateNorm SourceNorm.l2 e
          = Real.sqrt (AppliedModelingLib.FiniteDimensionalNorms.l2Sq e) := by
            rfl
      _ ≤ Real.sqrt (B ^ 2) := hsqrt
      _ = B := by
            rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hB]
  exact
    (finiteDot_abs_le_l2_mul_l2 a e).trans
      (mul_le_mul_of_nonneg_left hnorme
        (finiteCoordinateNorm_l2_nonneg a))

theorem finiteDot_fixedDirection_lower_of_normalizedProgress
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a direction displacement : Coord → ℝ) {r β κ : ℝ}
    (hr : 0 ≤ r)
    (hstep_sq : finiteDot displacement displacement ≤ r ^ 2)
    (hdirection_sq : finiteDot direction direction ≤ 1)
    (hprogress :
      (1 - β) * r ≤ finiteDot direction displacement)
    (hκ : 0 ≤ κ)
    (hβκ : 2 * β ≤ κ ^ 2) :
    r * finiteDot a direction -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) ≤
      finiteDot a displacement := by
  let err : Coord → ℝ := fun i => displacement i - r * direction i
  have herr_sq :
      finiteDot err err ≤ 2 * β * r ^ 2 := by
    simpa [err] using
      finiteDot_l2Sq_sub_radius_normalized_le_of_progress
        direction displacement hr hstep_sq hdirection_sq hprogress
  have hBnonneg : 0 ≤ κ * r := mul_nonneg hκ hr
  have hBsq : 2 * β * r ^ 2 ≤ (κ * r) ^ 2 := by
    nlinarith [hβκ, sq_nonneg r]
  have herr_bound :
      |finiteDot a err| ≤
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) :=
    finiteDot_abs_le_l2_mul_of_self_le_sq a err hBnonneg
      (le_trans herr_sq hBsq)
  have herr_lower :
      -(finiteCoordinateNorm SourceNorm.l2 a * (κ * r)) ≤
        finiteDot a err :=
    (abs_le.mp herr_bound).1
  have hdecomp :
      r * finiteDot a direction + finiteDot a err =
        finiteDot a displacement := by
    unfold finiteDot err
    calc
      r * (∑ i : Coord, a i * direction i) +
          ∑ i : Coord, a i * (displacement i - r * direction i)
          =
        (∑ i : Coord, r * (a i * direction i)) +
          ∑ i : Coord, a i * (displacement i - r * direction i) := by
          rw [Finset.mul_sum]
      _ =
        ∑ i : Coord,
          (r * (a i * direction i) +
            a i * (displacement i - r * direction i)) := by
          rw [Finset.sum_add_distrib]
      _ = ∑ i : Coord, a i * displacement i := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
  linarith

/--
Finite first-order expansion of a voter utility around a center, with the
paper's concrete `L2` finite-coordinate distance as the error scale.

This is the exact differentiability condition needed for the Model A analogue
of Theorem 3: the utility is locally its gradient linearization up to
`o(||y - x||₂)`.
-/
def FiniteModelAFirstOrderExpansionAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (gradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (voter : Voter) (center : Coord → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 y center ≤ δ →
          |E.utility voter y - E.utility voter center -
              finiteDot (gradient voter center)
                (fun i => y i - center i)| ≤
            ε * finiteCoordinateDistance SourceNorm.l2 y center

/--
Feasibility of the comparison point used in the Model A first-order argument:
the local query set contains the boundary point obtained by moving from the
current center in the selected voter's normalized-gradient direction.

In full finite-coordinate space this is automatic.  In constrained spaces this
is the exact source-side condition needed for the Taylor comparison.
-/
def ModelANormalizedGradientStepFeasibleAt
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (gradient : Voter → (Coord → ℝ) → Coord → ℝ)
    (voter : Voter) (center : Coord → ℝ) (r : ℝ) : Prop :=
  (fun i =>
    center i + r *
      modelBFiniteNormalizedDirection SourceNorm.l2
        (gradient voter center) i) ∈
    LocalNeighborhood E SourceNorm.l2 center r

/--
Local Model A maximization has positive first-order progress in the selected
voter's normalized-gradient direction.  This is the formal version of the
Taylor-expansion step in the post-Theorem-3 conjecture: compare the exact Model
A maximizer with the boundary point reached by the normalized gradient.
-/
theorem modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder_candidate_mem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {voter : Voter} {center response : Coord → ℝ} {r η : ℝ}
    (hcandidate_mem :
      ModelANormalizedGradientStepFeasibleAt E gradient voter center r)
    (hFirstOrder :
      FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient : gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hr_pos : 0 < r)
    (hr_small :
      r ≤ Classical.choose
        (hFirstOrder
          (η * finiteCoordinateNorm SourceNorm.l2 (gradient voter center))
          (mul_pos heta_pos
            (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
              (exists_coord_ne_zero_of_ne_zero hgradient)))))
    (hresponse :
      ModelAResponseAt E SourceNorm.l2 center r voter response) :
    (1 - 2 * η) * r ≤
      finiteDot
        (modelBFiniteNormalizedDirection SourceNorm.l2
          (gradient voter center))
        (fun i => response i - center i) := by
  let g : Coord → ℝ := gradient voter center
  let n : Coord → ℝ := modelBFiniteNormalizedDirection SourceNorm.l2 g
  let candidate : Coord → ℝ := fun i => center i + r * n i
  have hgpos : 0 < finiteCoordinateNorm SourceNorm.l2 g :=
    finiteCoordinateNorm_l2_pos_of_exists_ne_zero
      (exists_coord_ne_zero_of_ne_zero hgradient)
  let ε : ℝ := η * finiteCoordinateNorm SourceNorm.l2 g
  have hεpos : 0 < ε := mul_pos heta_pos hgpos
  let δ : ℝ := Classical.choose (hFirstOrder ε hεpos)
  have hδ : 0 < δ ∧
      ∀ y : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 y center ≤ δ →
          |E.utility voter y - E.utility voter center -
              finiteDot g (fun i => y i - center i)| ≤
            ε * finiteCoordinateDistance SourceNorm.l2 y center :=
    Classical.choose_spec (hFirstOrder ε hεpos)
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hresp_dist_r :
      finiteCoordinateDistance SourceNorm.l2 response center ≤ r := by
    have hdistE : E.normDistance SourceNorm.l2 response center ≤ r :=
      hresponse.1.2
    simpa [hNorm SourceNorm.l2 response center] using hdistE
  have hresp_dist_δ :
      finiteCoordinateDistance SourceNorm.l2 response center ≤ δ :=
    le_trans hresp_dist_r hr_small
  have hcandidate_response :
      ModelBFiniteResponseAt SourceNorm.l2 center r g candidate := by
    rfl
  have hcandidate_dist_r :
      finiteCoordinateDistance SourceNorm.l2 candidate center ≤ r :=
    modelBFiniteResponseAt_l2_within_radius hr_nonneg hcandidate_response
  have hcandidate_dist_δ :
      finiteCoordinateDistance SourceNorm.l2 candidate center ≤ δ :=
    le_trans hcandidate_dist_r hr_small
  have hcandidate_mem_local :
      candidate ∈ LocalNeighborhood E SourceNorm.l2 center r := by
    simpa [ModelANormalizedGradientStepFeasibleAt, candidate, n, g] using
      hcandidate_mem
  have hmax : E.utility voter candidate ≤ E.utility voter response :=
    hresponse.2 candidate hcandidate_mem_local
  have hresp_fo := (hδ.2 response hresp_dist_δ)
  have hcandidate_fo := (hδ.2 candidate hcandidate_dist_δ)
  have hresp_upper :
      E.utility voter response ≤
        E.utility voter center +
          finiteDot g (fun i => response i - center i) + ε * r := by
    have hle_abs :
        E.utility voter response - E.utility voter center -
            finiteDot g (fun i => response i - center i) ≤
          ε * finiteCoordinateDistance SourceNorm.l2 response center :=
      (abs_le.mp hresp_fo).2
    have hε_nonneg : 0 ≤ ε := le_of_lt hεpos
    have hdist_scaled :
        ε * finiteCoordinateDistance SourceNorm.l2 response center ≤ ε * r :=
      mul_le_mul_of_nonneg_left hresp_dist_r hε_nonneg
    linarith
  have hcandidate_lower :
      E.utility voter center +
          finiteDot g (fun i => candidate i - center i) - ε * r ≤
        E.utility voter candidate := by
    have hle_abs :
        -(ε * finiteCoordinateDistance SourceNorm.l2 candidate center) ≤
          E.utility voter candidate - E.utility voter center -
            finiteDot g (fun i => candidate i - center i) :=
      (abs_le.mp hcandidate_fo).1
    have hε_nonneg : 0 ≤ ε := le_of_lt hεpos
    have hdist_scaled :
        ε * finiteCoordinateDistance SourceNorm.l2 candidate center ≤ ε * r :=
      mul_le_mul_of_nonneg_left hcandidate_dist_r hε_nonneg
    linarith
  have hdot_candidate :
      finiteDot g (fun i => candidate i - center i) =
        r * finiteCoordinateNorm SourceNorm.l2 g := by
    have hdiff :
        (fun i => candidate i - center i) = fun i => r * n i := by
      funext i
      simp [candidate, n]
    rw [hdiff]
    calc
      finiteDot g (fun i => r * n i)
          = ∑ i : Coord, r * (g i * n i) := by
            simp [finiteDot, mul_left_comm]
      _ = r * finiteDot g n := by
            simp [finiteDot, Finset.mul_sum]
      _ = r * finiteCoordinateNorm SourceNorm.l2 g := by
            rw [finiteDot_gradient_normalizedDirection_eq_norm hgradient]
  have hdot_lower :
      r * finiteCoordinateNorm SourceNorm.l2 g - 2 * ε * r ≤
        finiteDot g (fun i => response i - center i) := by
    linarith
  have hnorm_dot :
      finiteDot n (fun i => response i - center i) =
        (finiteCoordinateNorm SourceNorm.l2 g)⁻¹ *
          finiteDot g (fun i => response i - center i) := by
    simpa [n, g] using
      finiteDot_modelBFiniteNormalizedDirection_eq_inv_mul
        g (fun i => response i - center i)
  have hscaled :
      (finiteCoordinateNorm SourceNorm.l2 g) *
        ((1 - 2 * η) * r) ≤
      finiteDot g (fun i => response i - center i) := by
    dsimp [ε] at hdot_lower
    nlinarith [hdot_lower]
  have hdiv :
      (1 - 2 * η) * r ≤
        (finiteCoordinateNorm SourceNorm.l2 g)⁻¹ *
          finiteDot g (fun i => response i - center i) := by
    rw [← div_eq_inv_mul]
    have hscaled' :
        ((1 - 2 * η) * r) *
            finiteCoordinateNorm SourceNorm.l2 g ≤
          finiteDot g (fun i => response i - center i) := by
      nlinarith [hscaled]
    exact (le_div_iff₀ hgpos).2 hscaled'
  change (1 - 2 * η) * r ≤
    finiteDot n (fun i => response i - center i)
  rw [hnorm_dot]
  exact hdiv

theorem modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {voter : Voter} {center response : Coord → ℝ} {r η : ℝ}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hFirstOrder :
      FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient : gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hr_pos : 0 < r)
    (hr_small :
      r ≤ Classical.choose
        (hFirstOrder
          (η * finiteCoordinateNorm SourceNorm.l2 (gradient voter center))
          (mul_pos heta_pos
            (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
              (exists_coord_ne_zero_of_ne_zero hgradient)))))
    (hresponse :
      ModelAResponseAt E SourceNorm.l2 center r voter response) :
    (1 - 2 * η) * r ≤
      finiteDot
        (modelBFiniteNormalizedDirection SourceNorm.l2
          (gradient voter center))
        (fun i => response i - center i) := by
  let candidate : Coord → ℝ :=
    fun i =>
      center i + r *
        modelBFiniteNormalizedDirection SourceNorm.l2
          (gradient voter center) i
  have hcandidate_response :
      ModelBFiniteResponseAt SourceNorm.l2 center r
        (gradient voter center) candidate := by
    rfl
  have hcandidate_dist_r :
      finiteCoordinateDistance SourceNorm.l2 candidate center ≤ r :=
    modelBFiniteResponseAt_l2_within_radius
      (le_of_lt hr_pos) hcandidate_response
  have hcandidate_mem :
      ModelANormalizedGradientStepFeasibleAt E gradient voter center r := by
    refine ⟨?_, ?_⟩
    · rw [hUniv]
      exact Set.mem_univ _
    · simpa [ModelANormalizedGradientStepFeasibleAt, candidate,
        hNorm SourceNorm.l2 candidate center] using hcandidate_dist_r
  exact
    modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder_candidate_mem
      hNorm hcandidate_mem hFirstOrder hgradient heta_pos hr_pos hr_small
      hresponse

/--
Weighted expected version of the Model A local Taylor comparison.  If every
voter utility has the same first-order error tolerance at the current center
and every selected local maximizer is a Model A response, then the weighted
expected progress in each selected voter's own normalized-gradient direction is
at least `(1 - 2η) r`.
-/
theorem modelAResponseAt_weighted_expected_own_normalizedGradient_progress_of_firstOrder
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {center : Coord → ℝ} {response : Voter → Coord → ℝ} {r η : ℝ}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hFirstOrder :
      ∀ voter : Voter,
        FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient :
      ∀ voter : Voter, gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hr_pos : 0 < r)
    (hr_small :
      ∀ voter : Voter,
        r ≤ Classical.choose
          (hFirstOrder voter
            (η * finiteCoordinateNorm SourceNorm.l2
              (gradient voter center))
            (mul_pos heta_pos
              (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
                (exists_coord_ne_zero_of_ne_zero
                  (hgradient voter))))))
    (hresponse :
      ∀ voter : Voter,
        ModelAResponseAt E SourceNorm.l2 center r voter
          (response voter)) :
    (1 - 2 * η) * r ≤
      ∑ voter : Voter,
        weight voter *
          finiteDot
            (modelBFiniteNormalizedDirection SourceNorm.l2
              (gradient voter center))
            (fun i => response voter i - center i) := by
  let lower : ℝ := (1 - 2 * η) * r
  have hpoint :
      ∀ voter : Voter,
        lower ≤
          finiteDot
            (modelBFiniteNormalizedDirection SourceNorm.l2
              (gradient voter center))
            (fun i => response voter i - center i) := by
    intro voter
    dsimp [lower]
    exact
      modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder
        hNorm hUniv (hFirstOrder voter) (hgradient voter) heta_pos hr_pos
        (hr_small voter) (hresponse voter)
  have hweighted :
      ∑ voter : Voter, weight voter * lower ≤
        ∑ voter : Voter,
          weight voter *
            finiteDot
              (modelBFiniteNormalizedDirection SourceNorm.l2
                (gradient voter center))
              (fun i => response voter i - center i) := by
    exact Finset.sum_le_sum fun voter _hvoter =>
      mul_le_mul_of_nonneg_left (hpoint voter) (hweight_nonneg voter)
  calc
    lower = (∑ voter : Voter, weight voter) * lower := by
      rw [hweight_sum]
      ring
    _ = ∑ voter : Voter, weight voter * lower := by
      rw [Finset.sum_mul]
    _ ≤
        ∑ voter : Voter,
          weight voter *
            finiteDot
              (modelBFiniteNormalizedDirection SourceNorm.l2
                (gradient voter center))
              (fun i => response voter i - center i) := hweighted

/--
Fixed-direction lower bound for one Model A local maximizer.  The local
first-order comparison says the response has almost full projection on the
selected voter's normalized-gradient direction; the squared-closeness algebra
then converts this to progress against any fixed finite-dot direction `a`, up
to a tunable `κ r` error.
-/
theorem modelAResponseAt_finiteDot_fixedDirection_lower_of_firstOrder
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {voter : Voter} {center response a : Coord → ℝ} {r η κ : ℝ}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hFirstOrder :
      FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient : gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hr_small :
      r ≤ Classical.choose
        (hFirstOrder
          (η * finiteCoordinateNorm SourceNorm.l2 (gradient voter center))
          (mul_pos heta_pos
            (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
              (exists_coord_ne_zero_of_ne_zero hgradient)))))
    (hresponse :
      ModelAResponseAt E SourceNorm.l2 center r voter response) :
    r *
        finiteDot a
          (modelBFiniteNormalizedDirection SourceNorm.l2
            (gradient voter center)) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) ≤
      finiteDot a (fun i => response i - center i) := by
  let n : Coord → ℝ :=
    modelBFiniteNormalizedDirection SourceNorm.l2 (gradient voter center)
  let d : Coord → ℝ := fun i => response i - center i
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hprogress :
      (1 - 2 * η) * r ≤ finiteDot n d := by
    simpa [n, d] using
      modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder
        hNorm hUniv hFirstOrder hgradient heta_pos hr_pos hr_small hresponse
  have hresp_dist_r :
      finiteCoordinateDistance SourceNorm.l2 response center ≤ r := by
    have hdistE : E.normDistance SourceNorm.l2 response center ≤ r :=
      hresponse.1.2
    simpa [hNorm SourceNorm.l2 response center] using hdistE
  have hnormd :
      finiteCoordinateNorm SourceNorm.l2 d ≤ r := by
    simpa [d, finiteCoordinateDistance] using hresp_dist_r
  have hstep_sq : finiteDot d d ≤ r ^ 2 := by
    rw [finiteDot_self_eq_finiteCoordinateNorm_l2_sq]
    exact
      (sq_le_sq₀ (finiteCoordinateNorm_l2_nonneg d) hr_nonneg).mpr hnormd
  have hn_sq : finiteDot n n ≤ 1 := by
    rw [finiteDot_self_eq_finiteCoordinateNorm_l2_sq]
    have hn_norm :
        finiteCoordinateNorm SourceNorm.l2 n = 1 := by
      simpa [n] using
        modelBFiniteNormalizedDirection_l2_norm_eq_one_of_ne_zero
          (gradient := gradient voter center) hgradient
    rw [hn_norm]
    norm_num
  have hβκ : 2 * (2 * η) ≤ κ ^ 2 := by
    nlinarith
  simpa [n, d] using
    finiteDot_fixedDirection_lower_of_normalizedProgress
      a n d hr_nonneg hstep_sq hn_sq hprogress hκ hβκ

/--
Fixed-direction lower bound for one Model A local maximizer under the exact
comparison-point feasibility condition.  This is the constrained-space version
of `modelAResponseAt_finiteDot_fixedDirection_lower_of_firstOrder`.
-/
theorem modelAResponseAt_finiteDot_fixedDirection_lower_of_firstOrder_candidate_mem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {voter : Voter} {center response a : Coord → ℝ} {r η κ : ℝ}
    (hcandidate_mem :
      ModelANormalizedGradientStepFeasibleAt E gradient voter center r)
    (hFirstOrder :
      FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient : gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hr_small :
      r ≤ Classical.choose
        (hFirstOrder
          (η * finiteCoordinateNorm SourceNorm.l2 (gradient voter center))
          (mul_pos heta_pos
            (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
              (exists_coord_ne_zero_of_ne_zero hgradient)))))
    (hresponse :
      ModelAResponseAt E SourceNorm.l2 center r voter response) :
    r *
        finiteDot a
          (modelBFiniteNormalizedDirection SourceNorm.l2
            (gradient voter center)) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) ≤
      finiteDot a (fun i => response i - center i) := by
  let n : Coord → ℝ :=
    modelBFiniteNormalizedDirection SourceNorm.l2 (gradient voter center)
  let d : Coord → ℝ := fun i => response i - center i
  have hr_nonneg : 0 ≤ r := le_of_lt hr_pos
  have hprogress :
      (1 - 2 * η) * r ≤ finiteDot n d := by
    simpa [n, d] using
      modelAResponseAt_finiteDot_normalizedGradient_progress_of_firstOrder_candidate_mem
        hNorm hcandidate_mem hFirstOrder hgradient heta_pos hr_pos hr_small
        hresponse
  have hresp_dist_r :
      finiteCoordinateDistance SourceNorm.l2 response center ≤ r := by
    have hdistE : E.normDistance SourceNorm.l2 response center ≤ r :=
      hresponse.1.2
    simpa [hNorm SourceNorm.l2 response center] using hdistE
  have hnormd :
      finiteCoordinateNorm SourceNorm.l2 d ≤ r := by
    simpa [d, finiteCoordinateDistance] using hresp_dist_r
  have hstep_sq : finiteDot d d ≤ r ^ 2 := by
    rw [finiteDot_self_eq_finiteCoordinateNorm_l2_sq]
    exact
      (sq_le_sq₀ (finiteCoordinateNorm_l2_nonneg d) hr_nonneg).mpr hnormd
  have hn_sq : finiteDot n n ≤ 1 := by
    rw [finiteDot_self_eq_finiteCoordinateNorm_l2_sq]
    have hn_norm :
        finiteCoordinateNorm SourceNorm.l2 n = 1 := by
      simpa [n] using
        modelBFiniteNormalizedDirection_l2_norm_eq_one_of_ne_zero
          (gradient := gradient voter center) hgradient
    rw [hn_norm]
    norm_num
  have hβκ : 2 * (2 * η) ≤ κ ^ 2 := by
    nlinarith
  simpa [n, d] using
    finiteDot_fixedDirection_lower_of_normalizedProgress
      a n d hr_nonneg hstep_sq hn_sq hprogress hκ hβκ

/--
Weighted fixed-direction lower bound for Model A local maximizers.  This is the
finite-voter uniformization bridge for the conjectural Theorem 3 analogue:
after choosing `κ` so that `κ²` dominates the first-order error parameter, the
weighted expected Model A raw finite-dot progress is bounded below by the
paper's normalized-gradient field, with an explicit `κ r` error.
-/
theorem modelAResponseAt_weighted_expected_fixedDirection_lower_of_firstOrder
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {center : Coord → ℝ} {response : Voter → Coord → ℝ}
    {a : Coord → ℝ} {r η κ : ℝ}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hFirstOrder :
      ∀ voter : Voter,
        FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient :
      ∀ voter : Voter, gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hr_small :
      ∀ voter : Voter,
        r ≤ Classical.choose
          (hFirstOrder voter
            (η * finiteCoordinateNorm SourceNorm.l2
              (gradient voter center))
            (mul_pos heta_pos
              (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
                (exists_coord_ne_zero_of_ne_zero
                  (hgradient voter))))))
    (hresponse :
      ∀ voter : Voter,
        ModelAResponseAt E SourceNorm.l2 center r voter
          (response voter)) :
    r *
        finiteDot a
          (finiteTheorem3DirectionalField weight gradient center) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) ≤
      ∑ voter : Voter,
        weight voter *
          finiteDot a (fun i => response voter i - center i) := by
  let C : ℝ := finiteCoordinateNorm SourceNorm.l2 a * (κ * r)
  let ownDot : Voter → ℝ := fun voter =>
    finiteDot a
      (modelBFiniteNormalizedDirection SourceNorm.l2
        (gradient voter center))
  let responseDot : Voter → ℝ := fun voter =>
    finiteDot a (fun i => response voter i - center i)
  have hpoint :
      ∀ voter : Voter, r * ownDot voter - C ≤ responseDot voter := by
    intro voter
    dsimp [ownDot, responseDot, C]
    exact
      modelAResponseAt_finiteDot_fixedDirection_lower_of_firstOrder
        hNorm hUniv (hFirstOrder voter) (hgradient voter) heta_pos hκ hηκ
        hr_pos (hr_small voter) (hresponse voter)
  have hweighted :
      ∑ voter : Voter, weight voter * (r * ownDot voter - C) ≤
        ∑ voter : Voter, weight voter * responseDot voter := by
    exact Finset.sum_le_sum fun voter _hvoter =>
      mul_le_mul_of_nonneg_left (hpoint voter) (hweight_nonneg voter)
  have hown :
      (∑ voter : Voter, weight voter * ownDot voter) =
        finiteDot a (finiteTheorem3DirectionalField weight gradient center) := by
    simpa [ownDot] using
      finiteTheorem3DirectionalField_expected_finiteDot_modelBNormalizedDirection
        weight gradient center a
  have hleft :
      (∑ voter : Voter, weight voter * (r * ownDot voter - C)) =
        r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
          C := by
    calc
      (∑ voter : Voter, weight voter * (r * ownDot voter - C))
          =
        (∑ voter : Voter, weight voter * (r * ownDot voter)) -
          ∑ voter : Voter, weight voter * C := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro voter _hvoter
          ring
      _ =
        r * (∑ voter : Voter, weight voter * ownDot voter) -
          C * (∑ voter : Voter, weight voter) := by
          congr 1
          · calc
              (∑ voter : Voter, weight voter * (r * ownDot voter))
                  =
                ∑ voter : Voter, r * (weight voter * ownDot voter) := by
                  apply Finset.sum_congr rfl
                  intro voter _hvoter
                  ring
              _ = r * (∑ voter : Voter, weight voter * ownDot voter) := by
                  rw [Finset.mul_sum]
          · calc
              (∑ voter : Voter, weight voter * C)
                  =
                ∑ voter : Voter, C * weight voter := by
                  apply Finset.sum_congr rfl
                  intro voter _hvoter
                  ring
              _ = C * (∑ voter : Voter, weight voter) := by
                  rw [Finset.mul_sum]
      _ =
        r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
          C := by
          rw [hown, hweight_sum]
          ring
  calc
    r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r)
        =
          ∑ voter : Voter, weight voter * (r * ownDot voter - C) := by
          exact hleft.symm
    _ ≤ ∑ voter : Voter, weight voter * responseDot voter := hweighted
    _ =
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response voter i - center i) := by
          rfl

/--
Weighted fixed-direction lower bound under per-voter normalized-gradient
comparison feasibility.  This replaces the full-space hypothesis by exactly
the feasible comparison points used in the Model A Taylor argument.
-/
theorem modelAResponseAt_weighted_expected_fixedDirection_lower_of_firstOrder_candidate_mem
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {center : Coord → ℝ} {response : Voter → Coord → ℝ}
    {a : Coord → ℝ} {r η κ : ℝ}
    (hcandidate_mem :
      ∀ voter : Voter,
        ModelANormalizedGradientStepFeasibleAt E gradient voter center r)
    (hFirstOrder :
      ∀ voter : Voter,
        FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient :
      ∀ voter : Voter, gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hr_small :
      ∀ voter : Voter,
        r ≤ Classical.choose
          (hFirstOrder voter
            (η * finiteCoordinateNorm SourceNorm.l2
              (gradient voter center))
            (mul_pos heta_pos
              (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
                (exists_coord_ne_zero_of_ne_zero
                  (hgradient voter))))))
    (hresponse :
      ∀ voter : Voter,
        ModelAResponseAt E SourceNorm.l2 center r voter
          (response voter)) :
    r *
        finiteDot a
          (finiteTheorem3DirectionalField weight gradient center) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r) ≤
      ∑ voter : Voter,
        weight voter *
          finiteDot a (fun i => response voter i - center i) := by
  let C : ℝ := finiteCoordinateNorm SourceNorm.l2 a * (κ * r)
  let ownDot : Voter → ℝ := fun voter =>
    finiteDot a
      (modelBFiniteNormalizedDirection SourceNorm.l2
        (gradient voter center))
  let responseDot : Voter → ℝ := fun voter =>
    finiteDot a (fun i => response voter i - center i)
  have hpoint :
      ∀ voter : Voter, r * ownDot voter - C ≤ responseDot voter := by
    intro voter
    dsimp [ownDot, responseDot, C]
    exact
      modelAResponseAt_finiteDot_fixedDirection_lower_of_firstOrder_candidate_mem
        hNorm (hcandidate_mem voter) (hFirstOrder voter) (hgradient voter)
        heta_pos hκ hηκ hr_pos (hr_small voter) (hresponse voter)
  have hweighted :
      ∑ voter : Voter, weight voter * (r * ownDot voter - C) ≤
        ∑ voter : Voter, weight voter * responseDot voter := by
    exact Finset.sum_le_sum fun voter _hvoter =>
      mul_le_mul_of_nonneg_left (hpoint voter) (hweight_nonneg voter)
  have hown :
      (∑ voter : Voter, weight voter * ownDot voter) =
        finiteDot a (finiteTheorem3DirectionalField weight gradient center) := by
    simpa [ownDot] using
      finiteTheorem3DirectionalField_expected_finiteDot_modelBNormalizedDirection
        weight gradient center a
  have hleft :
      (∑ voter : Voter, weight voter * (r * ownDot voter - C)) =
        r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
          C := by
    calc
      (∑ voter : Voter, weight voter * (r * ownDot voter - C))
          =
        (∑ voter : Voter, weight voter * (r * ownDot voter)) -
          ∑ voter : Voter, weight voter * C := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro voter _hvoter
          ring
      _ =
        r * (∑ voter : Voter, weight voter * ownDot voter) -
          C * (∑ voter : Voter, weight voter) := by
          congr 1
          · calc
              (∑ voter : Voter, weight voter * (r * ownDot voter))
                  =
                ∑ voter : Voter, r * (weight voter * ownDot voter) := by
                  apply Finset.sum_congr rfl
                  intro voter _hvoter
                  ring
              _ = r * (∑ voter : Voter, weight voter * ownDot voter) := by
                  rw [Finset.mul_sum]
          · calc
              (∑ voter : Voter, weight voter * C)
                  =
                ∑ voter : Voter, C * weight voter := by
                  apply Finset.sum_congr rfl
                  intro voter _hvoter
                  ring
              _ = C * (∑ voter : Voter, weight voter) := by
                  rw [Finset.mul_sum]
      _ =
        r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
          C := by
          rw [hown, hweight_sum]
          ring
  calc
    r * finiteDot a (finiteTheorem3DirectionalField weight gradient center) -
        finiteCoordinateNorm SourceNorm.l2 a * (κ * r)
        =
          ∑ voter : Voter, weight voter * (r * ownDot voter - C) := by
          exact hleft.symm
    _ ≤ ∑ voter : Voter, weight voter * responseDot voter := hweighted
    _ =
        ∑ voter : Voter,
          weight voter *
            finiteDot a (fun i => response voter i - center i) := by
          rfl

/--
Drift-ready Model A finite-voter bridge.  Once the limiting direction `a`
has positive dot product at the current field value and the first-order
alignment error is chosen smaller than half of that drift, the weighted
expected Model A raw response has positive scalar progress.
-/
theorem modelAResponseAt_weighted_expected_fixedDirection_drift_lower_of_firstOrder
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {center : Coord → ℝ} {response : Voter → Coord → ℝ}
    {a : Coord → ℝ} {r η κ c : ℝ}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ)))
    (hFirstOrder :
      ∀ voter : Voter,
        FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient :
      ∀ voter : Voter, gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hdrift :
      c ≤ finiteDot a (finiteTheorem3DirectionalField weight gradient center))
    (hκsmall : finiteCoordinateNorm SourceNorm.l2 a * κ ≤ c / 2)
    (hr_small :
      ∀ voter : Voter,
        r ≤ Classical.choose
          (hFirstOrder voter
            (η * finiteCoordinateNorm SourceNorm.l2
              (gradient voter center))
            (mul_pos heta_pos
              (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
                (exists_coord_ne_zero_of_ne_zero
                  (hgradient voter))))))
    (hresponse :
      ∀ voter : Voter,
        ModelAResponseAt E SourceNorm.l2 center r voter
          (response voter)) :
    (c / 2) * r ≤
      ∑ voter : Voter,
        weight voter *
          finiteDot a (fun i => response voter i - center i) := by
  have hbridge :=
    modelAResponseAt_weighted_expected_fixedDirection_lower_of_firstOrder
      hNorm hweight_nonneg hweight_sum hUniv hFirstOrder hgradient heta_pos
      hκ hηκ hr_pos hr_small hresponse (a := a)
  have htarget :
      (c / 2) * r ≤
        r * finiteDot a
            (finiteTheorem3DirectionalField weight gradient center) -
          finiteCoordinateNorm SourceNorm.l2 a * (κ * r) := by
    nlinarith [hdrift, hκsmall, le_of_lt hr_pos]
  exact le_trans htarget hbridge

/--
Drift-ready Model A bridge under per-voter normalized-gradient comparison
feasibility, replacing the full-space hypothesis in the finite-voter step.
-/
theorem modelAResponseAt_weighted_expected_fixedDirection_drift_lower_of_firstOrder_candidate_mem
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hNorm : UsesFiniteCoordinateNormDistance E)
    {weight : Voter → ℝ}
    (hweight_nonneg : ∀ voter, 0 ≤ weight voter)
    (hweight_sum : (∑ voter : Voter, weight voter) = 1)
    {gradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {center : Coord → ℝ} {response : Voter → Coord → ℝ}
    {a : Coord → ℝ} {r η κ c : ℝ}
    (hcandidate_mem :
      ∀ voter : Voter,
        ModelANormalizedGradientStepFeasibleAt E gradient voter center r)
    (hFirstOrder :
      ∀ voter : Voter,
        FiniteModelAFirstOrderExpansionAt E gradient voter center)
    (hgradient :
      ∀ voter : Voter, gradient voter center ≠ fun _ => 0)
    (heta_pos : 0 < η)
    (hκ : 0 ≤ κ)
    (hηκ : 4 * η ≤ κ ^ 2)
    (hr_pos : 0 < r)
    (hdrift :
      c ≤ finiteDot a (finiteTheorem3DirectionalField weight gradient center))
    (hκsmall : finiteCoordinateNorm SourceNorm.l2 a * κ ≤ c / 2)
    (hr_small :
      ∀ voter : Voter,
        r ≤ Classical.choose
          (hFirstOrder voter
            (η * finiteCoordinateNorm SourceNorm.l2
              (gradient voter center))
            (mul_pos heta_pos
              (finiteCoordinateNorm_l2_pos_of_exists_ne_zero
                (exists_coord_ne_zero_of_ne_zero
                  (hgradient voter))))))
    (hresponse :
      ∀ voter : Voter,
        ModelAResponseAt E SourceNorm.l2 center r voter
          (response voter)) :
    (c / 2) * r ≤
      ∑ voter : Voter,
        weight voter *
          finiteDot a (fun i => response voter i - center i) := by
  have hbridge :=
    modelAResponseAt_weighted_expected_fixedDirection_lower_of_firstOrder_candidate_mem
      hNorm hweight_nonneg hweight_sum hcandidate_mem hFirstOrder hgradient
      heta_pos hκ hηκ hr_pos hr_small hresponse (a := a)
  have htarget :
      (c / 2) * r ≤
        r * finiteDot a
            (finiteTheorem3DirectionalField weight gradient center) -
          finiteCoordinateNorm SourceNorm.l2 a * (κ * r) := by
    nlinarith [hdrift, hκsmall, le_of_lt hr_pos]
  exact le_trans htarget hbridge

/--
Parameter choice for the Model A first-order alignment argument.  Any positive
tail drift `c` admits positive `η` and nonnegative `κ` with
`4η <= κ²` and `||a||₂ κ <= c/2`, exactly the numeric side conditions consumed
by `modelAResponseAt_weighted_expected_fixedDirection_drift_lower_of_firstOrder`.
-/
theorem exists_modelA_firstOrder_alignment_parameters
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (a : Coord → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ η κ : ℝ,
      0 < η ∧ 0 ≤ κ ∧ 4 * η ≤ κ ^ 2 ∧
        finiteCoordinateNorm SourceNorm.l2 a * κ ≤ c / 2 := by
  let A : ℝ := finiteCoordinateNorm SourceNorm.l2 a
  let κ : ℝ := c / (2 * (A + 1))
  let η : ℝ := κ ^ 2 / 4
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact finiteCoordinateNorm_l2_nonneg a
  have hden_pos : 0 < 2 * (A + 1) := by
    nlinarith
  have hκ_pos : 0 < κ := by
    dsimp [κ]
    exact div_pos hc hden_pos
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos (sq_pos_of_ne_zero (ne_of_gt hκ_pos)) (by norm_num)
  refine ⟨η, κ, hη_pos, le_of_lt hκ_pos, ?_, ?_⟩
  · dsimp [η]
    nlinarith
  · have hdiv :
        A * c / (2 * (A + 1)) ≤ c / 2 := by
      refine (div_le_iff₀ hden_pos).2 ?_
      nlinarith [mul_le_mul_of_nonneg_right
        (show A ≤ A + 1 by nlinarith) (le_of_lt hc)]
    dsimp [κ, A]
    simpa [mul_div_assoc] using hdiv

theorem finiteDot_self_pos_of_ne_zero
    {Coord : Type*} [Fintype Coord]
    {x : Coord → ℝ} (hx : x ≠ fun _ => 0) :
    0 < finiteDot x x := by
  rw [finiteDot_self_eq_l2Sq]
  exact AppliedModelingLib.FiniteDimensionalNorms.normL2Sq_pos_of_exists_ne_zero
    (exists_coord_ne_zero_of_ne_zero hx)

theorem finiteDot_self_pos_of_ne_zeroDirection
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {xstar : Coord → ℝ}
    (hzero : E.zeroDirection = fun _ => 0)
    (hne : E.directionalField xstar ≠ E.zeroDirection) :
    0 < finiteDot (E.directionalField xstar) (E.directionalField xstar) := by
  exact finiteDot_self_pos_of_ne_zero (by
    intro hfield
    exact hne (by simpa [hzero] using hfield))

/--
Projection of a point onto the nonzero field direction at the candidate limit.
This is the scalar coordinate used by the analytic drift contradiction.
-/
noncomputable def theorem3FiniteFieldProjection
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (xstar y : Coord → ℝ) : ℝ :=
  finiteDot (E.directionalField xstar) y

/--
Theorem 3 scalar projection using the concrete finite-coordinate
normalized-gradient field rather than the abstract environment field.  This is
definitionally the same projection once a `FiniteTheorem3DirectionalFieldModel`
is installed, but it lets the remaining progress boundary name the paper's
displayed field directly.
-/
noncomputable def theorem3ConcreteFiniteFieldProjection
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar y : Coord → ℝ) : ℝ :=
  finiteDot (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar) y

theorem theorem3ConcreteFiniteFieldProjection_eq
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar y : Coord → ℝ) :
    theorem3ConcreteFiniteFieldProjection M xstar y =
      theorem3FiniteFieldProjection E xstar y := by
  simp [theorem3ConcreteFiniteFieldProjection, theorem3FiniteFieldProjection,
    M.directionalField_eq]

theorem theorem3FiniteFieldProjection_step_sub
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (xstar x y : Coord → ℝ) :
    theorem3FiniteFieldProjection E xstar y -
        theorem3FiniteFieldProjection E xstar x =
      finiteDot (E.directionalField xstar) (fun i => y i - x i) := by
  unfold theorem3FiniteFieldProjection finiteDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem theorem3ConcreteFiniteFieldProjection_step_sub
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar x y : Coord → ℝ) :
    theorem3ConcreteFiniteFieldProjection M xstar y -
        theorem3ConcreteFiniteFieldProjection M xstar x =
      finiteDot
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
        (fun i => y i - x i) := by
  unfold theorem3ConcreteFiniteFieldProjection finiteDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/--
Finite-dot telescoping for the scalar projection used in the Theorem 3
contradiction.  This is the vector analogue of the coordinate telescoping
identity: the projected tail displacement is the sum of one-step finite-dot
increments.
-/
theorem theorem3ConcreteFiniteFieldProjection_tail_eq_base_add_sum_steps
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar : Coord → ℝ) (trajectory : ℕ → Coord → ℝ) (N n : ℕ) :
    theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N)) =
      theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
        ∑ t ∈ Finset.range n,
          finiteDot
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
            (fun i => trajectory (t + 1 + N) i - trajectory (t + N) i) := by
  let s : ℕ → ℝ := fun k =>
    theorem3ConcreteFiniteFieldProjection M xstar (trajectory k)
  have htel := scalar_tail_displacement_eq_sum_increments s N n
  have hsteps :
      ∑ t ∈ Finset.range n, (s (t + 1 + N) - s (t + N)) =
        ∑ t ∈ Finset.range n,
          finiteDot
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
            (fun i => trajectory (t + 1 + N) i - trajectory (t + N) i) := by
    apply Finset.sum_congr rfl
    intro t _ht
    dsimp [s]
    exact theorem3ConcreteFiniteFieldProjection_step_sub
      M xstar (trajectory (t + N)) (trajectory (t + 1 + N))
  calc
    theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N))
        =
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
            (s (n + N) - s N) := by
          dsimp [s]
          ring
    _ =
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
            ∑ t ∈ Finset.range n, (s (t + 1 + N) - s (t + N)) := by
          rw [htel]
    _ =
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
            ∑ t ∈ Finset.range n,
              finiteDot
                (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
                (fun i =>
                  trajectory (t + 1 + N) i - trajectory (t + N) i) := by
          rw [hsteps]

/--
Exact residual identity for the finite-dot projection slack.  The difference
between accumulated selected raw finite-dot increments and the actual scalar
projection movement is precisely the sum of finite-dot residuals between the
selected raw response and the projected next iterate.
-/
theorem theorem3ConcreteFiniteFieldProjection_selectedRaw_residual_identity
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar : Coord → ℝ) (trajectory : ℕ → Coord → ℝ)
    (sampledVoter : ℕ → Voter) (response : ℕ → Voter → Coord → ℝ)
    (N n : ℕ) :
    theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
        ∑ t ∈ Finset.range n,
          finiteDot
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
            (fun i => response t (sampledVoter t) i - trajectory (t + N) i) -
        theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N)) =
      ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) := by
  let a : Coord → ℝ :=
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
  have htail :=
    theorem3ConcreteFiniteFieldProjection_tail_eq_base_add_sum_steps
      (M := M) (xstar := xstar) (trajectory := trajectory) (N := N) (n := n)
  have hdiff :
      (∑ t ∈ Finset.range n,
          finiteDot a
            (fun i => response t (sampledVoter t) i - trajectory (t + N) i)) -
        (∑ t ∈ Finset.range n,
          finiteDot a
            (fun i => trajectory (t + 1 + N) i - trajectory (t + N) i)) =
        ∑ t ∈ Finset.range n,
          finiteDot a
            (fun i => response t (sampledVoter t) i -
              trajectory (t + 1 + N) i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _ht
    unfold finiteDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  calc
    theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
          ∑ t ∈ Finset.range n,
            finiteDot
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
              (fun i => response t (sampledVoter t) i - trajectory (t + N) i) -
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N))
        =
          (∑ t ∈ Finset.range n,
              finiteDot a
                (fun i => response t (sampledVoter t) i -
                  trajectory (t + N) i)) -
            (∑ t ∈ Finset.range n,
              finiteDot a
                (fun i => trajectory (t + 1 + N) i -
                  trajectory (t + N) i)) := by
          rw [htail]
          dsimp [a]
          ring
    _ =
          ∑ t ∈ Finset.range n,
            finiteDot
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
              (fun i => response t (sampledVoter t) i -
                trajectory (t + 1 + N) i) := by
          simpa [a] using hdiff

theorem finiteDot_selectedRaw_residual_sum_nonpos_of_pointwise
    {Voter Coord : Type*} [Fintype Coord]
    (a : Coord → ℝ) (trajectory : ℕ → Coord → ℝ)
    (sampledVoter : ℕ → Voter) (response : ℕ → Voter → Coord → ℝ)
    (N : ℕ)
    (hresidual :
      ∀ t : ℕ,
        finiteDot a
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) ≤ 0) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot a
          (fun i => response t (sampledVoter t) i -
            trajectory (t + 1 + N) i) ≤ 0 := by
  intro n
  rw [← Finset.sum_const_zero]
  exact Finset.sum_le_sum fun t _ht => hresidual t

theorem finiteTheorem3DirectionalField_self_pos_of_ne_zero
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {weight : Voter → ℝ}
    {utilityGradient : Voter → (Coord → ℝ) → Coord → ℝ}
    {xstar : Coord → ℝ}
    (hne :
      finiteTheorem3DirectionalField weight utilityGradient xstar ≠
        fun _ => 0) :
    0 <
      finiteDot
        (finiteTheorem3DirectionalField weight utilityGradient xstar)
        (finiteTheorem3DirectionalField weight utilityGradient xstar) :=
  finiteDot_self_pos_of_ne_zero hne

theorem theorem3ConcreteFiniteFieldProjection_rawFieldStep_sub
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (xstar x : Coord → ℝ) (r : ℝ) :
    theorem3ConcreteFiniteFieldProjection M xstar
        (fun i =>
          x i +
            r * finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i) -
        theorem3ConcreteFiniteFieldProjection M xstar x =
      r *
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar) := by
  rw [theorem3ConcreteFiniteFieldProjection_step_sub]
  unfold finiteDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem theorem3ConcreteFiniteFieldProjection_rawFieldStep_sub_pos
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    {xstar x : Coord → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hne :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => 0) :
    0 <
      theorem3ConcreteFiniteFieldProjection M xstar
          (fun i =>
            x i +
              r * finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i) -
        theorem3ConcreteFiniteFieldProjection M xstar x := by
  rw [theorem3ConcreteFiniteFieldProjection_rawFieldStep_sub]
  exact mul_pos hr
    (finiteTheorem3DirectionalField_self_pos_of_ne_zero hne)

theorem theorem3ConcreteFiniteFieldProjection_projectedRawFieldStep_progress
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ}
    {xstar previous raw next : Coord → ℝ} {r : ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hr : 0 < r)
    (hraw :
      raw =
        fun i =>
          previous i +
            r * finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i)
    (hprevious : previous ∈ E.solutionSpace) :
    (1 / r) *
        finiteDot (fun i => next i - previous i)
          (fun i => next i - previous i) ≤
      theorem3ConcreteFiniteFieldProjection M xstar next -
        theorem3ConcreteFiniteFieldProjection M xstar previous := by
  have hprogress :=
    finiteDot_step_progress_of_l2_normProjection
      (E := E) hNorm hconv hproject hupdate hr hraw hprevious
  rw [theorem3ConcreteFiniteFieldProjection_step_sub]
  exact hprogress

theorem theorem3ConcreteFiniteFieldProjection_projectedRawFieldStep_nonneg
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hconv : Convex ℝ E.solutionSpace)
    {project : (Coord → ℝ) → Coord → ℝ}
    {xstar previous raw next : Coord → ℝ} {r : ℝ}
    (hproject : IsNormProjectionOnto E SourceNorm.l2 project)
    (hupdate : Algorithm1ProjectedUpdate project raw next)
    (hr : 0 < r)
    (hraw :
      raw =
        fun i =>
          previous i +
            r * finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i)
    (hprevious : previous ∈ E.solutionSpace) :
    0 ≤
      theorem3ConcreteFiniteFieldProjection M xstar next -
        theorem3ConcreteFiniteFieldProjection M xstar previous := by
  have hprogress :=
    theorem3ConcreteFiniteFieldProjection_projectedRawFieldStep_progress
      M hNorm hconv hproject hupdate hr hraw hprevious
  have hleft_nonneg :
      0 ≤
        (1 / r) *
          finiteDot (fun i => next i - previous i)
            (fun i => next i - previous i) := by
    exact mul_nonneg (div_nonneg zero_le_one (le_of_lt hr))
      (finiteDot_self_nonneg (fun i => next i - previous i))
  exact le_trans hleft_nonneg hprogress

/--
Finite-coordinate reading of `x_t -> x*` for the Theorem 3 row.  The generic
environment field `convergesToPoint` is intentionally abstract, so the
finite-coordinate paper-facing theorem uses this explicit coordinatewise
topological convergence predicate when it needs analytic consequences.
-/
def FiniteCoordinateILVTrajectoryConvergesTo
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ))
    (q : SourceNorm) (model : VoterResponseModel) (xstar : Coord → ℝ) : Prop :=
  ∀ i : Coord,
    Filter.Tendsto
      (fun n : ℕ => E.trajectory q model n i)
      Filter.atTop (nhds (xstar i))

/--
Source-level reading of the abstract paper convergence predicate in a
finite-coordinate environment.  The generic `ILVEnvironment.convergesToPoint`
field is intentionally abstract; this source record states that, in the concrete
finite-coordinate model, convergence to a point entails coordinatewise
topological convergence.
-/
structure FiniteCoordinateConvergenceSource
    {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  finite_coordinate_of_ilv_converges :
    ∀ {q : SourceNorm} {model : VoterResponseModel} {xstar : Coord → ℝ},
      ILVTrajectoryConvergesTo E q model xstar →
        FiniteCoordinateILVTrajectoryConvergesTo E q model xstar

theorem finiteDot_tendsto_of_coordinatewise
    {Coord : Type*} [Fintype Coord]
    (a : Coord → ℝ) {x : ℕ → Coord → ℝ} {xstar : Coord → ℝ}
    (hconv : ∀ i : Coord,
      Filter.Tendsto (fun n : ℕ => x n i) Filter.atTop (nhds (xstar i))) :
    Filter.Tendsto
      (fun n : ℕ => finiteDot a (x n))
      Filter.atTop (nhds (finiteDot a xstar)) := by
  unfold finiteDot
  exact
    tendsto_finset_sum Finset.univ
      (fun i _hi =>
        (tendsto_const_nhds.mul (hconv i)))

theorem finiteCoordinate_l2Sq_tendsto_zero_of_coordinatewise
    {Coord : Type*} [Fintype Coord]
    {x : ℕ → Coord → ℝ} {xstar : Coord → ℝ}
    (hconv : ∀ i : Coord,
      Filter.Tendsto (fun n : ℕ => x n i) Filter.atTop (nhds (xstar i))) :
    Filter.Tendsto
      (fun n : ℕ =>
        AppliedModelingLib.FiniteDimensionalNorms.l2Sq
          (fun i => x n i - xstar i))
      Filter.atTop (nhds 0) := by
  unfold AppliedModelingLib.FiniteDimensionalNorms.l2Sq
  have hsum :
      Filter.Tendsto
        (fun n : ℕ =>
          ∑ i : Coord, (x n i - xstar i) * (x n i - xstar i))
        Filter.atTop (nhds (∑ _i : Coord, (0 : ℝ))) :=
    tendsto_finset_sum Finset.univ
      (fun i _hi => by
        have hsub :
            Filter.Tendsto (fun n : ℕ => x n i - xstar i)
              Filter.atTop (nhds 0) := by
          have hconst :
              Filter.Tendsto (fun _n : ℕ => xstar i)
                Filter.atTop (nhds (xstar i)) :=
            tendsto_const_nhds
          simpa using (hconv i).sub hconst
        simpa [pow_two] using hsub.mul hsub)
  have hzero : (∑ _i : Coord, (0 : ℝ)) = 0 := by
    simp
  simpa [pow_two, hzero] using hsum

theorem finiteCoordinateDistance_l2_tendsto_zero_of_coordinatewise
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {x : ℕ → Coord → ℝ} {xstar : Coord → ℝ}
    (hconv : ∀ i : Coord,
      Filter.Tendsto (fun n : ℕ => x n i) Filter.atTop (nhds (xstar i))) :
    Filter.Tendsto
      (fun n : ℕ => finiteCoordinateDistance SourceNorm.l2 (x n) xstar)
      Filter.atTop (nhds 0) := by
  have hsumsq :=
    finiteCoordinate_l2Sq_tendsto_zero_of_coordinatewise hconv
  have hsqrt :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.sqrt
            (AppliedModelingLib.FiniteDimensionalNorms.l2Sq
              (fun i => x n i - xstar i)))
        Filter.atTop (nhds (Real.sqrt 0)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsumsq
  simpa [finiteCoordinateDistance, finiteCoordinateNorm,
    AppliedModelingLib.FiniteDimensionalNorms.l2] using hsqrt

theorem finiteCoordinateILVTrajectory_l2Distance_tendsto_zero_model
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {model : VoterResponseModel} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        model xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteCoordinateDistance SourceNorm.l2
          (E.trajectory SourceNorm.l2 model n) xstar)
      Filter.atTop (nhds 0) := by
  exact finiteCoordinateDistance_l2_tendsto_zero_of_coordinatewise hconv

theorem finiteCoordinateILVTrajectory_l2Distance_tendsto_zero
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteCoordinateDistance SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n) xstar)
      Filter.atTop (nhds 0) := by
  exact finiteCoordinateILVTrajectory_l2Distance_tendsto_zero_model hconv

theorem theorem3FiniteFieldProjection_tendsto_model
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {model : VoterResponseModel} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        model xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        theorem3FiniteFieldProjection E xstar
          (E.trajectory SourceNorm.l2 model n))
      Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar)) := by
  exact finiteDot_tendsto_of_coordinatewise
    (E.directionalField xstar) hconv

theorem theorem3FiniteFieldProjection_tendsto
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        theorem3FiniteFieldProjection E xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
      Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar)) := by
  exact theorem3FiniteFieldProjection_tendsto_model hconv

theorem theorem3FiniteFieldProjection_tendsto_model_nat_add
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {model : VoterResponseModel} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2 model xstar)
    (N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        theorem3FiniteFieldProjection E xstar
          (E.trajectory SourceNorm.l2 model (n + N)))
      Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar)) := by
  have hshift :
      Filter.Tendsto (fun n : ℕ => n + N) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro a
    exact Filter.eventually_atTop.2
      ⟨a, fun n hn => le_trans hn (Nat.le_add_right n N)⟩
  exact (theorem3FiniteFieldProjection_tendsto_model hconv).comp
    hshift

theorem theorem3FiniteFieldProjection_tendsto_nat_add
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)} {xstar : Coord → ℝ}
    (hconv :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar)
    (N : ℕ) :
    Filter.Tendsto
      (fun n : ℕ =>
        theorem3FiniteFieldProjection E xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N)))
      Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar)) := by
  exact theorem3FiniteFieldProjection_tendsto_model_nat_add hconv N

/--
Finite-coordinate analytic drift semantics for Theorem 3.  Compared with the
generic `Theorem3AnalyticDriftSemantics`, this fixes the scalar projection to
the dot product against the limiting field direction `G(x*)`.
-/
structure FiniteTheorem3AnalyticDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  radiusTail : (Coord → ℝ) → ℕ → ℝ
  radiusTail_partial_sums_tendsto_atTop :
    ∀ xstar : Coord → ℝ,
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radiusTail xstar t)
        Filter.atTop Filter.atTop
  projection_converges :
    ∀ {xstar : Coord → ℝ},
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
        Filter.Tendsto
          (fun n : ℕ =>
            theorem3FiniteFieldProjection E xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
          Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar))
  nonzero_drift_accumulates :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c baseValue, 0 < c ∧
                  ∀ n : ℕ,
                    baseValue +
                        c * (∑ t ∈ Finset.range n, radiusTail xstar t) ≤
                      theorem3FiniteFieldProjection E xstar
                        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n)

/--
One-step finite-coordinate drift semantics for Theorem 3.  This is closer to
the source proof than `FiniteTheorem3AnalyticDriftSemantics`: callers must prove
only the local projected progress inequality for the Model B trajectory, and
Lean telescopes it into the accumulated-drift contradiction.
-/
structure FiniteTheorem3OneStepDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  radiusTail : (Coord → ℝ) → ℕ → ℝ
  radiusTail_partial_sums_tendsto_atTop :
    ∀ xstar : Coord → ℝ,
      Filter.Tendsto
        (fun n : ℕ => ∑ t ∈ Finset.range n, radiusTail xstar t)
        Filter.atTop Filter.atTop
  projection_converges :
    ∀ {xstar : Coord → ℝ},
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
        Filter.Tendsto
          (fun n : ℕ =>
            theorem3FiniteFieldProjection E xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
          Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar))
  one_step_projection_progress :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c, 0 < c ∧
                  ∀ t : ℕ,
                    c * radiusTail xstar t ≤
                      theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1)) -
                        theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB t)

/--
Paper-radius version of the finite-coordinate Theorem 3 progress interface.
This removes one degree of freedom from `FiniteTheorem3OneStepDriftSemantics`:
the accumulated drift uses the source step size `r_t = r0 / t`, shifted to
Lean's zero-based indexing as `ilvRadius r0 (t + 1)`.
-/
structure FiniteTheorem3PaperRadiusDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  projection_converges :
    ∀ {xstar : Coord → ℝ},
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
        Filter.Tendsto
          (fun n : ℕ =>
            theorem3FiniteFieldProjection E xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
          Filter.atTop (nhds (theorem3FiniteFieldProjection E xstar xstar))
  one_step_projection_progress :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c, 0 < c ∧
                  ∀ t : ℕ,
                    c * ilvRadius r0 (t + 1) ≤
                      theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1)) -
                        theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB t)

/--
Paper-radius progress semantics after the trajectory convergence part has been
made explicit.  Unlike `FiniteTheorem3PaperRadiusDriftSemantics`, this record
does not store projection convergence as a field: for finite-coordinate
trajectories, Lean derives it from `FiniteCoordinateILVTrajectoryConvergesTo`
and the linear finite-dot projection.
-/
structure FiniteTheorem3PaperRadiusProgressSemantics
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  one_step_projection_progress :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c, 0 < c ∧
                  ∀ t : ℕ,
                    c * ilvRadius r0 (t + 1) ≤
                      theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + 1)) -
                      theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB t)

/--
Model A paper-radius progress semantics for the conjectural analogue of
Theorem 3.  The conclusion is identical to the Model B progress interface, but
the trajectory and response hypothesis are Model A.  Separate local lemmas
derive the needed one-step drift from first-order Model A maximization
hypotheses.
-/
structure FiniteTheorem3ModelAPaperRadiusProgressSemantics
    {Voter Coord : Type*} [Fintype Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  one_step_projection_progress :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              E.directionalField xstar ≠ E.zeroDirection →
                ∃ c, 0 < c ∧
                  ∀ t : ℕ,
                    c * ilvRadius r0 (t + 1) ≤
                      theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (t + 1)) -
                        theorem3FiniteFieldProjection E xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA t)

/--
Concrete finite-coordinate paper-radius progress semantics for Theorem 3.
Unlike `FiniteTheorem3PaperRadiusProgressSemantics`, the scalar projection and
nonzero premise are stated with the finite normalized-gradient field supplied by
`FiniteTheorem3DirectionalFieldModel`.  This removes the last ambiguity about
whether the progress boundary is talking about the paper's displayed
`G(x) = E_v[grad f_v(x) / ||grad f_v(x)||_2]` field.
-/
structure FiniteTheorem3ConcretePaperRadiusProgressSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  one_step_projection_progress :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ c, 0 < c ∧
                  ∀ t : ℕ,
                    c * ilvRadius r0 (t + 1) ≤
                      theorem3ConcreteFiniteFieldProjection M xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1)) -
                      theorem3ConcreteFiniteFieldProjection M xstar
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB t)

/--
Concrete finite-coordinate paper-radius escape semantics for Theorem 3.  This
is the intended remaining stochastic boundary: if a coordinatewise-convergent
Model B trajectory had a nonzero limiting normalized-gradient field, the
paper's random-increment and concentration argument should force accumulated
projected progress along that field.  Lean then derives the contradiction with
finite-coordinate convergence.
-/
structure FiniteTheorem3ConcretePaperRadiusEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  accumulated_projection_escape :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ c baseValue, 0 < c ∧
                  ∀ n : ℕ,
                    baseValue +
                        c * (∑ t ∈ Finset.range n,
                          ilvRadius r0 (t + 1)) ≤
                      theorem3ConcreteFiniteFieldProjection M xstar
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB n)

/--
Eventual concrete finite-coordinate paper-radius escape semantics for
Theorem 3.  This is the paper-faithful remaining stochastic boundary: after a
trajectory is close enough to a putative non-equilibrium limit, the paper's
Model B drift/concentration argument should force unbounded accumulated
projected progress along the concrete normalized-gradient field.
-/
structure FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  eventual_accumulated_projection_escape :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ N c baseValue, 0 < c ∧
                  ∀ n : ℕ,
                    baseValue +
                        c * (∑ t ∈ Finset.range n,
                          ilvRadius r0 (t + 1)) ≤
                      theorem3ConcreteFiniteFieldProjection M xstar
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N))

/--
Eventual concrete finite-coordinate paper-radius escape semantics for the
corrected Model A analogue of Theorem 3.  This is the same deterministic
divergence target as the Model B route, with the trajectory and response
hypotheses switched to `modelA`.
-/
structure FiniteTheorem3ModelAConcretePaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  eventual_accumulated_projection_escape :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ N c baseValue, 0 < c ∧
                  ∀ n : ℕ,
                    baseValue +
                        c * (∑ t ∈ Finset.range n,
                          ilvRadius r0 (t + 1)) ≤
                      theorem3ConcreteFiniteFieldProjection M xstar
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelA (n + N))

/--
Concrete finite-coordinate neighborhood-escape semantics for Theorem 3.  This is
the deterministic path property produced by the paper's Model B
drift/concentration argument: if a convergent-looking trajectory had nonzero
limiting normalized-gradient field, then for every sufficiently small ball and
every late time there would be a later iterate outside the ball.
-/
structure FiniteTheorem3ConcretePaperNeighborhoodEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  neighborhood_escape :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ δ, 0 < δ ∧
                  ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ < δ →
                    ∀ t : ℕ, ∃ τ : ℕ, t ≤ τ ∧
                      δ₂ <
                        finiteCoordinateDistance SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB τ)
                          xstar

/--
Coordinate-level escape semantics for Theorem 3.  This is a narrower geometric
target than full `L2` neighborhood escape: it asks the stochastic part of the
paper proof only to produce an arbitrarily late displacement in one concrete
coordinate.  Lean turns that into `L2` neighborhood escape using
`finiteCoordinateDistance_l2_coord_abs_le`.
-/
structure FiniteTheorem3ConcreteCoordinateEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  coordinate_escape :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ i δ, 0 < δ ∧
                  ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ < δ →
                    ∀ t : ℕ, ∃ τ : ℕ, t ≤ τ ∧
                      δ₂ <
                        |E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB τ i - xstar i|

/--
Coordinate-drift escape semantics for Theorem 3.  This isolates the remaining
stochastic/Hoeffding obligation after Lean has proved the analytic continuity
step: a persistent same-sign, bounded-magnitude coordinate drift must force
arbitrarily late displacement in that coordinate.
-/
structure FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  drift_coordinate_escape :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ δ, 0 < δ ∧
                    ∀ δ₂ : ℝ, 0 < δ₂ → δ₂ < δ →
                      ∀ t : ℕ, ∃ τ : ℕ, t ≤ τ ∧
                        δ₂ <
                          |E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB τ i - xstar i|

/--
Accumulated signed-coordinate escape semantics for Theorem 3.  This is closer
to the paper's Hoeffding layer than `FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics`:
after Lean identifies a persistent same-sign drift coordinate, the remaining
stochastic obligation is an accumulated lower bound on movement in that signed
coordinate.  Lean then derives arbitrarily late coordinate displacement.
-/
structure FiniteTheorem3ConcreteCoordinateAccumulationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  accumulated_signed_coordinate_escape :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ c baseValue, 0 < c ∧
                    ∀ n : ℕ,
                      baseValue +
                          c * (∑ t ∈ Finset.range n,
                            ilvRadius r0 (t + 1)) ≤
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                            xstar i *
                          (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N) i - xstar i)

/--
One-step signed-coordinate progress semantics for Theorem 3.  This is the
deterministic telescoping layer under the accumulated signed-coordinate boundary:
if the paper's Model B/concentration argument can supply a lower bound on every
signed coordinate increment after the fixed drift coordinate is identified, Lean
accumulates it using the source `r0 / t` radius schedule.
-/
structure FiniteTheorem3ConcreteCoordinateStepProgressSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  one_step_signed_coordinate_progress :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ c, 0 < c ∧
                    ∀ n : ℕ,
                      c * ilvRadius r0 (n + 1) ≤
                        (finiteTheorem3DirectionalField M.weight M.utilityGradient
                            xstar i *
                          (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + 1 + N) i - xstar i)) -
                        (finiteTheorem3DirectionalField M.weight M.utilityGradient
                            xstar i *
                          (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N) i - xstar i))

/--
Expected-drift plus fluctuation-control semantics for Theorem 3.  This is the
non-probabilistic shell of Appendix C.6: the paper's Hoeffding argument should
provide an expected signed coordinate displacement with harmonic positive drift
and a pathwise fluctuation bound along the realized trajectory.  Lean then
absorbs the bounded fluctuation into the accumulated signed-coordinate route.
-/
structure FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  expected_minus_fluctuation_signed_coordinate_escape :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ c expectedBase fluctuationBound
                    : ℝ,
                    ∃ expectedSignedDisplacement : ℕ → ℝ,
                    0 < c ∧
                      (∀ n : ℕ,
                        expectedBase +
                            c * (∑ t ∈ Finset.range n,
                              ilvRadius r0 (t + 1)) ≤
                          expectedSignedDisplacement n) ∧
                      (∀ n : ℕ,
                        expectedSignedDisplacement n - fluctuationBound ≤
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (n + N) i -
                              xstar i))

/--
Hoeffding-shell semantics for Theorem 3.  Compared with
`FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics`, this no longer
assumes the expected harmonic drift lower bound: Lean derives it from the
fixed-sign coordinate drift.  The remaining source obligation is the
concentration/fluctuation comparison between realized accumulated movement and
the expected signed coordinate sum.
-/
structure FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  coordinate_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ fluctuationBound : ℝ,
                    ∀ n : ℕ,
                      (∑ t ∈ Finset.range n,
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (ilvRadius r0 (t + 1) *
                              finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N)) i)) -
                          fluctuationBound ≤
                        finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar i *
                          (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N) i -
                            xstar i)

/--
Eventual Hoeffding-shell semantics for Theorem 3.  This is weaker than a
uniform all-time fluctuation bound: once the fixed drift coordinate has been
identified, the concentration layer only has to control the realized accumulated
coordinate movement by the expected signed coordinate sum after some tail time.
Lean combines that eventual control with harmonic divergence to produce the
paper's arbitrarily late coordinate escape.
-/
structure FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  coordinate_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                    ∀ n : ℕ, T ≤ n →
                      (∑ t ∈ Finset.range n,
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (ilvRadius r0 (t + 1) *
                              finiteTheorem3DirectionalField M.weight
                                M.utilityGradient
                                (E.trajectory SourceNorm.l2
                                  VoterResponseModel.modelB (t + N)) i)) -
                          fluctuationBound ≤
                        finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar i *
                          (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N) i -
                            xstar i)

/--
Sampled raw-increment version of the Theorem 3 Hoeffding shell.  This exposes
the C.6 source shape directly: a sampled voter path supplies raw Model B
responses, actual coordinate increments agree with the selected raw response
increments, and concentration controls the gap between realized accumulated
signed increments and their finite-voter expectation.

The exact increment-equality field is deliberately visible because the paper's
text expands the trajectory as an unprojected sum of `Δx_k`; if projection can
change the coordinate, this is precisely the source-side condition that must be
justified or replaced by a projected analogue.
-/
structure FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_raw_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ sampledVoter : ℕ → Voter,
                  ∃ response : ℕ → Voter → Coord → ℝ,
                    (∀ t voter,
                      ModelBFiniteResponseAt SourceNorm.l2
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + N))
                        (ilvRadius r0 (t + 1))
                        (M.utilityGradient voter
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N)))
                        (response t voter)) ∧
                    (∀ t,
                      E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + 1 + N) i -
                        E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + N) i =
                        response t (sampledVoter t) i -
                          E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N) i) ∧
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (∑ t ∈ Finset.range n,
                            ∑ voter : Voter,
                              M.weight voter *
                                (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar i *
                                  (response t voter i -
                                    E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N) i))) -
                            fluctuationBound ≤
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N i - xstar i) +
                            ∑ t ∈ Finset.range n,
                              finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar i *
                                (response t (sampledVoter t) i -
                                  E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N) i)

/--
Projected sampled-raw version of the Theorem 3 Hoeffding shell.  This avoids
assuming that projected trajectory increments exactly equal selected raw
response increments.  Instead it exposes two source-side obligations: a
Hoeffding/concentration lower bound for selected raw increments and a bounded
projection-slack lower bound comparing accumulated selected raw increments with
actual projected trajectory movement in the drift coordinate.
-/
structure FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_projected_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {i : Coord} {N : ℕ} {ε₂ : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              0 < ε₂ →
                (∀ n : ℕ,
                  ε₂ <
                      |finiteTheorem3DirectionalField M.weight M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)) i| ∧
                    0 <
                      finiteTheorem3DirectionalField M.weight M.utilityGradient
                          xstar i *
                        finiteTheorem3DirectionalField M.weight M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)) i) →
                  ∃ sampledVoter : ℕ → Voter,
                  ∃ response : ℕ → Voter → Coord → ℝ,
                    (∀ t voter,
                      ModelBFiniteResponseAt SourceNorm.l2
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + N))
                        (ilvRadius r0 (t + 1))
                        (M.utilityGradient voter
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N)))
                        (response t voter)) ∧
                    ∃ concentrationBound projectionSlackBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        ((∑ t ∈ Finset.range n,
                            ∑ voter : Voter,
                              M.weight voter *
                                (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar i *
                                  (response t voter i -
                                    E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N) i))) -
                            concentrationBound ≤
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N i - xstar i) +
                            ∑ t ∈ Finset.range n,
                              finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar i *
                                (response t (sampledVoter t) i -
                                  E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N) i)) ∧
                        (finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N i - xstar i) +
                            ∑ t ∈ Finset.range n,
                              finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar i *
                                (response t (sampledVoter t) i -
                                  E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N) i)) -
                            projectionSlackBound ≤
                          finiteTheorem3DirectionalField M.weight
                              M.utilityGradient xstar i *
                            (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (n + N) i - xstar i)

/--
Finite-dot eventual Hoeffding shell for Theorem 3.  This is the scalar
projection analogue of the coordinate Hoeffding shell and lines up with the
existing finite `L2` projection-progress route.  The remaining source work is
split into:

* eventual positive scalar drift
  `<G(x*), G(x_t)> >= c > 0` along a tail, and
* a pathwise fluctuation/concentration bound comparing accumulated expected
  scalar drift with the actual scalar projection of the trajectory.
-/
structure FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  eventual_finiteDot_drift :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ N c, 0 < c ∧
                  ∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))
  finiteDot_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (∑ t ∈ Finset.range n,
                            ilvRadius r0 (t + 1) *
                              finiteDot
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar)
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N))

/--
Model A finite-dot eventual Hoeffding shell for the corrected post-Theorem-3
analogue.  It has the same scalar shape as the Model B shell, but every
trajectory and response hypothesis is `modelA`.  The first-order Model A
analysis can be used to prove the fluctuation-control field below once the
source trace has been instantiated.
-/
structure FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  eventual_finiteDot_drift :
    ∀ {xstar : Coord → ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                ∃ N c, 0 < c ∧
                  ∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (n + N)))
  finiteDot_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (∑ t ∈ Finset.range n,
                            ilvRadius r0 (t + 1) *
                              finiteDot
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar)
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelA (t + N)))) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelA (n + N))

/--
Model A finite-dot Hoeffding shell with analytic drift derived in Lean.  This is
the corrected analogue of the Model B `FiniteDotHoeffdingShellSemantics`: source
work only has to supply the eventual fluctuation comparison, while Lean derives
the positive scalar drift from convergence and continuity of the normalized
field.
-/
structure FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  finiteDot_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (∑ t ∈ Finset.range n,
                            ilvRadius r0 (t + 1) *
                              finiteDot
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar)
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelA (t + N)))) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelA (n + N))

/--
Model A harmonic Hoeffding shell for the corrected first-order analogue of
Theorem 3.  Model A does not have the exact Model B identity
`E[Δx_t] = r_t G(x_t)`.  The first-order proof only needs the weaker, source
faithful consequence: once `<G(x*), G(x_t)> >= c` on a tail, the realized scalar
projection eventually dominates `(c/2) * sum r_t` up to a finite fluctuation
constant.
-/
structure FiniteTheorem3ModelAConcreteHarmonicEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  harmonic_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (c / 2) *
                            (∑ t ∈ Finset.range n,
                              ilvRadius r0 (t + 1)) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelA (n + N))

/--
Global-tail Model A harmonic Hoeffding shell.  This is the source-faithful
version for Algorithm 2: after shifting to a tail beginning at `N`, the step
size remains the original `r0 / (t + N + 1)` rather than resetting to
`r0 / (t + 1)`.
-/
structure FiniteTheorem3ModelAConcreteGlobalHarmonicEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  global_harmonic_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelA →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelA xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelA (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (c / 2) *
                            (∑ t ∈ Finset.range n,
                              ilvTailRadius r0 N t) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelA (n + N))

/--
Finite-dot Hoeffding shell with analytic drift derived in Lean.  Compared with
`FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics`, this record
does not ask the source model to supply eventual positive scalar drift.  The
conversion below derives that drift from coordinate-continuity of the concrete
field and convergence of the trajectory.
-/
structure FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  finiteDot_fluctuation_eventual_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                      ∀ n : ℕ, T ≤ n →
                        (∑ t ∈ Finset.range n,
                            ilvRadius r0 (t + 1) *
                              finiteDot
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient xstar)
                                (finiteTheorem3DirectionalField M.weight
                                  M.utilityGradient
                                  (E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + N)))) -
                            fluctuationBound ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (n + N))

/--
Raw Model B response version of the finite-dot Hoeffding shell.  The source
obligation is now phrased over finite-voter raw response increments; Lean
converts their expectation to the scalar `r * <G(x*), G(x_t)>` field term.
-/
structure FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_finiteDot_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                        ∀ n : ℕ, T ≤ n →
                          (∑ t ∈ Finset.range n,
                              ∑ voter : Voter,
                                M.weight voter *
                                  finiteDot
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)
                                    (fun i =>
                                      response t voter i -
                                        E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB (t + N) i)) -
                              fluctuationBound ≤
                            theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (n + N))

/--
Exact sampled-raw finite-dot shell.  This is the zero-projection-slack special
case of the projected finite-dot source target: selected raw responses exactly
match the actual trajectory increments, and concentration is phrased against
those selected raw finite-dot increments.
-/
structure FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_exact_finiteDot_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ sampledVoter : ℕ → Voter,
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      (∀ t i,
                        E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N) i -
                          E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N) i =
                          response t (sampledVoter t) i -
                            E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N) i) ∧
                      ∃ fluctuationBound : ℝ, ∃ T : ℕ,
                        ∀ n : ℕ, T ≤ n →
                          (∑ t ∈ Finset.range n,
                              ∑ voter : Voter,
                                M.weight voter *
                                  finiteDot
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)
                                    (fun i =>
                                      response t voter i -
                                        E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB (t + N) i)) -
                              fluctuationBound ≤
                            theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N) +
                              ∑ t ∈ Finset.range n,
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (fun i =>
                                    response t (sampledVoter t) i -
                                      E.trajectory SourceNorm.l2
                                        VoterResponseModel.modelB (t + N) i)

/--
Sampled raw finite-dot shell with explicit projection slack.  This is the
finite-dot analogue of `FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics`:
concentration controls selected raw Model B increments, and a separate slack
bound compares those accumulated selected raw increments to the actual scalar
projection of the projected trajectory.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_projected_finiteDot_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ sampledVoter : ℕ → Voter,
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∃ concentrationBound projectionSlackBound : ℝ, ∃ T : ℕ,
                        ∀ n : ℕ, T ≤ n →
                          ((∑ t ∈ Finset.range n,
                              ∑ voter : Voter,
                                M.weight voter *
                                  finiteDot
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)
                                    (fun i =>
                                      response t voter i -
                                        E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB (t + N) i)) -
                              concentrationBound ≤
                            theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N) +
                              ∑ t ∈ Finset.range n,
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (fun i =>
                                    response t (sampledVoter t) i -
                                      E.trajectory SourceNorm.l2
                                        VoterResponseModel.modelB (t + N) i)) ∧
                          theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N) +
                              ∑ t ∈ Finset.range n,
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (fun i =>
                                    response t (sampledVoter t) i -
                                      E.trajectory SourceNorm.l2
                                        VoterResponseModel.modelB (t + N) i) ≤
                          theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (n + N)) +
                              projectionSlackBound

/--
Residual form of the projected sampled-raw finite-dot shell.  This is a sharper
presentation of the same projection-sensitive boundary: concentration controls
selected raw increments, while the projection loss is stated as a bound on the
cumulative finite-dot residual between each selected raw response and the
projected next iterate.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_projected_residual_finiteDot_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ sampledVoter : ℕ → Voter,
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∃ concentrationBound residualBound : ℝ, ∃ T : ℕ,
                        ∀ n : ℕ, T ≤ n →
                          ((∑ t ∈ Finset.range n,
                              ∑ voter : Voter,
                                M.weight voter *
                                  finiteDot
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)
                                    (fun i =>
                                      response t voter i -
                                        E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB (t + N) i)) -
                              concentrationBound ≤
                            theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N) +
                              ∑ t ∈ Finset.range n,
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (fun i =>
                                    response t (sampledVoter t) i -
                                      E.trajectory SourceNorm.l2
                                        VoterResponseModel.modelB (t + N) i)) ∧
                          ∑ t ∈ Finset.range n,
                            finiteDot
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar)
                              (fun i =>
                                response t (sampledVoter t) i -
                                  E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + 1 + N) i) ≤
                            residualBound

/--
Projected-trace form of the finite-dot Theorem 3 shell.  Compared with
`FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics`, this does
not ask the source layer for a residual bound directly.  Instead it asks for the
paper's projected Algorithm 1 trace: selected raw responses, a finite `L2`
norm-minimizing projection onto a convex feasible set, projected updates, and
the geometric fact that the fixed `G(x*)` direction remains feasible from the
projected iterates.  Lean derives the cumulative residual bound from the
projection normal-cone inequality.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  sampled_projected_trace_finiteDot_fluctuation_control :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ sampledVoter : ℕ → Voter,
                    ∃ response : ℕ → Voter → Coord → ℝ,
                    ∃ raw : ℕ → Coord → ℝ,
                    ∃ project : (Coord → ℝ) → Coord → ℝ,
                      UsesFiniteCoordinateNormDistance E ∧
                      Convex ℝ E.solutionSpace ∧
                      IsNormProjectionOnto E SourceNorm.l2 project ∧
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                      (∀ t : ℕ,
                        Algorithm1ProjectedUpdate project (raw t)
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))) ∧
                      (∀ t : ℕ,
                        FiniteFeasibleDirectionAt E.solutionSpace
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar)) ∧
                      ∃ concentrationBound : ℝ, ∃ T : ℕ,
                        ∀ n : ℕ, T ≤ n →
                          (∑ t ∈ Finset.range n,
                              ∑ voter : Voter,
                                M.weight voter *
                                  finiteDot
                                    (finiteTheorem3DirectionalField M.weight
                                      M.utilityGradient xstar)
                                    (fun i =>
                                      response t voter i -
                                        E.trajectory SourceNorm.l2
                                          VoterResponseModel.modelB (t + N) i)) -
                              concentrationBound ≤
                            theorem3ConcreteFiniteFieldProjection M xstar
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB N) +
                              ∑ t ∈ Finset.range n,
                                finiteDot
                                  (finiteTheorem3DirectionalField M.weight
                                    M.utilityGradient xstar)
                                  (fun i =>
                                    response t (sampledVoter t) i -
                                      E.trajectory SourceNorm.l2
                                        VoterResponseModel.modelB (t + N) i)

/--
Pathwise projected-trace certificate for the finite-dot Theorem 3 route.

The important alignment is explicit in this record: the same sampled voter
stream supplies the selected raw responses, the projected updates of the fixed
trajectory, and the finite-dot concentration bound.  This avoids treating the
trajectory/sample-path identification as an implicit property of
`ILVEnvironment.trajectory`.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSample
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (r0 : ℝ) (xstar : Coord → ℝ) (N : ℕ)
    (sampledVoter : ℕ → Voter) where
  response : ℕ → Voter → Coord → ℝ
  raw : ℕ → Coord → ℝ
  project : (Coord → ℝ) → Coord → ℝ
  normDistance : UsesFiniteCoordinateNormDistance E
  convex_solutionSpace : Convex ℝ E.solutionSpace
  normProjection : IsNormProjectionOnto E SourceNorm.l2 project
  raw_response :
    ∀ t voter,
      ModelBFiniteResponseAt SourceNorm.l2
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
        (ilvRadius r0 (t + 1))
        (M.utilityGradient voter
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
        (response t voter)
  selected_raw :
    ∀ t : ℕ, raw t = response t (sampledVoter t)
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))
  feasible_direction :
    ∀ t : ℕ,
      FiniteFeasibleDirectionAt E.solutionSpace
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
  concentrationBound : ℝ
  concentration_time : ℕ
  concentration_control :
    ∀ n : ℕ, concentration_time ≤ n →
      (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter *
              finiteDot
                (finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar)
                (fun i =>
                  response t voter i -
                    E.trajectory SourceNorm.l2
                      VoterResponseModel.modelB (t + N) i)) -
          concentrationBound ≤
        theorem3ConcreteFiniteFieldProjection M xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
          ∑ t ∈ Finset.range n,
            finiteDot
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                xstar)
              (fun i =>
                response t (sampledVoter t) i -
                  E.trajectory SourceNorm.l2
                    VoterResponseModel.modelB (t + N) i)

theorem FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSample.residual_sum_nonpos
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    {r0 : ℝ} {xstar : Coord → ℝ} {N : ℕ}
    {sampledVoter : ℕ → Voter}
    (P :
      FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSample
        M r0 xstar N sampledVoter) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (fun i =>
            P.response t (sampledVoter t) i -
              E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                (t + 1 + N) i) ≤ 0 := by
  intro n
  let trajectory : ℕ → Coord → ℝ :=
    fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
  let direction : Coord → ℝ :=
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
  have hnormal :
      ∀ t : ℕ,
        FiniteProjectionNormalConeAt E.solutionSpace (P.raw t)
          (trajectory (t + 1 + N)) := by
    intro t
    exact
      finiteProjectionNormalConeAt_of_l2_normProjection
        (E := E) P.normDistance P.convex_solutionSpace P.normProjection
        (P.projected_update t)
  have hresidual_raw :
      ∑ t ∈ Finset.range n,
        finiteDot direction
          (fun i => P.raw t i - trajectory (t + 1 + N) i) ≤ 0 := by
    exact
      finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
        (X := E.solutionSpace)
        (raw := P.raw)
        (next := fun t => trajectory (t + 1 + N))
        (direction := direction)
        hnormal
        (by
          intro t
          simpa [trajectory, direction] using P.feasible_direction t)
        n
  have hresidual_selected :
      (∑ t ∈ Finset.range n,
        finiteDot direction
          (fun i =>
            P.response t (sampledVoter t) i -
              trajectory (t + 1 + N) i)) =
        ∑ t ∈ Finset.range n,
          finiteDot direction
            (fun i => P.raw t i - trajectory (t + 1 + N) i) := by
    apply Finset.sum_congr rfl
    intro t _ht
    rw [← P.selected_raw t]
  calc
    ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (fun i =>
            P.response t (sampledVoter t) i -
              E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                (t + 1 + N) i)
        =
          ∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i =>
                P.response t (sampledVoter t) i -
                  trajectory (t + 1 + N) i) := by
            rfl
    _ =
          ∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i => P.raw t i - trajectory (t + 1 + N) i) :=
            hresidual_selected
    _ ≤ 0 := hresidual_raw

/--
Almost-sure trace skeleton for the projected-trace Theorem 3 route.  This is
weaker and more paper-faithful than a universal deterministic skeleton: the
selected raw/projected trace facts only need to hold on an almost-sure set of
sampled voter streams under the explicit iid weighted-voter product law.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceAETraceSkeleton
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  ae_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvRadius r0 (t + 1))
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∀ᵐ sampledVoter
                          ∂theorem3FiniteWeightedVoterSequenceMeasure
                            M.weight M.weight_nonneg M.weight_sum,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          Convex ℝ E.solutionSpace ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar))

/--
Pathwise source-semantics version of the projected-trace finite-dot Theorem 3
boundary.  The existential stream returned here is the stream that generates
the selected raw/projected trajectory and already satisfies the concentration
event needed downstream.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  pathwise_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    Nonempty
                      (Σ sampledVoter : ℕ → Voter,
                        FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSample
                          M r0 xstar N sampledVoter)

noncomputable def
    FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics.toProjectedTraceHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics M) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_trace_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.pathwise_projected_trace
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨⟨sampledVoter, P⟩⟩
    exact
      ⟨sampledVoter, P.response, P.raw, P.project, P.normDistance,
        P.convex_solutionSpace, P.normProjection, P.raw_response,
        P.selected_raw, P.projected_update, P.feasible_direction,
        P.concentrationBound, P.concentration_time, P.concentration_control⟩

noncomputable def
    FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics.toProjectedResidualHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics M) :
    FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_residual_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.pathwise_projected_trace
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨⟨sampledVoter, P⟩⟩
    refine
      ⟨sampledVoter, P.response, P.raw_response,
        P.concentrationBound, 0, P.concentration_time, ?_⟩
    intro n hn
    exact
      ⟨P.concentration_control n hn,
        P.residual_sum_nonpos n⟩

/--
Concrete coordinatewise continuity for the finite normalized-gradient field in
Theorem 3.  This is the source continuity assumption in the form needed by the
Appendix C.6 coordinate drift argument.
-/
def FiniteTheorem3DirectionalFieldCoordinateContinuity
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) : Prop :=
  ∀ xstar i ε, 0 < ε →
    ∃ δ, 0 < δ ∧
      ∀ x : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
          |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
            finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i| < ε

/--
Appendix C.6 continuity step: if `G(x*)` is nonzero, then some coordinate keeps
the same sign and has magnitude bounded below throughout a small `L2` ball.
-/
theorem finiteTheorem3DirectionalField_exists_local_coordinate_drift
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {xstar : Coord → ℝ}
    (hne :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ∃ i δ ε₂, 0 < δ ∧ 0 < ε₂ ∧
      ∀ x : Coord → ℝ,
        finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
          ε₂ < |finiteTheorem3DirectionalField M.weight M.utilityGradient x i| ∧
            0 <
              finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i *
                finiteTheorem3DirectionalField M.weight M.utilityGradient x i := by
  rcases exists_coord_ne_zero_of_ne_zero hne with ⟨i, hi⟩
  let a : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
  have ha_ne : a ≠ 0 := by
    simpa [a] using hi
  have ha_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
  have hhalf_pos : 0 < |a| / 2 := by linarith
  rcases hcont xstar i (|a| / 2) hhalf_pos with ⟨δ, hδpos, hδ⟩
  refine ⟨i, δ, |a| / 2, hδpos, hhalf_pos, ?_⟩
  intro x hx
  let b : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient x i
  have hclose : |b - a| < |a| / 2 := by
    simpa [a, b] using hδ x hx
  have hmag : |a| / 2 < |b| := by
    have htri : |a| ≤ |b - a| + |b| := by
      calc
        |a| = |-(b - a) + b| := by ring_nf
        _ ≤ |-(b - a)| + |b| := abs_add_le _ _
        _ = |b - a| + |b| := by
          rw [abs_neg, abs_sub_comm]
    linarith
  have hsame : 0 < a * b := by
    by_cases ha_pos : 0 < a
    · have habs : |a| = a := abs_of_pos ha_pos
      have hbounds := abs_lt.mp hclose
      have hbpos : 0 < b := by
        rw [habs] at hbounds
        linarith
      exact mul_pos ha_pos hbpos
    · have ha_nonpos : a ≤ 0 := not_lt.mp ha_pos
      have ha_neg : a < 0 := lt_of_le_of_ne ha_nonpos ha_ne
      have habs : |a| = -a := abs_of_neg ha_neg
      have hbounds := abs_lt.mp hclose
      have hbneg : b < 0 := by
        rw [habs] at hbounds
        linarith
      exact mul_pos_of_neg_of_neg ha_neg hbneg
  exact ⟨by simpa [b] using hmag, by simpa [a, b] using hsame⟩

/--
Trajectory form of the Appendix C.6 continuity step.  Once the trajectory
converges to a non-directional-equilibrium candidate, all sufficiently late
iterates share the fixed-sign, bounded-magnitude coordinate guaranteed above.
-/
theorem finiteTheorem3DirectionalField_eventual_coordinate_drift_of_converges
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar)
    (hne :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ∃ i N ε₂, 0 < ε₂ ∧
      ∀ n : ℕ,
        ε₂ <
            |finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N)) i| ∧
          0 <
            finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i *
              finiteTheorem3DirectionalField M.weight M.utilityGradient
                (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N)) i := by
  rcases finiteTheorem3DirectionalField_exists_local_coordinate_drift
      M hcont hne with
    ⟨i, δ, ε₂, hδpos, hε₂pos, hlocal⟩
  have hdist_tendsto :=
    finiteCoordinateILVTrajectory_l2Distance_tendsto_zero hConverges
  have heventually_close :
      ∀ᶠ n in Filter.atTop,
        finiteCoordinateDistance SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n)
          xstar < δ :=
    hdist_tendsto.eventually (eventually_lt_nhds hδpos)
  rcases Filter.eventually_atTop.1 heventually_close with ⟨N, hN⟩
  refine ⟨i, N, ε₂, hε₂pos, ?_⟩
  intro n
  exact hlocal
    (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N))
    (hN (n + N) (Nat.le_add_left N n))

/--
Coordinatewise convergence of the concrete finite Theorem 3 field along a
convergent trajectory, using the proof-facing coordinate-continuity interface.
This model-parameterized form is used by the Model A analogue and the original
Model B theorem route.
-/
theorem finiteTheorem3DirectionalField_coordinate_tendsto_of_converges_model
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {model : VoterResponseModel}
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        model xstar)
    (i : Coord) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteTheorem3DirectionalField M.weight M.utilityGradient
          (E.trajectory SourceNorm.l2 model n) i)
      Filter.atTop
      (nhds
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  rcases hcont xstar i ε hε with ⟨δ, hδpos, hδ⟩
  have hdist_tendsto :=
    finiteCoordinateILVTrajectory_l2Distance_tendsto_zero_model hConverges
  have heventually_close :
      ∀ᶠ n in Filter.atTop,
        finiteCoordinateDistance SourceNorm.l2
          (E.trajectory SourceNorm.l2 model n)
          xstar < δ :=
    hdist_tendsto.eventually (eventually_lt_nhds hδpos)
  filter_upwards [heventually_close] with n hn
  simpa [Real.dist_eq] using
    hδ (E.trajectory SourceNorm.l2 model n) hn

theorem finiteTheorem3DirectionalField_coordinate_tendsto_of_converges
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar)
    (i : Coord) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteTheorem3DirectionalField M.weight M.utilityGradient
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n) i)
      Filter.atTop
      (nhds
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i)) := by
  exact
    finiteTheorem3DirectionalField_coordinate_tendsto_of_converges_model
      M hcont hConverges i

/--
Finite-dot convergence of the concrete Theorem 3 field along a convergent
trajectory.
-/
theorem finiteTheorem3DirectionalField_finiteDot_tendsto_of_converges_model
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {model : VoterResponseModel}
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        model xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (finiteTheorem3DirectionalField M.weight M.utilityGradient
            (E.trajectory SourceNorm.l2 model n)))
      Filter.atTop
      (nhds
        (finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar))) := by
  exact
    finiteDot_tendsto_of_coordinatewise
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
      (fun i =>
        finiteTheorem3DirectionalField_coordinate_tendsto_of_converges_model
          M hcont hConverges i)

theorem finiteTheorem3DirectionalField_finiteDot_tendsto_of_converges
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    Filter.Tendsto
      (fun n : ℕ =>
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (finiteTheorem3DirectionalField M.weight M.utilityGradient
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n)))
      Filter.atTop
      (nhds
        (finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar))) := by
  exact
    finiteTheorem3DirectionalField_finiteDot_tendsto_of_converges_model
      M hcont hConverges

/--
Finite-dot version of the local positive-drift step: near a nonzero limiting
field, the scalar product `<G(x*), G(x_t)>` is eventually uniformly positive.
-/
theorem finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges_model
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {model : VoterResponseModel}
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        model xstar)
    (hne :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ∃ N c, 0 < c ∧
      ∀ n : ℕ,
        c ≤
          finiteDot
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
            (finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 model (n + N))) := by
  let a : Coord → ℝ :=
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
  let L : ℝ := finiteDot a a
  have hLpos : 0 < L := by
    simpa [a, L] using
      finiteTheorem3DirectionalField_self_pos_of_ne_zero
        (weight := M.weight) (utilityGradient := M.utilityGradient)
        (xstar := xstar) hne
  let c : ℝ := L / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith
  have hc_lt_L : c < L := by
    dsimp [c]
    linarith
  have hdot_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          finiteDot a
            (finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 model n)))
        Filter.atTop (nhds L) := by
    simpa [a, L] using
      finiteTheorem3DirectionalField_finiteDot_tendsto_of_converges_model
        M hcont hConverges
  have heventually_pos :
      ∀ᶠ n in Filter.atTop,
        c <
          finiteDot a
            (finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 model n)) :=
    hdot_tendsto.eventually (Ioi_mem_nhds hc_lt_L)
  rcases Filter.eventually_atTop.1 heventually_pos with ⟨N, hN⟩
  refine ⟨N, c, hc, ?_⟩
  intro n
  exact le_of_lt (hN (n + N) (Nat.le_add_left N n))

theorem finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar)
    (hne :
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) :
    ∃ N c, 0 < c ∧
      ∀ n : ℕ,
        c ≤
          finiteDot
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
            (finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N))) := by
  exact
    finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges_model
      M hcont hConverges hne

/--
Pathwise projected-trace certificate with the original global Algorithm 1
radius on every tail.  At tail index `t` after a shift `N`, the source update
uses `ilvTailRadius r0 N t = r0 / (t + N + 1)`.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSample
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (r0 : ℝ) (xstar : Coord → ℝ) (N : ℕ)
    (sampledVoter : ℕ → Voter) where
  response : ℕ → Voter → Coord → ℝ
  raw : ℕ → Coord → ℝ
  project : (Coord → ℝ) → Coord → ℝ
  normDistance : UsesFiniteCoordinateNormDistance E
  convex_solutionSpace : Convex ℝ E.solutionSpace
  normProjection : IsNormProjectionOnto E SourceNorm.l2 project
  raw_response :
    ∀ t voter,
      ModelBFiniteResponseAt SourceNorm.l2
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N))
        (ilvTailRadius r0 N t)
        (M.utilityGradient voter
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)))
        (response t voter)
  selected_raw :
    ∀ t : ℕ, raw t = response t (sampledVoter t)
  projected_update :
    ∀ t : ℕ,
      Algorithm1ProjectedUpdate project (raw t)
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))
  feasible_direction :
    ∀ t : ℕ,
      FiniteFeasibleDirectionAt E.solutionSpace
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
  concentrationBound : ℝ
  concentration_time : ℕ
  concentration_control :
    ∀ n : ℕ, concentration_time ≤ n →
      (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter *
              finiteDot
                (finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar)
                (fun i =>
                  response t voter i -
                    E.trajectory SourceNorm.l2
                      VoterResponseModel.modelB (t + N) i)) -
          concentrationBound ≤
        theorem3ConcreteFiniteFieldProjection M xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N) +
          ∑ t ∈ Finset.range n,
            finiteDot
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                xstar)
              (fun i =>
                response t (sampledVoter t) i -
                  E.trajectory SourceNorm.l2
                    VoterResponseModel.modelB (t + N) i)

theorem
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSample.residual_sum_nonpos
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    {r0 : ℝ} {xstar : Coord → ℝ} {N : ℕ}
    {sampledVoter : ℕ → Voter}
    (P :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSample
        M r0 xstar N sampledVoter) :
    ∀ n : ℕ,
      ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (fun i =>
            P.response t (sampledVoter t) i -
              E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                (t + 1 + N) i) ≤ 0 := by
  intro n
  let trajectory : ℕ → Coord → ℝ :=
    fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
  let direction : Coord → ℝ :=
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
  have hnormal :
      ∀ t : ℕ,
        FiniteProjectionNormalConeAt E.solutionSpace (P.raw t)
          (trajectory (t + 1 + N)) := by
    intro t
    exact
      finiteProjectionNormalConeAt_of_l2_normProjection
        (E := E) P.normDistance P.convex_solutionSpace P.normProjection
        (P.projected_update t)
  have hresidual_raw :
      ∑ t ∈ Finset.range n,
        finiteDot direction
          (fun i => P.raw t i - trajectory (t + 1 + N) i) ≤ 0 := by
    exact
      finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
        (X := E.solutionSpace)
        (raw := P.raw)
        (next := fun t => trajectory (t + 1 + N))
        (direction := direction)
        hnormal
        (by
          intro t
          simpa [trajectory, direction] using P.feasible_direction t)
        n
  have hresidual_selected :
      (∑ t ∈ Finset.range n,
        finiteDot direction
          (fun i =>
            P.response t (sampledVoter t) i -
              trajectory (t + 1 + N) i)) =
        ∑ t ∈ Finset.range n,
          finiteDot direction
            (fun i => P.raw t i - trajectory (t + 1 + N) i) := by
    apply Finset.sum_congr rfl
    intro t _ht
    rw [← P.selected_raw t]
  calc
    ∑ t ∈ Finset.range n,
        finiteDot
          (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
          (fun i =>
            P.response t (sampledVoter t) i -
              E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                (t + 1 + N) i)
        =
          ∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i =>
                P.response t (sampledVoter t) i -
                  trajectory (t + 1 + N) i) := by
            rfl
    _ =
          ∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i => P.raw t i - trajectory (t + 1 + N) i) :=
            hresidual_selected
    _ ≤ 0 := hresidual_raw

/--
Corrected pathwise source-semantics version of the projected-trace Theorem 3
boundary.  This uses the global Algorithm 1 tail radii, rather than restarting
the harmonic schedule after the tail index `N`.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  pathwise_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    Nonempty
                      (Σ sampledVoter : ℕ → Voter,
                        FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSample
                          M r0 xstar N sampledVoter)

/--
Almost-sure source trace skeleton for the corrected global-radius projected
Theorem 3 route.  The stochastic concentration theorem is not a field here:
`ProofInterface` derives it from the iid weighted-voter product law and then
extracts a pathwise sample.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalAETraceSkeleton
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  ae_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvTailRadius r0 N t)
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∀ᵐ sampledVoter
                          ∂theorem3FiniteWeightedVoterSequenceMeasure
                            M.weight M.weight_nonneg M.weight_sum,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          Convex ℝ E.solutionSpace ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar))

/--
Concrete coordinatewise continuity source for the finite normalized-gradient
field in Theorem 3.  This separates the paper's directional-field continuity
interpretation from the projected Algorithm 1 trace generator.
-/
structure FiniteTheorem3ConcreteFieldContinuitySource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε

/--
Trace-only deterministic global-radius source for the corrected projected-trace
Theorem 3 route.  It supplies pointwise projected Algorithm 1 trace data for
every sampled voter stream; coordinate continuity is supplied separately by
`FiniteTheorem3ConcreteFieldContinuitySource`.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  deterministic_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        response t voter =
                          fun i =>
                            E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + N) i +
                              ilvTailRadius r0 N t *
                                modelBFiniteNormalizedDirection SourceNorm.l2
                                  (M.utilityGradient voter
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N))) i) ∧
                      ∀ sampledVoter : ℕ → Voter,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar))

/--
Primitive global projected Algorithm 1 trace generator for the corrected
Theorem 3 route.  It exposes the two source facts that the old deterministic
trace core had bundled together: selected Model B raw responses are projected
onto the actual `E.trajectory`, and the limiting directional field is feasible
at the projected tail iterates under the positive-drift branch.
-/
structure FiniteTheorem3GlobalProjectedAlgorithm1TraceSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  normDistance : UsesFiniteCoordinateNormDistance E
  project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ
  project_norm :
    ∀ sampledVoter : ℕ → Voter,
      IsNormProjectionOnto E SourceNorm.l2 (project sampledVoter)
  projected_update :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ sampledVoter : ℕ → Voter,
                      ∀ t : ℕ,
                        Algorithm1ProjectedUpdate (project sampledVoter)
                          (fun i =>
                            E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + N) i +
                              ilvTailRadius r0 N t *
                                modelBFiniteNormalizedDirection SourceNorm.l2
                                  (M.utilityGradient (sampledVoter t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N))) i)
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
  feasible_direction :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ sampledVoter : ℕ → Voter,
                      ∀ t : ℕ,
                        FiniteFeasibleDirectionAt E.solutionSpace
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
                          (finiteTheorem3DirectionalField M.weight
                            M.utilityGradient xstar)

/--
More primitive global projected Algorithm 1 source for the Theorem 3 route.

Instead of assuming the aggregate field `G(x*)` is feasible after each
projection, this record asks for a common positive step along every selected
voter's normalized-gradient direction. Convexity and the finite voter weights
then prove aggregate feasibility for `G(x*)`.
-/
structure FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  normDistance : UsesFiniteCoordinateNormDistance E
  project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ
  project_norm :
    ∀ sampledVoter : ℕ → Voter,
      IsNormProjectionOnto E SourceNorm.l2 (project sampledVoter)
  projected_update :
    ∀ {N : ℕ},
      ∀ sampledVoter : ℕ → Voter,
        ∀ t : ℕ,
          Algorithm1ProjectedUpdate (project sampledVoter)
            (fun i =>
              E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + N) i +
                ilvTailRadius r0 N t *
                  modelBFiniteNormalizedDirection SourceNorm.l2
                    (M.utilityGradient (sampledVoter t)
                      (E.trajectory SourceNorm.l2
                        VoterResponseModel.modelB (t + N))) i)
            (E.trajectory SourceNorm.l2
              VoterResponseModel.modelB (t + 1 + N))

/--
Geometric feasibility source for the projected Theorem 3 residual argument.
This is separated from the Algorithm 1 update source because it is not a raw
update equation: it states the positive-step tangent fact needed to compare the
projection residual with the fixed limiting directional field.
-/
structure FiniteTheorem3GlobalProjectedLimitGradientFeasibilitySource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  per_voter_feasible_step :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ sampledVoter : ℕ → Voter,
                      ∀ t : ℕ,
                        ∃ η : ℝ,
                          0 < η ∧
                            ∀ voter : Voter,
                              (fun i =>
                                E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + 1 + N) i +
                                  η *
                                    modelBFiniteNormalizedDirection
                                      SourceNorm.l2
                                      (M.utilityGradient voter xstar) i) ∈
                                E.solutionSpace

/--
Aggregate feasibility source for the projected Theorem 3 residual argument.
This is the exact geometric fact consumed by the projection-residual proof:
from each projected tail iterate, the limiting directional field admits a
positive feasible step.  The older per-voter source below is a sufficient way
to construct this aggregate source, but the residual argument itself does not
need a pathwise feasible step for every voter separately.
-/
structure FiniteTheorem3GlobalProjectedAggregateFeasibilitySource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  aggregate_feasible_direction :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ t : ℕ,
                      FiniteFeasibleDirectionAt E.solutionSpace
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (t + 1 + N))
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)

/--
Record-free spelling of the aggregate feasible-direction condition.  This is
used by the final no-hidden-premise closeout to state the remaining constrained
Theorem 3 alternative without taking the aggregate-feasibility source record as
a premise.
-/
def FiniteTheorem3AggregateFeasibleDirectionFormula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) : Prop :=
  ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
            VoterResponseModel.modelB xstar →
            (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
              fun _ => (0 : ℝ)) →
              0 < c →
                (∀ n : ℕ,
                  c ≤
                    finiteDot
                      (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar)
                      (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient
                        (E.trajectory SourceNorm.l2
                          VoterResponseModel.modelB (n + N)))) →
                  ∀ t : ℕ,
                    FiniteFeasibleDirectionAt E.solutionSpace
                      (E.trajectory SourceNorm.l2
                        VoterResponseModel.modelB (t + 1 + N))
                      (finiteTheorem3DirectionalField M.weight
                        M.utilityGradient xstar)

def finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_formula
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (h : FiniteTheorem3AggregateFeasibleDirectionFormula M) :
    FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M where
  aggregate_feasible_direction := h

theorem finiteTheorem3AggregateFeasibleDirectionFormula_of_source
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M) :
    FiniteTheorem3AggregateFeasibleDirectionFormula M :=
  S.aggregate_feasible_direction

/--
Full-space solution sets justify the aggregate feasible-direction source used
by the projected Theorem 3 residual argument.  This is the concrete recovery of
the paper's unprojected drift proof in the unconstrained case: no boundary can
block a positive step along `G(x*)`.
-/
def finiteTheorem3GlobalProjectedAggregateFeasibilitySource_of_univ_solutionSpace
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (hUniv : E.solutionSpace = (Set.univ : Set (Coord → ℝ))) :
    FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M where
  aggregate_feasible_direction := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift t
    rw [hUniv]
    exact
      finiteFeasibleDirectionAt_univ
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + 1 + N))
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)

/--
Combined source record used by the existing Theorem 3 proof route.  New code
should usually construct this from
`FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource` plus
`FiniteTheorem3GlobalProjectedLimitGradientFeasibilitySource`.
-/
structure FiniteTheorem3GlobalProjectedAlgorithm1PerVoterStepTraceSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  normDistance : UsesFiniteCoordinateNormDistance E
  project : (ℕ → Voter) → (Coord → ℝ) → Coord → ℝ
  project_norm :
    ∀ sampledVoter : ℕ → Voter,
      IsNormProjectionOnto E SourceNorm.l2 (project sampledVoter)
  projected_update :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ sampledVoter : ℕ → Voter,
                      ∀ t : ℕ,
                        Algorithm1ProjectedUpdate (project sampledVoter)
                          (fun i =>
                            E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + N) i +
                              ilvTailRadius r0 N t *
                                modelBFiniteNormalizedDirection SourceNorm.l2
                                  (M.utilityGradient (sampledVoter t)
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N))) i)
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + 1 + N))
  per_voter_feasible_step :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∀ sampledVoter : ℕ → Voter,
                      ∀ t : ℕ,
                        ∃ η : ℝ,
                          0 < η ∧
                            ∀ voter : Voter,
                              (fun i =>
                                E.trajectory SourceNorm.l2
                                    VoterResponseModel.modelB (t + 1 + N) i +
                                  η *
                                    modelBFiniteNormalizedDirection
                                      SourceNorm.l2
                                      (M.utilityGradient voter xstar) i) ∈
                                E.solutionSpace

/--
The projected-update source and the geometric feasibility source recover the
combined per-voter trace record consumed by the existing global trace route.
-/
noncomputable def
    finiteTheorem3GlobalProjectedAlgorithm1PerVoterStepTraceSource_of_update_feasibility
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (F : FiniteTheorem3GlobalProjectedLimitGradientFeasibilitySource M) :
    FiniteTheorem3GlobalProjectedAlgorithm1PerVoterStepTraceSource M where
  r0 := U.r0
  r0_pos := U.r0_pos
  normDistance := U.normDistance
  project := U.project
  project_norm := U.project_norm
  projected_update := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
      sampledVoter t
    exact U.projected_update (N := N) sampledVoter t
  per_voter_feasible_step := F.per_voter_feasible_step

/--
The projected-update source and the aggregate feasible-direction source recover
the trace record consumed by the global projected residual proof without asking
for the stronger per-voter common-step witness.
-/
noncomputable def
    finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_update_aggregateFeasibility
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (U : FiniteTheorem3GlobalProjectedAlgorithm1UpdateSource M)
    (F : FiniteTheorem3GlobalProjectedAggregateFeasibilitySource M) :
    FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M where
  r0 := U.r0
  r0_pos := U.r0_pos
  normDistance := U.normDistance
  project := U.project
  project_norm := U.project_norm
  projected_update := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
      sampledVoter t
    exact U.projected_update (N := N) sampledVoter t
  feasible_direction := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
      sampledVoter t
    exact
      F.aggregate_feasible_direction hC hContinuous hResponse hConverges
        hNonzero hc hDrift t

/--
The per-voter common-step source is strong enough to recover the aggregate
feasible-direction field used by the projected-trace proof.
-/
noncomputable def
    finiteTheorem3GlobalProjectedAlgorithm1TraceSource_of_perVoterStepTraceSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (S : FiniteTheorem3GlobalProjectedAlgorithm1PerVoterStepTraceSource M) :
    FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M where
  r0 := S.r0
  r0_pos := S.r0_pos
  normDistance := S.normDistance
  project := S.project
  project_norm := S.project_norm
  projected_update := S.projected_update
  feasible_direction := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
      sampledVoter t
    rcases
      S.per_voter_feasible_step hC hContinuous hResponse hConverges
        hNonzero hc hDrift sampledVoter t with
      ⟨η, hη, hpointwise⟩
    have hfeasibleExpectation :
        FiniteFeasibleDirectionAt E.solutionSpace
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB
            (t + 1 + N))
          (finiteVoterExpectation M.weight
            (fun voter =>
              modelBFiniteNormalizedDirection SourceNorm.l2
                (M.utilityGradient voter xstar))) :=
      finiteFeasibleDirectionAt_finiteVoterExpectation_of_common_step
        (X := E.solutionSpace)
        (point :=
          E.trajectory SourceNorm.l2 VoterResponseModel.modelB
            (t + 1 + N))
        (η := η)
        (weight := M.weight)
        (dir := fun voter =>
          modelBFiniteNormalizedDirection SourceNorm.l2
            (M.utilityGradient voter xstar))
        (hConvex hC)
        M.weight_nonneg M.weight_sum hη hpointwise
    have hdir :
        finiteVoterExpectation M.weight
          (fun voter =>
            modelBFiniteNormalizedDirection SourceNorm.l2
              (M.utilityGradient voter xstar)) =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
      funext i
      exact
        (finiteTheorem3DirectionalField_coord_eq_modelBNormalizedExpectation
          M.weight M.utilityGradient xstar i).symm
    simpa [hdir] using hfeasibleExpectation

noncomputable def
    finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource_of_algorithm1Trace
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (S : FiniteTheorem3GlobalProjectedAlgorithm1TraceSource M) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
      M where
  r0 := S.r0
  r0_pos := S.r0_pos
  deterministic_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
    let response : ℕ → Voter → Coord → ℝ := fun t voter =>
      fun i =>
        E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N) i +
          ilvTailRadius S.r0 N t *
            modelBFiniteNormalizedDirection SourceNorm.l2
              (M.utilityGradient voter
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (t + N))) i
    refine ⟨response, ?_, ?_⟩
    · intro t voter
      rfl
    · intro sampledVoter
      refine
        ⟨fun t => response t (sampledVoter t), S.project sampledVoter,
          S.normDistance, S.project_norm sampledVoter, ?_, ?_, ?_⟩
      · intro t
        rfl
      · intro t
        exact
          S.projected_update hC hContinuous hResponse hConverges hNonzero hc
            hDrift sampledVoter t
      · intro t
        exact
          S.feasible_direction hC hContinuous hResponse hConverges hNonzero hc
            hDrift sampledVoter t

/--
Deterministic global-radius source skeleton for the corrected projected-trace
Theorem 3 route.  It supplies pointwise projected Algorithm 1 trace data for
every sampled voter stream; the iid concentration theorem is added separately
and this pointwise generator is later weakened to the almost-sure trace
skeleton.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  deterministic_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        response t voter =
                          fun i =>
                            E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + N) i +
                              ilvTailRadius r0 N t *
                                modelBFiniteNormalizedDirection SourceNorm.l2
                                  (M.utilityGradient voter
                                    (E.trajectory SourceNorm.l2
                                      VoterResponseModel.modelB (t + N))) i) ∧
                      ∀ sampledVoter : ℕ → Voter,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar))

def finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource_of_core
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (C : FiniteTheorem3ConcreteFieldContinuitySource M)
    (S :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
        M) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
      M where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := C.coordinate_continuity
  deterministic_projected_trace := S.deterministic_projected_trace

/--
Proof-facing deterministic trace skeleton: a raw deterministic trace source
together with the concrete C1 convexity interpretation needed for the Euclidean
projection residual argument.
-/
structure FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E) where
  r0 : ℝ
  r0_pos : 0 < r0
  coordinate_continuity :
    E.directionalFieldUniformlyContinuous →
      ∀ xstar i ε, 0 < ε →
        ∃ δ, 0 < δ ∧
          ∀ x : Coord → ℝ,
            finiteCoordinateDistance SourceNorm.l2 x xstar < δ →
              |finiteTheorem3DirectionalField M.weight M.utilityGradient x i -
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  xstar i| < ε
  convex_solutionSpace :
    ConditionsC123 E → Convex ℝ E.solutionSpace
  deterministic_projected_trace :
    ∀ {xstar : Coord → ℝ} {N : ℕ} {c : ℝ},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
              VoterResponseModel.modelB xstar →
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
                fun _ => (0 : ℝ)) →
                0 < c →
                  (∀ n : ℕ,
                    c ≤
                      finiteDot
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient xstar)
                        (finiteTheorem3DirectionalField M.weight
                          M.utilityGradient
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (n + N)))) →
                    ∃ response : ℕ → Voter → Coord → ℝ,
                      (∀ t voter,
                        ModelBFiniteResponseAt SourceNorm.l2
                          (E.trajectory SourceNorm.l2
                            VoterResponseModel.modelB (t + N))
                          (ilvTailRadius r0 N t)
                          (M.utilityGradient voter
                            (E.trajectory SourceNorm.l2
                              VoterResponseModel.modelB (t + N)))
                          (response t voter)) ∧
                      ∀ sampledVoter : ℕ → Voter,
                        ∃ raw : ℕ → Coord → ℝ,
                        ∃ project : (Coord → ℝ) → Coord → ℝ,
                          UsesFiniteCoordinateNormDistance E ∧
                          IsNormProjectionOnto E SourceNorm.l2 project ∧
                          (∀ t : ℕ, raw t = response t (sampledVoter t)) ∧
                          (∀ t : ℕ,
                            Algorithm1ProjectedUpdate project (raw t)
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))) ∧
                          (∀ t : ℕ,
                            FiniteFeasibleDirectionAt E.solutionSpace
                              (E.trajectory SourceNorm.l2
                                VoterResponseModel.modelB (t + 1 + N))
                              (finiteTheorem3DirectionalField M.weight
                                M.utilityGradient xstar))

def finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton_of_traceSource
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (hConvex : ConditionsC123 E → Convex ℝ E.solutionSpace)
    (S :
      FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
        M) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicSkeleton
      M where
  r0 := S.r0
  r0_pos := S.r0_pos
  coordinate_continuity := S.coordinate_continuity
  convex_solutionSpace := hConvex
  deterministic_projected_trace := by
    intro xstar N c hC hContinuous hResponse hConverges hNonzero hc hDrift
    rcases
      S.deterministic_projected_trace hC hContinuous hResponse hConverges
        hNonzero hc hDrift with
      ⟨response, hResponseFormula, hSampledTrace⟩
    refine ⟨response, ?_, hSampledTrace⟩
    intro t voter
    exact hResponseFormula t voter

theorem
    theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTraceGlobalPathwise
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalPathwiseSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  have hneConcrete :
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) := by
    intro hzero
    apply hne
    calc
      E.directionalField xstar =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
            rw [M.directionalField_eq]
      _ = (fun _ => 0) := hzero
      _ = E.zeroDirection := by
            rw [M.zeroDirection_eq]
  rcases finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges
      M (D.coordinate_continuity hContinuous) hConverges hneConcrete with
    ⟨N, c, hc, hdrift⟩
  rcases D.pathwise_projected_trace
      (xstar := xstar) (N := N) (c := c)
      hC hContinuous hResponse hConverges hneConcrete hc hdrift with
    ⟨⟨sampledVoter, P⟩⟩
  let trajectory : ℕ → Coord → ℝ :=
    fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
  let a : Coord → ℝ :=
    finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
  let T : ℕ := P.concentration_time
  let expected : ℕ → ℝ :=
    fun m =>
      ∑ t ∈ Finset.range m,
        ilvTailRadius D.r0 N t *
          finiteDot a
            (finiteTheorem3DirectionalField M.weight M.utilityGradient
              (trajectory (t + N)))
  have htail_lower :
      ∀ n : ℕ,
        (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          ∑ t ∈ Finset.range (n + T), ilvTailRadius D.r0 N t := by
    intro n
    have hprefix_nonneg :
        0 ≤ ∑ t ∈ Finset.range T, ilvTailRadius D.r0 N t := by
      exact Finset.sum_nonneg fun t _ht =>
        ilvTailRadius_nonneg (le_of_lt D.r0_pos) N t
    have htail_eq :
        (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) =
          ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      simp [ilvTailRadius, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    calc
      (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t)
          =
            ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) :=
            htail_eq
      _ ≤
            (∑ t ∈ Finset.range T, ilvTailRadius D.r0 N t) +
              ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) := by
            linarith
      _ =
            ∑ t ∈ Finset.range (T + n), ilvTailRadius D.r0 N t := by
            rw [Finset.sum_range_add]
      _ =
            ∑ t ∈ Finset.range (n + T), ilvTailRadius D.r0 N t := by
            rw [Nat.add_comm]
  have hlower :
      ∀ n : ℕ,
        -P.concentrationBound +
            c * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (trajectory (n + (N + T))) := by
    intro n
    let m : ℕ := n + T
    let rawExpected : ℝ :=
      ∑ t ∈ Finset.range m,
        ∑ voter : Voter,
          M.weight voter *
            finiteDot a
              (fun i => P.response t voter i - trajectory (t + N) i)
    let rawRealizedWithBase : ℝ :=
      theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
        ∑ t ∈ Finset.range m,
          finiteDot a
            (fun i => P.response t (sampledVoter t) i - trajectory (t + N) i)
    let actualProjection : ℝ :=
      theorem3ConcreteFiniteFieldProjection M xstar (trajectory (m + N))
    let residualSum : ℝ :=
      ∑ t ∈ Finset.range m,
        finiteDot a
          (fun i => P.response t (sampledVoter t) i -
            trajectory (t + 1 + N) i)
    have hm_ge_T : T ≤ m := by
      dsimp [m]
      exact Nat.le_add_left T n
    have hconcentration_raw :
        rawExpected - P.concentrationBound ≤ rawRealizedWithBase := by
      simpa [rawExpected, rawRealizedWithBase, trajectory, a, m] using
        P.concentration_control m hm_ge_T
    have hrawExpected_eq : rawExpected = expected m := by
      exact
        finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
          (weight := M.weight) (utilityGradient := M.utilityGradient)
          (center := fun t => trajectory (t + N))
          (radius := fun t => ilvTailRadius D.r0 N t)
          (response := P.response) a P.raw_response m
    have hresidual_id : rawRealizedWithBase - actualProjection = residualSum := by
      simpa [rawRealizedWithBase, actualProjection, residualSum, trajectory, a, m]
        using
          theorem3ConcreteFiniteFieldProjection_selectedRaw_residual_identity
            (M := M) (xstar := xstar) (trajectory := trajectory)
            (sampledVoter := sampledVoter) (response := P.response)
            (N := N) (n := m)
    have hresidual_nonpos : residualSum ≤ 0 := by
      simpa [residualSum, trajectory, a, m] using P.residual_sum_nonpos m
    have hprojection : rawRealizedWithBase ≤ actualProjection := by
      linarith
    have hfluctuation_tail : expected m - P.concentrationBound ≤ actualProjection := by
      calc
        expected m - P.concentrationBound =
            rawExpected - P.concentrationBound := by
              rw [hrawExpected_eq]
        _ ≤ rawRealizedWithBase := hconcentration_raw
        _ ≤ actualProjection := hprojection
    have hfull_expected_lower :
        c * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) ≤ expected m := by
      calc
        c * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t)
            = ∑ t ∈ Finset.range m, c * ilvTailRadius D.r0 N t := by
              rw [Finset.mul_sum]
        _ = ∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t * c := by
              apply Finset.sum_congr rfl
              intro t _ht
              ring
        _ ≤
            ∑ t ∈ Finset.range m,
              ilvTailRadius D.r0 N t *
                finiteDot a
                  (finiteTheorem3DirectionalField M.weight M.utilityGradient
                    (trajectory (t + N))) := by
              exact Finset.sum_le_sum fun t _ht =>
                mul_le_mul_of_nonneg_left (hdrift t)
                  (ilvTailRadius_nonneg (le_of_lt D.r0_pos) N t)
        _ = expected m := by
              rfl
    have hscaled_tail :
        c * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          c * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) := by
      have htail := htail_lower n
      simpa [m] using mul_le_mul_of_nonneg_left htail (le_of_lt hc)
    have htarget :
        -P.concentrationBound +
            c * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          actualProjection := by
      calc
        -P.concentrationBound +
            c * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t)
            ≤
              -P.concentrationBound +
                c * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) := by
              linarith
        _ ≤ -P.concentrationBound + expected m := by
              linarith
        _ = expected m - P.concentrationBound := by
              ring
        _ ≤ actualProjection := hfluctuation_tail
    simpa [actualProjection, trajectory, m, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using htarget
  have hproj_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          theorem3ConcreteFiniteFieldProjection M xstar
            (trajectory (n + (N + T))))
        Filter.atTop
        (nhds (theorem3ConcreteFiniteFieldProjection M xstar xstar)) := by
    simpa [trajectory, theorem3ConcreteFiniteFieldProjection_eq M,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      theorem3FiniteFieldProjection_tendsto_nat_add
        (E := E) (xstar := xstar) hConverges (N + T)
  exact
    scalar_convergence_contradiction_of_accumulated_drift
      (s := fun n =>
        theorem3ConcreteFiniteFieldProjection M xstar
          (trajectory (n + (N + T))))
      (limit := theorem3ConcreteFiniteFieldProjection M xstar xstar)
      (base := -P.concentrationBound)
      (c := c)
      (radiusTail := fun t => ilvTailRadius D.r0 (N + T) t)
      hc
      (ilvTailRadius_sum_tendsto_atTop D.r0_pos (N + T))
      hlower
      hproj_tendsto

noncomputable def
    FiniteTheorem3ConcreteCoordinateEscapeSemantics.toPaperNeighborhoodEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateEscapeSemantics M) :
    FiniteTheorem3ConcretePaperNeighborhoodEscapeSemantics M where
  neighborhood_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases D.coordinate_escape hC hContinuous hResponse hConverges
        hneConcrete with
      ⟨i, δ, hδpos, hescape⟩
    refine ⟨δ, hδpos, ?_⟩
    intro δ₂ hδ₂pos hδ₂lt t
    rcases hescape δ₂ hδ₂pos hδ₂lt t with ⟨τ, htτ, hcoord⟩
    refine ⟨τ, htτ, ?_⟩
    exact lt_of_lt_of_le hcoord
      (finiteCoordinateDistance_l2_coord_abs_le
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB τ) xstar i)

noncomputable def
    FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics.toCoordinateEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics M) :
    FiniteTheorem3ConcreteCoordinateEscapeSemantics M where
  coordinate_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    have hcont : FiniteTheorem3DirectionalFieldCoordinateContinuity M :=
      D.coordinate_continuity hContinuous
    rcases finiteTheorem3DirectionalField_eventual_coordinate_drift_of_converges
        M hcont hConverges hneConcrete with
      ⟨i, N, ε₂, hε₂pos, hdrift⟩
    rcases D.drift_coordinate_escape
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨δ, hδpos, hescape⟩
    exact ⟨i, δ, hδpos, hescape⟩

noncomputable def
    FiniteTheorem3ConcreteCoordinateAccumulationSemantics.toCoordinateDriftEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateAccumulationSemantics M) :
    FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics M where
  coordinate_continuity := D.coordinate_continuity
  drift_coordinate_escape := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.accumulated_signed_coordinate_escape
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨c, baseValue, hc, hlower⟩
    let a : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    have ha_ne : a ≠ 0 := by
      intro ha
      have hprod := (hdrift 0).2
      have ha0 :
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i = 0 := by
        simpa [a] using ha
      rw [ha0, zero_mul] at hprod
      exact (lt_irrefl (0 : ℝ)) hprod
    have ha_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
    refine ⟨1, by norm_num, ?_⟩
    intro δ₂ hδ₂pos _hδ₂lt t
    let bound : ℝ := (|a| * δ₂ - baseValue) / c
    have hsum_eventual :
        ∀ᶠ n in Filter.atTop,
          bound <
            ∑ k ∈ Finset.range n, ilvRadius D.r0 (k + 1) :=
      (ilvRadius_sum_tendsto_atTop D.r0_pos).eventually
        (Filter.eventually_gt_atTop bound)
    have hlate_eventual :
        ∀ᶠ n in Filter.atTop, t ≤ n + N := by
      exact Filter.eventually_atTop.2
        ⟨t, by
          intro n hn
          exact le_trans hn (Nat.le_add_right n N)⟩
    rcases Filter.eventually_atTop.1 (hsum_eventual.and hlate_eventual) with
      ⟨n0, hn0⟩
    rcases hn0 n0 le_rfl with ⟨hsum, hlate⟩
    refine ⟨n0 + N, hlate, ?_⟩
    have htarget_lt_csum :
        |a| * δ₂ - baseValue <
          c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) := by
      have hmul :
          c * bound <
            c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) :=
        mul_lt_mul_of_pos_left hsum hc
      have hbound_eq : c * bound = |a| * δ₂ - baseValue := by
        dsimp [bound]
        field_simp [hc.ne']
      calc
        |a| * δ₂ - baseValue = c * bound := hbound_eq.symm
        _ < c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) := hmul
    have htarget_lt_signed :
        |a| * δ₂ <
          a * (E.trajectory SourceNorm.l2
            VoterResponseModel.modelB (n0 + N) i - xstar i) := by
      have hlower_n :
          baseValue +
              c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) ≤
            a * (E.trajectory SourceNorm.l2
              VoterResponseModel.modelB (n0 + N) i - xstar i) := by
        simpa [a] using hlower n0
      linarith
    let d : ℝ :=
      E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n0 + N) i - xstar i
    have hmul_lt : |a| * δ₂ < |a| * |d| := by
      calc
        |a| * δ₂ < a * d := by
          simpa [d] using htarget_lt_signed
        _ ≤ |a * d| := le_abs_self _
        _ = |a| * |d| := by rw [abs_mul]
    exact lt_of_mul_lt_mul_left hmul_lt ha_abs_pos.le

noncomputable def
    FiniteTheorem3ConcreteCoordinateStepProgressSemantics.toCoordinateAccumulationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateStepProgressSemantics M) :
    FiniteTheorem3ConcreteCoordinateAccumulationSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  accumulated_signed_coordinate_escape := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.one_step_signed_coordinate_progress
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨c, hc, hstep⟩
    let a : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    refine
      ⟨c,
        a * (E.trajectory SourceNorm.l2 VoterResponseModel.modelB N i - xstar i),
        hc, ?_⟩
    intro n
    have htel :=
      scalar_accumulated_drift_lower_bound_of_one_step
        (s := fun n =>
          a * (E.trajectory SourceNorm.l2
            VoterResponseModel.modelB (n + N) i - xstar i))
        (radiusTail := fun t => ilvRadius D.r0 (t + 1))
        (c := c) hstep n
    simpa [a] using htel

noncomputable def
    FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics.toCoordinateAccumulationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics M) :
    FiniteTheorem3ConcreteCoordinateAccumulationSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  accumulated_signed_coordinate_escape := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.expected_minus_fluctuation_signed_coordinate_escape
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨c, expectedBase, fluctuationBound, expectedSignedDisplacement,
        hc, hexpected, hfluctuation⟩
    refine ⟨c, expectedBase - fluctuationBound, hc, ?_⟩
    intro n
    have hexpected_n := hexpected n
    have hfluctuation_n := hfluctuation n
    linarith

noncomputable def
    FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics.toExpectedFluctuationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  expected_minus_fluctuation_signed_coordinate_escape := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.coordinate_fluctuation_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨fluctuationBound, hfluctuation⟩
    let a : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    let expectedSignedDisplacement : ℕ → ℝ :=
      fun n =>
        ∑ t ∈ Finset.range n,
          a * (ilvRadius D.r0 (t + 1) *
            finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)) i)
    have ha_ne : a ≠ 0 := by
      intro ha
      have hprod := (hdrift 0).2
      have ha0 :
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i = 0 := by
        simpa [a] using ha
      rw [ha0, zero_mul] at hprod
      exact (lt_irrefl (0 : ℝ)) hprod
    have hc : 0 < |a| * ε₂ :=
      mul_pos (abs_pos.mpr ha_ne) hε₂pos
    refine ⟨|a| * ε₂, 0, fluctuationBound, expectedSignedDisplacement, hc, ?_, ?_⟩
    · intro n
      have hsum :=
        signed_expected_coordinate_sum_lower_bound_of_drift_sequence
          (r0 := D.r0) (a := a) (ε := ε₂)
          (b := fun t =>
            finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (t + N)) i)
          D.r0_pos hdrift n
      simpa [expectedSignedDisplacement, a] using hsum
    · intro n
      simpa [expectedSignedDisplacement, a] using hfluctuation n

noncomputable def
    FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics.toCoordinateAccumulationSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteCoordinateAccumulationSemantics M :=
  FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics.toCoordinateAccumulationSemantics
    (FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics.toExpectedFluctuationSemantics
      D)

noncomputable def
    FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics.toEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  coordinate_fluctuation_eventual_control := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.coordinate_fluctuation_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨fluctuationBound, hfluctuation⟩
    exact ⟨fluctuationBound, 0, by
      intro n _hn
      exact hfluctuation n⟩

noncomputable def
    FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateDriftEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics M where
  coordinate_continuity := D.coordinate_continuity
  drift_coordinate_escape := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.coordinate_fluctuation_eventual_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨fluctuationBound, T, hfluctuation⟩
    let a : ℝ := finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    have ha_ne : a ≠ 0 := by
      intro ha
      have hprod := (hdrift 0).2
      have ha0 :
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i = 0 := by
        simpa [a] using ha
      rw [ha0, zero_mul] at hprod
      exact (lt_irrefl (0 : ℝ)) hprod
    have ha_abs_pos : 0 < |a| := abs_pos.mpr ha_ne
    let c : ℝ := |a| * ε₂
    have hc : 0 < c := by
      dsimp [c]
      exact mul_pos ha_abs_pos hε₂pos
    refine ⟨1, by norm_num, ?_⟩
    intro δ₂ hδ₂pos _hδ₂lt t
    let bound : ℝ := (|a| * δ₂ + fluctuationBound) / c
    have hsum_eventual :
        ∀ᶠ n in Filter.atTop,
          bound <
            ∑ k ∈ Finset.range n, ilvRadius D.r0 (k + 1) :=
      (ilvRadius_sum_tendsto_atTop D.r0_pos).eventually
        (Filter.eventually_gt_atTop bound)
    have hlate_eventual :
        ∀ᶠ n in Filter.atTop, t ≤ n + N := by
      exact Filter.eventually_atTop.2
        ⟨t, by
          intro n hn
          exact le_trans hn (Nat.le_add_right n N)⟩
    have hfluctuation_eventual :
        ∀ᶠ n in Filter.atTop,
          (∑ k ∈ Finset.range n,
              a * (ilvRadius D.r0 (k + 1) *
                finiteTheorem3DirectionalField M.weight M.utilityGradient
                  (E.trajectory SourceNorm.l2
                    VoterResponseModel.modelB (k + N)) i)) -
              fluctuationBound ≤
            a *
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                  (n + N) i - xstar i) := by
      exact Filter.eventually_atTop.2
        ⟨T, by
          intro n hn
          simpa [a] using hfluctuation n hn⟩
    rcases Filter.eventually_atTop.1
        ((hsum_eventual.and hlate_eventual).and hfluctuation_eventual) with
      ⟨n0, hn0⟩
    rcases hn0 n0 le_rfl with ⟨⟨hsum, hlate⟩, hfluct_n⟩
    refine ⟨n0 + N, hlate, ?_⟩
    have hexpected_lower :
        c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) ≤
          ∑ k ∈ Finset.range n0,
            a * (ilvRadius D.r0 (k + 1) *
              finiteTheorem3DirectionalField M.weight M.utilityGradient
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (k + N)) i) := by
      have hsum_lower :=
        signed_expected_coordinate_sum_lower_bound_of_drift_sequence
          (r0 := D.r0) (a := a) (ε := ε₂)
          (b := fun k =>
            finiteTheorem3DirectionalField M.weight M.utilityGradient
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (k + N)) i)
          D.r0_pos hdrift n0
      simpa [c, a] using hsum_lower
    have htarget_lt_csum :
        |a| * δ₂ + fluctuationBound <
          c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) := by
      have hmul :
          c * bound <
            c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) :=
        mul_lt_mul_of_pos_left hsum hc
      have hbound_eq : c * bound = |a| * δ₂ + fluctuationBound := by
        dsimp [bound]
        field_simp [hc.ne']
      calc
        |a| * δ₂ + fluctuationBound = c * bound := hbound_eq.symm
        _ < c * (∑ k ∈ Finset.range n0, ilvRadius D.r0 (k + 1)) := hmul
    have htarget_lt_expected :
        |a| * δ₂ + fluctuationBound <
          ∑ k ∈ Finset.range n0,
            a * (ilvRadius D.r0 (k + 1) *
              finiteTheorem3DirectionalField M.weight M.utilityGradient
                (E.trajectory SourceNorm.l2
                  VoterResponseModel.modelB (k + N)) i) := by
      exact lt_of_lt_of_le htarget_lt_csum hexpected_lower
    have htarget_lt_signed :
        |a| * δ₂ <
          a * (E.trajectory SourceNorm.l2
            VoterResponseModel.modelB (n0 + N) i - xstar i) := by
      linarith
    let d : ℝ :=
      E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n0 + N) i - xstar i
    have hmul_lt : |a| * δ₂ < |a| * |d| := by
      calc
        |a| * δ₂ < a * d := by
          simpa [d] using htarget_lt_signed
        _ ≤ |a * d| := le_abs_self _
        _ = |a| * |d| := by rw [abs_mul]
    exact lt_of_mul_lt_mul_left hmul_lt ha_abs_pos.le

noncomputable def
    FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteCoordinateEscapeSemantics M :=
  FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics.toCoordinateEscapeSemantics
    (FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateDriftEscapeSemantics
      D)

noncomputable def
    FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  coordinate_fluctuation_eventual_control := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.sampled_raw_fluctuation_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨sampledVoter, response, hrawResponse, hactualIncrement,
        fluctuationBound, T, hfluctuation⟩
    refine ⟨fluctuationBound, T, ?_⟩
    intro n hn
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
    let a : ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    have hexpected_sum :
        (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter * (a * (response t voter i - trajectory (t + N) i))) =
          ∑ t ∈ Finset.range n,
            a * (ilvRadius D.r0 (t + 1) *
              finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N)) i) := by
      exact
        finiteTheorem3DirectionalField_expected_signed_modelB_response_increment_sum
          (weight := M.weight) (utilityGradient := M.utilityGradient)
          (center := fun t => trajectory (t + N))
          (radius := fun t => ilvRadius D.r0 (t + 1))
          (response := response) i a hrawResponse n
    have hrealized_sum :
        a * (trajectory (n + N) i - xstar i) =
          a * (trajectory N i - xstar i) +
            ∑ t ∈ Finset.range n,
              a * (response t (sampledVoter t) i -
                trajectory (t + N) i) := by
      have htel :=
        signed_finiteCoordinate_tail_displacement_eq_base_add_sum_increments
          trajectory a xstar i N n
      calc
        a * (trajectory (n + N) i - xstar i)
            =
              a * (trajectory N i - xstar i) +
                ∑ t ∈ Finset.range n,
                  a * (trajectory (t + 1 + N) i - trajectory (t + N) i) :=
              htel
        _ =
              a * (trajectory N i - xstar i) +
                ∑ t ∈ Finset.range n,
                  a * (response t (sampledVoter t) i -
                    trajectory (t + N) i) := by
              congr 1
              apply Finset.sum_congr rfl
              intro t _ht
              rw [hactualIncrement t]
    have hfluctuation_n := hfluctuation n hn
    calc
      (∑ t ∈ Finset.range n,
          a * (ilvRadius D.r0 (t + 1) *
            finiteTheorem3DirectionalField M.weight M.utilityGradient
              (trajectory (t + N)) i)) -
          fluctuationBound
          =
        (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter * (a * (response t voter i - trajectory (t + N) i))) -
          fluctuationBound := by
            rw [hexpected_sum]
      _ ≤
          a * (trajectory N i - xstar i) +
            ∑ t ∈ Finset.range n,
              a * (response t (sampledVoter t) i -
                trajectory (t + N) i) := by
            simpa [trajectory, a] using hfluctuation_n
      _ =
          a * (trajectory (n + N) i - xstar i) := by
            rw [hrealized_sum]

noncomputable def
    FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toCoordinateEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteCoordinateEscapeSemantics M :=
  FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateEscapeSemantics
    (FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toEventualHoeffdingShellSemantics
      D)

noncomputable def
    FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toProjectedRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_fluctuation_control := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.sampled_raw_fluctuation_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨sampledVoter, response, hrawResponse, hactualIncrement,
        fluctuationBound, T, hfluctuation⟩
    refine ⟨sampledVoter, response, hrawResponse, fluctuationBound, 0, T, ?_⟩
    intro n hn
    constructor
    · exact hfluctuation n hn
    · let trajectory : ℕ → Coord → ℝ :=
        fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
      let a : ℝ :=
        finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
      have hrealized_sum :
          a * (trajectory (n + N) i - xstar i) =
            a * (trajectory N i - xstar i) +
              ∑ t ∈ Finset.range n,
                a * (response t (sampledVoter t) i -
                  trajectory (t + N) i) := by
        have htel :=
          signed_finiteCoordinate_tail_displacement_eq_base_add_sum_increments
            trajectory a xstar i N n
        calc
          a * (trajectory (n + N) i - xstar i)
              =
                a * (trajectory N i - xstar i) +
                  ∑ t ∈ Finset.range n,
                    a * (trajectory (t + 1 + N) i - trajectory (t + N) i) :=
                htel
          _ =
                a * (trajectory N i - xstar i) +
                  ∑ t ∈ Finset.range n,
                    a * (response t (sampledVoter t) i -
                      trajectory (t + N) i) := by
                congr 1
                apply Finset.sum_congr rfl
                intro t _ht
                rw [hactualIncrement t]
      have hslack :
          (a * (trajectory N i - xstar i) +
              ∑ t ∈ Finset.range n,
                a * (response t (sampledVoter t) i -
                  trajectory (t + N) i)) - 0 ≤
            a * (trajectory (n + N) i - xstar i) := by
        rw [← hrealized_sum]
        linarith
      simpa [trajectory, a] using hslack

noncomputable def
    FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics.toEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  coordinate_fluctuation_eventual_control := by
    intro xstar i N ε₂ hC hContinuous hResponse hConverges hε₂pos hdrift
    rcases D.sampled_projected_fluctuation_control
        (xstar := xstar) (i := i) (N := N) (ε₂ := ε₂)
        hC hContinuous hResponse hConverges hε₂pos hdrift with
      ⟨sampledVoter, response, hrawResponse,
        concentrationBound, projectionSlackBound, T, hbounds⟩
    refine ⟨concentrationBound + projectionSlackBound, T, ?_⟩
    intro n hn
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
    let a : ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar i
    let rawExpected : ℝ :=
      ∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          M.weight voter * (a * (response t voter i - trajectory (t + N) i))
    let fieldExpected : ℝ :=
      ∑ t ∈ Finset.range n,
        a * (ilvRadius D.r0 (t + 1) *
          finiteTheorem3DirectionalField M.weight M.utilityGradient
            (trajectory (t + N)) i)
    let rawRealizedWithBase : ℝ :=
      a * (trajectory N i - xstar i) +
        ∑ t ∈ Finset.range n,
          a * (response t (sampledVoter t) i - trajectory (t + N) i)
    let actualSigned : ℝ :=
      a * (trajectory (n + N) i - xstar i)
    have hexpected_sum : rawExpected = fieldExpected := by
      exact
        finiteTheorem3DirectionalField_expected_signed_modelB_response_increment_sum
          (weight := M.weight) (utilityGradient := M.utilityGradient)
          (center := fun t => trajectory (t + N))
          (radius := fun t => ilvRadius D.r0 (t + 1))
          (response := response) i a hrawResponse n
    have hbounds_n := hbounds n hn
    have hconcentration :
        rawExpected - concentrationBound ≤ rawRealizedWithBase := by
      simpa [rawExpected, rawRealizedWithBase, trajectory, a] using
        hbounds_n.1
    have hprojection :
        rawRealizedWithBase - projectionSlackBound ≤ actualSigned := by
      simpa [rawRealizedWithBase, actualSigned, trajectory, a] using
        hbounds_n.2
    have hmain :
        fieldExpected - (concentrationBound + projectionSlackBound) ≤
          actualSigned := by
      calc
        fieldExpected - (concentrationBound + projectionSlackBound)
            = rawExpected - (concentrationBound + projectionSlackBound) := by
              rw [← hexpected_sum]
        _ = (rawExpected - concentrationBound) - projectionSlackBound := by
              ring
        _ ≤ rawRealizedWithBase - projectionSlackBound := by
              linarith
        _ ≤ actualSigned := hprojection
    simpa [fieldExpected, actualSigned, trajectory, a] using hmain

noncomputable def
    FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics.toCoordinateEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteCoordinateEscapeSemantics M :=
  FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateEscapeSemantics
    (FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics.toEventualHoeffdingShellSemantics
      D)

noncomputable def
    FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics.toProjectedRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.sampled_exact_finiteDot_fluctuation_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨sampledVoter, response, hrawResponse, hactualIncrement,
        fluctuationBound, T, hfluctuation⟩
    refine ⟨sampledVoter, response, hrawResponse, fluctuationBound, 0, T, ?_⟩
    intro n hn
    constructor
    · exact hfluctuation n hn
    · let trajectory : ℕ → Coord → ℝ :=
        fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
      let a : Coord → ℝ :=
        finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
      have hselected_eq_steps :
          (∑ t ∈ Finset.range n,
              finiteDot a
                (fun i => response t (sampledVoter t) i -
                  trajectory (t + N) i)) =
            ∑ t ∈ Finset.range n,
              finiteDot a
                (fun i => trajectory (t + 1 + N) i - trajectory (t + N) i) := by
        apply Finset.sum_congr rfl
        intro t _ht
        unfold finiteDot
        apply Finset.sum_congr rfl
        intro i _hi
        dsimp [trajectory]
        rw [← hactualIncrement t i]
      have hrealized_eq :
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
              ∑ t ∈ Finset.range n,
                finiteDot a
                  (fun i => response t (sampledVoter t) i -
                    trajectory (t + N) i) =
            theorem3ConcreteFiniteFieldProjection M xstar
              (trajectory (n + N)) := by
        rw [theorem3ConcreteFiniteFieldProjection_tail_eq_base_add_sum_steps
          (M := M) (xstar := xstar) (trajectory := trajectory) (N := N) (n := n)]
        rw [hselected_eq_steps]
      have hprojection :
          theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
              ∑ t ∈ Finset.range n,
                finiteDot a
                  (fun i => response t (sampledVoter t) i -
                    trajectory (t + N) i) ≤
            theorem3ConcreteFiniteFieldProjection M xstar
              (trajectory (n + N)) + 0 := by
        rw [hrealized_eq]
        linarith
      simpa [trajectory, a] using hprojection

noncomputable def
    FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics.toProjectedRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics M) :
    FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.sampled_projected_residual_finiteDot_fluctuation_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨sampledVoter, response, hrawResponse,
        concentrationBound, residualBound, T, hbounds⟩
    refine ⟨sampledVoter, response, hrawResponse, concentrationBound,
      residualBound, T, ?_⟩
    intro n hn
    constructor
    · exact (hbounds n hn).1
    · let trajectory : ℕ → Coord → ℝ :=
        fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
      let a : Coord → ℝ :=
        finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
      let rawRealizedWithBase : ℝ :=
        theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
          ∑ t ∈ Finset.range n,
            finiteDot a
              (fun i => response t (sampledVoter t) i - trajectory (t + N) i)
      let actualProjection : ℝ :=
        theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N))
      let residualSum : ℝ :=
        ∑ t ∈ Finset.range n,
          finiteDot a
            (fun i => response t (sampledVoter t) i -
              trajectory (t + 1 + N) i)
      have hresidual_id :
          rawRealizedWithBase - actualProjection = residualSum := by
        simpa [rawRealizedWithBase, actualProjection, residualSum,
          trajectory, a] using
          theorem3ConcreteFiniteFieldProjection_selectedRaw_residual_identity
            (M := M) (xstar := xstar) (trajectory := trajectory)
            (sampledVoter := sampledVoter) (response := response)
            (N := N) (n := n)
      have hresidual_bound : residualSum ≤ residualBound := by
        simpa [residualSum, trajectory, a] using (hbounds n hn).2
      have hprojection :
          rawRealizedWithBase ≤ actualProjection + residualBound := by
        linarith
      simpa [rawRealizedWithBase, actualProjection, trajectory, a] using hprojection

noncomputable def
    FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics.toProjectedResidualHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTraceHoeffdingSemantics M) :
    FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_projected_residual_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.sampled_projected_trace_finiteDot_fluctuation_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨sampledVoter, response, raw, project, hNorm, hconv, hproject,
        hrawResponse, hselectedRaw, hprojectedUpdate, hfeasibleDirection,
        concentrationBound, T, hconcentration⟩
    refine ⟨sampledVoter, response, hrawResponse, concentrationBound, 0, T, ?_⟩
    intro n hn
    constructor
    · exact hconcentration n hn
    · let trajectory : ℕ → Coord → ℝ :=
        fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
      let direction : Coord → ℝ :=
        finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
      have hnormal :
          ∀ t : ℕ,
            FiniteProjectionNormalConeAt E.solutionSpace (raw t)
              (trajectory (t + 1 + N)) := by
        intro t
        exact
          finiteProjectionNormalConeAt_of_l2_normProjection
            (E := E) hNorm hconv hproject (hprojectedUpdate t)
      have hresidual_raw :
          ∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i => raw t i - trajectory (t + 1 + N) i) ≤ 0 := by
        exact
          finiteDot_projection_residual_sum_nonpos_of_feasibleDirectionAt
            (X := E.solutionSpace)
            (raw := raw)
            (next := fun t => trajectory (t + 1 + N))
            (direction := direction)
            hnormal
            (by
              intro t
              simpa [trajectory, direction] using hfeasibleDirection t)
            n
      have hresidual_selected :
          (∑ t ∈ Finset.range n,
            finiteDot direction
              (fun i =>
                response t (sampledVoter t) i - trajectory (t + 1 + N) i)) =
            ∑ t ∈ Finset.range n,
              finiteDot direction
                (fun i => raw t i - trajectory (t + 1 + N) i) := by
        apply Finset.sum_congr rfl
        intro t _ht
        rw [← hselectedRaw t]
      calc
        ∑ t ∈ Finset.range n,
            finiteDot
              (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar)
              (fun i =>
                response t (sampledVoter t) i -
                  E.trajectory SourceNorm.l2 VoterResponseModel.modelB
                    (t + 1 + N) i)
            =
              ∑ t ∈ Finset.range n,
                finiteDot direction
                  (fun i =>
                    response t (sampledVoter t) i -
                      trajectory (t + 1 + N) i) := by
                rfl
        _ =
              ∑ t ∈ Finset.range n,
                finiteDot direction
                  (fun i => raw t i - trajectory (t + 1 + N) i) :=
                hresidual_selected
        _ ≤ 0 := hresidual_raw

noncomputable def
    FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics.toSampledRawHoeffdingSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  sampled_finiteDot_fluctuation_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.sampled_projected_finiteDot_fluctuation_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨sampledVoter, response, hrawResponse,
        concentrationBound, projectionSlackBound, T, hbounds⟩
    refine ⟨response, hrawResponse, concentrationBound + projectionSlackBound, T, ?_⟩
    intro n hn
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
    let a : Coord → ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
    let rawExpected : ℝ :=
      ∑ t ∈ Finset.range n,
        ∑ voter : Voter,
          M.weight voter *
            finiteDot a (fun i => response t voter i - trajectory (t + N) i)
    let rawRealizedWithBase : ℝ :=
      theorem3ConcreteFiniteFieldProjection M xstar (trajectory N) +
        ∑ t ∈ Finset.range n,
          finiteDot a
            (fun i => response t (sampledVoter t) i - trajectory (t + N) i)
    let actualProjection : ℝ :=
      theorem3ConcreteFiniteFieldProjection M xstar (trajectory (n + N))
    have hbounds_n := hbounds n hn
    have hconcentration :
        rawExpected - concentrationBound ≤ rawRealizedWithBase := by
      simpa [rawExpected, rawRealizedWithBase, trajectory, a] using
        hbounds_n.1
    have hprojection :
        rawRealizedWithBase ≤ actualProjection + projectionSlackBound := by
      simpa [rawRealizedWithBase, actualProjection, trajectory, a] using
        hbounds_n.2
    have hmain :
        rawExpected - (concentrationBound + projectionSlackBound) ≤
          actualProjection := by
      calc
        rawExpected - (concentrationBound + projectionSlackBound)
            = (rawExpected - concentrationBound) - projectionSlackBound := by
              ring
        _ ≤ rawRealizedWithBase - projectionSlackBound := by
              linarith
        _ ≤ actualProjection := by
              linarith
    simpa [rawExpected, actualProjection, trajectory, a] using hmain

noncomputable def
    FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics.toFiniteDotHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics M) :
    FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  coordinate_continuity := D.coordinate_continuity
  finiteDot_fluctuation_eventual_control := by
    intro xstar N c hC hContinuous hResponse hConverges hneConcrete hc hdrift
    rcases D.sampled_finiteDot_fluctuation_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨response, hrawResponse, fluctuationBound, T, hfluctuation⟩
    refine ⟨fluctuationBound, T, ?_⟩
    intro n hn
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
    let a : Coord → ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
    have hexpected_sum :
        (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter *
              finiteDot a
                (fun i => response t voter i - trajectory (t + N) i)) =
          ∑ t ∈ Finset.range n,
            ilvRadius D.r0 (t + 1) *
              finiteDot a
                (finiteTheorem3DirectionalField M.weight M.utilityGradient
                  (trajectory (t + N))) := by
      exact
        finiteTheorem3DirectionalField_expected_finiteDot_modelB_response_increment_sum
          (weight := M.weight) (utilityGradient := M.utilityGradient)
          (center := fun t => trajectory (t + N))
          (radius := fun t => ilvRadius D.r0 (t + 1))
          (response := response) a hrawResponse n
    calc
      (∑ t ∈ Finset.range n,
          ilvRadius D.r0 (t + 1) *
            finiteDot a
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N)))) -
          fluctuationBound
          =
        (∑ t ∈ Finset.range n,
          ∑ voter : Voter,
            M.weight voter *
              finiteDot a
                (fun i => response t voter i - trajectory (t + N) i)) -
          fluctuationBound := by
            rw [← hexpected_sum]
      _ ≤ theorem3ConcreteFiniteFieldProjection M xstar
            (trajectory (n + N)) := by
            simpa [trajectory, a] using hfluctuation n hn

noncomputable def
    FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics.toEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics M) :
    FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_finiteDot_drift := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    exact
      finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges
        M (D.coordinate_continuity hContinuous) hConverges hneConcrete
  finiteDot_fluctuation_eventual_control :=
    D.finiteDot_fluctuation_eventual_control

noncomputable def
    FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics M) :
    FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_accumulated_projection_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases D.eventual_finiteDot_drift
        hC hContinuous hResponse hConverges hneConcrete with
      ⟨N, c, hc, hdrift⟩
    rcases D.finiteDot_fluctuation_eventual_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨fluctuationBound, T, hfluctuation⟩
    refine ⟨N + T, c, -fluctuationBound, hc, ?_⟩
    intro n
    let a : Coord → ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelB t
    let expected : ℕ → ℝ :=
      fun m =>
        ∑ t ∈ Finset.range m,
          ilvRadius D.r0 (t + 1) *
            finiteDot a
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N)))
    have hfluctuation_tail := hfluctuation (n + T) (Nat.le_add_left T n)
    have hlower_expected :
        c * (∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1)) ≤
          expected (n + T) := by
      simpa [expected, trajectory, a] using
        finiteDot_expected_sum_lower_bound_of_drift_sequence
          (r0 := D.r0) (c := c)
          (b := fun t =>
            finiteDot a
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N))))
          D.r0_pos hdrift (n + T)
    have hsum_mono :
        (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          ∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1) :=
      ilvRadius_sum_range_mono_add D.r0_pos n T
    have hscaled_mono :
        c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          c * (∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1)) := by
      exact mul_le_mul_of_nonneg_left hsum_mono (le_of_lt hc)
    have htarget_tail :
        -fluctuationBound +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (trajectory ((n + T) + N)) := by
      calc
        -fluctuationBound +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1))
            ≤
              -fluctuationBound +
                c * (∑ t ∈ Finset.range (n + T),
                  ilvRadius D.r0 (t + 1)) := by
              linarith
        _ ≤ -fluctuationBound + expected (n + T) := by
              linarith
        _ = expected (n + T) - fluctuationBound := by
              ring
        _ ≤ theorem3ConcreteFiniteFieldProjection M xstar
              (trajectory ((n + T) + N)) := by
              simpa [expected, trajectory, a] using hfluctuation_tail
    simpa [trajectory, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      htarget_tail

noncomputable def
    FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics M) :
    FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics M :=
  FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    (FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics.toEventualHoeffdingShellSemantics
      D)

noncomputable def
    FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics.toEventualHoeffdingShellSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics M) :
    FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_finiteDot_drift := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    exact
      finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges_model
        M (D.coordinate_continuity hContinuous) hConverges hneConcrete
  finiteDot_fluctuation_eventual_control :=
    D.finiteDot_fluctuation_eventual_control

noncomputable def
    FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics M) :
    FiniteTheorem3ModelAConcretePaperRadiusEventualEscapeSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_accumulated_projection_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases D.eventual_finiteDot_drift
        hC hContinuous hResponse hConverges hneConcrete with
      ⟨N, c, hc, hdrift⟩
    rcases D.finiteDot_fluctuation_eventual_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨fluctuationBound, T, hfluctuation⟩
    refine ⟨N + T, c, -fluctuationBound, hc, ?_⟩
    intro n
    let a : Coord → ℝ :=
      finiteTheorem3DirectionalField M.weight M.utilityGradient xstar
    let trajectory : ℕ → Coord → ℝ :=
      fun t => E.trajectory SourceNorm.l2 VoterResponseModel.modelA t
    let expected : ℕ → ℝ :=
      fun m =>
        ∑ t ∈ Finset.range m,
          ilvRadius D.r0 (t + 1) *
            finiteDot a
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N)))
    have hfluctuation_tail := hfluctuation (n + T) (Nat.le_add_left T n)
    have hlower_expected :
        c * (∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1)) ≤
          expected (n + T) := by
      simpa [expected, trajectory, a] using
        finiteDot_expected_sum_lower_bound_of_drift_sequence
          (r0 := D.r0) (c := c)
          (b := fun t =>
            finiteDot a
              (finiteTheorem3DirectionalField M.weight M.utilityGradient
                (trajectory (t + N))))
          D.r0_pos hdrift (n + T)
    have hsum_mono :
        (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          ∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1) :=
      ilvRadius_sum_range_mono_add D.r0_pos n T
    have hscaled_mono :
        c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          c * (∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1)) := by
      exact mul_le_mul_of_nonneg_left hsum_mono (le_of_lt hc)
    have htarget_tail :
        -fluctuationBound +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (trajectory ((n + T) + N)) := by
      calc
        -fluctuationBound +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1))
            ≤
              -fluctuationBound +
                c * (∑ t ∈ Finset.range (n + T),
                  ilvRadius D.r0 (t + 1)) := by
              linarith
        _ ≤ -fluctuationBound + expected (n + T) := by
              linarith
        _ = expected (n + T) - fluctuationBound := by
              ring
        _ ≤ theorem3ConcreteFiniteFieldProjection M xstar
              (trajectory ((n + T) + N)) := by
              simpa [expected, trajectory, a] using hfluctuation_tail
    simpa [trajectory, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      htarget_tail

noncomputable def
    FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics M) :
    FiniteTheorem3ModelAConcretePaperRadiusEventualEscapeSemantics M :=
  FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    (FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics.toEventualHoeffdingShellSemantics
      D)

noncomputable def
    FiniteTheorem3ModelAConcreteHarmonicEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D :
      FiniteTheorem3ModelAConcreteHarmonicEventualHoeffdingShellSemantics M) :
    FiniteTheorem3ModelAConcretePaperRadiusEventualEscapeSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_accumulated_projection_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases
        finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges_model
          M (D.coordinate_continuity hContinuous) hConverges hneConcrete with
      ⟨N, c, hc, hdrift⟩
    rcases D.harmonic_fluctuation_eventual_control
        (xstar := xstar) (N := N) (c := c)
        hC hContinuous hResponse hConverges hneConcrete hc hdrift with
      ⟨fluctuationBound, T, hfluctuation⟩
    refine ⟨N + T, c / 2, -fluctuationBound, by linarith, ?_⟩
    intro n
    have hfluctuation_tail := hfluctuation (n + T) (Nat.le_add_left T n)
    have hsum_mono :
        (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          ∑ t ∈ Finset.range (n + T), ilvRadius D.r0 (t + 1) :=
      ilvRadius_sum_range_mono_add D.r0_pos n T
    have hscaled_mono :
        (c / 2) * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          (c / 2) * (∑ t ∈ Finset.range (n + T),
            ilvRadius D.r0 (t + 1)) := by
      exact mul_le_mul_of_nonneg_left hsum_mono (by linarith)
    have htarget_tail :
        -fluctuationBound +
            (c / 2) *
              (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA
              ((n + T) + N)) := by
      calc
        -fluctuationBound +
            (c / 2) *
              (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1))
            ≤
              -fluctuationBound +
                (c / 2) *
                  (∑ t ∈ Finset.range (n + T),
                    ilvRadius D.r0 (t + 1)) := by
              linarith
        _ =
            (c / 2) *
              (∑ t ∈ Finset.range (n + T),
                ilvRadius D.r0 (t + 1)) -
                fluctuationBound := by
              ring
        _ ≤ theorem3ConcreteFiniteFieldProjection M xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelA
                ((n + T) + N)) := hfluctuation_tail
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htarget_tail

noncomputable def
    FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics.toPaperNeighborhoodEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics M) :
    FiniteTheorem3ConcretePaperNeighborhoodEscapeSemantics M :=
  FiniteTheorem3ConcreteCoordinateEscapeSemantics.toPaperNeighborhoodEscapeSemantics
    (FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics.toCoordinateEscapeSemantics D)

noncomputable def
    FiniteTheorem3ConcretePaperRadiusProgressSemantics.toPaperRadiusEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcretePaperRadiusProgressSemantics M) :
    FiniteTheorem3ConcretePaperRadiusEscapeSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  accumulated_projection_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases D.one_step_projection_progress
        hC hContinuous hResponse hConverges hneConcrete with
      ⟨c, hc, hstep⟩
    refine
      ⟨c,
        theorem3ConcreteFiniteFieldProjection M xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB 0),
        hc, ?_⟩
    intro n
    exact
      scalar_accumulated_drift_lower_bound_of_one_step
        (s := fun n =>
          theorem3ConcreteFiniteFieldProjection M xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
        (radiusTail := fun t => ilvRadius D.r0 (t + 1))
        (c := c) hstep n

noncomputable def
    FiniteTheorem3ConcretePaperRadiusEscapeSemantics.toPaperRadiusEventualEscapeSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcretePaperRadiusEscapeSemantics M) :
    FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics M where
  r0 := D.r0
  r0_pos := D.r0_pos
  eventual_accumulated_projection_escape := by
    intro xstar hC hContinuous hResponse hConverges hneConcrete
    rcases D.accumulated_projection_escape
        hC hContinuous hResponse hConverges hneConcrete with
      ⟨c, baseValue, hc, hlower⟩
    exact ⟨0, c, baseValue, hc, by
      intro n
      simpa using hlower n⟩

noncomputable def
    FiniteTheorem3ConcretePaperRadiusProgressSemantics.toPaperRadiusProgressSemantics
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {M : FiniteTheorem3DirectionalFieldModel E}
    (D : FiniteTheorem3ConcretePaperRadiusProgressSemantics M) :
    FiniteTheorem3PaperRadiusProgressSemantics E where
  r0 := D.r0
  r0_pos := D.r0_pos
  one_step_projection_progress := by
    intro xstar hC hContinuous hResponse hConverges hne
    have hneConcrete :
        (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
          fun _ => (0 : ℝ)) := by
      intro hzero
      apply hne
      calc
        E.directionalField xstar =
            finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
              rw [M.directionalField_eq]
        _ = (fun _ => 0) := hzero
        _ = E.zeroDirection := by
              rw [M.zeroDirection_eq]
    rcases D.one_step_projection_progress
        hC hContinuous hResponse hConverges hneConcrete with
      ⟨c, hc, hstep⟩
    refine ⟨c, hc, ?_⟩
    intro t
    simpa [theorem3ConcreteFiniteFieldProjection_eq M] using hstep t

noncomputable def FiniteTheorem3PaperRadiusDriftSemantics.toOneStepDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3PaperRadiusDriftSemantics E) :
    FiniteTheorem3OneStepDriftSemantics E where
  radiusTail := fun _xstar t => ilvRadius D.r0 (t + 1)
  radiusTail_partial_sums_tendsto_atTop := by
    intro _xstar
    exact ilvRadius_sum_tendsto_atTop D.r0_pos
  projection_converges := D.projection_converges
  one_step_projection_progress := D.one_step_projection_progress

noncomputable def FiniteTheorem3OneStepDriftSemantics.toAnalyticDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3OneStepDriftSemantics E) :
    FiniteTheorem3AnalyticDriftSemantics E where
  radiusTail := D.radiusTail
  radiusTail_partial_sums_tendsto_atTop :=
    D.radiusTail_partial_sums_tendsto_atTop
  projection_converges := D.projection_converges
  nonzero_drift_accumulates := by
    intro xstar hC hContinuous hResponse hConverges hne
    rcases D.one_step_projection_progress
        hC hContinuous hResponse hConverges hne with
      ⟨c, hc, hstep⟩
    refine
      ⟨c,
        theorem3FiniteFieldProjection E xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB 0),
        hc, ?_⟩
    intro n
    exact
      scalar_accumulated_drift_lower_bound_of_one_step
        (s := fun n =>
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
        (radiusTail := D.radiusTail xstar)
        (c := c) hstep n

noncomputable def FiniteTheorem3AnalyticDriftSemantics.toAnalyticDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3AnalyticDriftSemantics E) :
    Theorem3AnalyticDriftSemantics E where
  radiusTail := D.radiusTail
  projection := theorem3FiniteFieldProjection E
  radiusTail_partial_sums_tendsto_atTop :=
    D.radiusTail_partial_sums_tendsto_atTop
  projection_converges := D.projection_converges
  nonzero_drift_accumulates := D.nonzero_drift_accumulates

/--
Theorem 3 drift certificate.  It isolates the deterministic contradiction left
after convergence of a Model B `L2` trajectory is known: a nonzero limiting
directional field is incompatible with convergence.
-/
structure ConvergentModelBDriftCertificate
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (xstar : Point) where
  hC : ConditionsC123 E
  hContinuous : E.directionalFieldUniformlyContinuous
  hResponse : E.respondsAccordingTo VoterResponseModel.modelB
  hConverges :
    ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar
  nonzero_drift_contradiction :
    E.directionalField xstar ≠ E.zeroDirection → False

theorem ConvergentModelBDriftCertificate.isDirectionalEquilibrium
    {Voter Point : Type*}
    {E : ILVEnvironment Voter Point} {xstar : Point}
    (C : ConvergentModelBDriftCertificate E xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  exact C.nonzero_drift_contradiction hne

/--
Deterministic bridge for Theorem 3 after trajectory convergence is known.

The future stochastic approximation layer may establish convergence of the
Model B trajectory.  This bridge isolates the separate deterministic drift
argument: every convergent Model B `L2` trajectory has a drift certificate, and
therefore its limit is a directional equilibrium.
-/
structure Theorem3DeterministicBridge
    {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop where
  drift_certificate :
    ∀ {xstar : Point},
      ConditionsC123 E →
        E.directionalFieldUniformlyContinuous →
          E.respondsAccordingTo VoterResponseModel.modelB →
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              ConvergentModelBDriftCertificate E xstar

theorem theorem3DeterministicBridge_of_analyticDriftSemantics
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (A : Theorem3AnalyticDriftSemantics E) :
    Theorem3DeterministicBridge E := by
  refine ⟨?_⟩
  intro xstar hC hContinuous hResponse hConverges
  refine
    { hC := hC
      hContinuous := hContinuous
      hResponse := hResponse
      hConverges := hConverges
      nonzero_drift_contradiction := ?_ }
  intro hne
  rcases A.nonzero_drift_accumulates hC hContinuous hResponse hConverges hne with
    ⟨c, baseValue, hc, hlower⟩
  exact scalar_convergence_contradiction_of_accumulated_drift
    (s := fun n =>
      A.projection xstar
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
    (limit := A.projection xstar xstar)
    (base := baseValue)
    (c := c)
    (radiusTail := A.radiusTail xstar)
    hc
    (A.radiusTail_partial_sums_tendsto_atTop xstar)
    hlower
    (A.projection_converges hConverges)

theorem theorem3DeterministicBridge_of_finiteOneStepDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3OneStepDriftSemantics E) :
    Theorem3DeterministicBridge E := by
  exact theorem3DeterministicBridge_of_analyticDriftSemantics
    (FiniteTheorem3AnalyticDriftSemantics.toAnalyticDriftSemantics
      (FiniteTheorem3OneStepDriftSemantics.toAnalyticDriftSemantics D))

theorem theorem3DeterministicBridge_of_finitePaperRadiusDriftSemantics
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3PaperRadiusDriftSemantics E) :
    Theorem3DeterministicBridge E := by
  exact theorem3DeterministicBridge_of_finiteOneStepDriftSemantics
    (FiniteTheorem3PaperRadiusDriftSemantics.toOneStepDriftSemantics D)

theorem theorem3_finite_directionalEquilibrium_of_paperRadiusProgress
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3PaperRadiusProgressSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  rcases D.one_step_projection_progress
      hC hContinuous hResponse hConverges hne with
    ⟨c, hc, hstep⟩
  have hlower :
      ∀ n : ℕ,
        theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB 0) +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n) := by
    intro n
    exact
      scalar_accumulated_drift_lower_bound_of_one_step
        (s := fun n =>
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
        (radiusTail := fun t => ilvRadius D.r0 (t + 1))
        (c := c) hstep n
  exact scalar_convergence_contradiction_of_accumulated_drift
    (s := fun n =>
      theorem3FiniteFieldProjection E xstar
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n))
    (limit := theorem3FiniteFieldProjection E xstar xstar)
    (base := theorem3FiniteFieldProjection E xstar
      (E.trajectory SourceNorm.l2 VoterResponseModel.modelB 0))
    (c := c)
    (radiusTail := fun t => ilvRadius D.r0 (t + 1))
    hc
    (ilvRadius_sum_tendsto_atTop D.r0_pos)
    hlower
    (theorem3FiniteFieldProjection_tendsto hConverges)

/--
Model A analogue of the finite-coordinate paper-radius endpoint: once the
Model A trace supplies the same positive scalar progress along any nonzero
limiting field direction, convergence forces the limit to be a directional
equilibrium.
-/
theorem theorem3_modelA_finite_directionalEquilibrium_of_paperRadiusProgress
    {Voter Coord : Type*} [Fintype Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (D : FiniteTheorem3ModelAPaperRadiusProgressSemantics E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  rcases D.one_step_projection_progress
      hC hContinuous hResponse hConverges hne with
    ⟨c, hc, hstep⟩
  have hlower :
      ∀ n : ℕ,
        theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA 0) +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA n) := by
    intro n
    exact
      scalar_accumulated_drift_lower_bound_of_one_step
        (s := fun n =>
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA n))
        (radiusTail := fun t => ilvRadius D.r0 (t + 1))
        (c := c) hstep n
  exact scalar_convergence_contradiction_of_accumulated_drift
    (s := fun n =>
      theorem3FiniteFieldProjection E xstar
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelA n))
    (limit := theorem3FiniteFieldProjection E xstar xstar)
    (base := theorem3FiniteFieldProjection E xstar
      (E.trajectory SourceNorm.l2 VoterResponseModel.modelA 0))
    (c := c)
    (radiusTail := fun t => ilvRadius D.r0 (t + 1))
    hc
    (ilvRadius_sum_tendsto_atTop D.r0_pos)
    hlower
    (theorem3FiniteFieldProjection_tendsto_model hConverges)

theorem theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusEventualEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  have hneConcrete :
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) := by
    intro hzero
    apply hne
    calc
      E.directionalField xstar =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
            rw [M.directionalField_eq]
      _ = (fun _ => 0) := hzero
      _ = E.zeroDirection := by
            rw [M.zeroDirection_eq]
  rcases D.eventual_accumulated_projection_escape
      hC hContinuous hResponse hConverges hneConcrete with
    ⟨N, c, baseValue, hc, hlowerConcrete⟩
  have hlower :
      ∀ n : ℕ,
        baseValue +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N)) := by
    intro n
    simpa [theorem3ConcreteFiniteFieldProjection_eq M] using
      hlowerConcrete n
  exact scalar_convergence_contradiction_of_accumulated_drift
    (s := fun n =>
      theorem3FiniteFieldProjection E xstar
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelB (n + N)))
    (limit := theorem3FiniteFieldProjection E xstar xstar)
    (base := baseValue)
    (c := c)
    (radiusTail := fun t => ilvRadius D.r0 (t + 1))
    hc
    (ilvRadius_sum_tendsto_atTop D.r0_pos)
    hlower
    (theorem3FiniteFieldProjection_tendsto_nat_add hConverges N)

/--
Corrected Model A analogue of the concrete paper-radius eventual-escape
endpoint.  Once the Model A trace has the same eventual scalar escape property
as the Model B proof, convergence forces the normalized-gradient field at the
limit to vanish.
-/
theorem theorem3_modelA_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ModelAConcretePaperRadiusEventualEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  have hneConcrete :
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) := by
    intro hzero
    apply hne
    calc
      E.directionalField xstar =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
            rw [M.directionalField_eq]
      _ = (fun _ => 0) := hzero
      _ = E.zeroDirection := by
            rw [M.zeroDirection_eq]
  rcases D.eventual_accumulated_projection_escape
      hC hContinuous hResponse hConverges hneConcrete with
    ⟨N, c, baseValue, hc, hlowerConcrete⟩
  have hlower :
      ∀ n : ℕ,
        baseValue +
            c * (∑ t ∈ Finset.range n, ilvRadius D.r0 (t + 1)) ≤
          theorem3FiniteFieldProjection E xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA (n + N)) := by
    intro n
    simpa [theorem3ConcreteFiniteFieldProjection_eq M] using
      hlowerConcrete n
  exact scalar_convergence_contradiction_of_accumulated_drift
    (s := fun n =>
      theorem3FiniteFieldProjection E xstar
        (E.trajectory SourceNorm.l2 VoterResponseModel.modelA (n + N)))
    (limit := theorem3FiniteFieldProjection E xstar xstar)
    (base := baseValue)
    (c := c)
    (radiusTail := fun t => ilvRadius D.r0 (t + 1))
    hc
    (ilvRadius_sum_tendsto_atTop D.r0_pos)
    hlower
    (theorem3FiniteFieldProjection_tendsto_model_nat_add hConverges N)

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotEventualHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    M
    (FiniteTheorem3ConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

/--
Corrected Model A analogue of the finite-dot eventual Hoeffding endpoint.  This
is the theorem-level target for the post-Theorem-3 conjecture after adding the
necessary first-order/non-flat-tail assumptions to prove the Model A shell.
-/
theorem theorem3_modelA_finite_directionalEquilibrium_of_concreteFiniteDotEventualHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_modelA_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
      M
      (FiniteTheorem3ModelAConcreteFiniteDotEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
        D)
      hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    M
    (FiniteTheorem3ConcreteFiniteDotHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_modelA_finite_directionalEquilibrium_of_concreteFiniteDotHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_modelA_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
      M
    (FiniteTheorem3ModelAConcreteFiniteDotHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
        D)
      hC hContinuous hResponse hConverges

theorem theorem3_modelA_finite_directionalEquilibrium_of_concreteHarmonicEventualHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D :
      FiniteTheorem3ModelAConcreteHarmonicEventualHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact
    theorem3_modelA_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
      M
      (FiniteTheorem3ModelAConcreteHarmonicEventualHoeffdingShellSemantics.toPaperRadiusEventualEscapeSemantics
        D)
      hC hContinuous hResponse hConverges

/--
Corrected Model A endpoint with the original global Algorithm 2 tail radius.
This is stronger than the reset-tail harmonic shell: the stochastic tail after
time `N` uses `ilvTailRadius r0 N t = r0 / (t + N + 1)`.
-/
theorem theorem3_modelA_finite_directionalEquilibrium_of_concreteGlobalHarmonicEventualHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D :
      FiniteTheorem3ModelAConcreteGlobalHarmonicEventualHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelA xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  have hneConcrete :
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) := by
    intro hzero
    apply hne
    calc
      E.directionalField xstar =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
            rw [M.directionalField_eq]
      _ = (fun _ => 0) := hzero
      _ = E.zeroDirection := by
            rw [M.zeroDirection_eq]
  rcases
      finiteTheorem3DirectionalField_eventual_finiteDot_drift_of_converges_model
        M (D.coordinate_continuity hContinuous) hConverges hneConcrete with
    ⟨N, c, hc, hdrift⟩
  rcases D.global_harmonic_fluctuation_eventual_control
      (xstar := xstar) (N := N) (c := c)
      hC hContinuous hResponse hConverges hneConcrete hc hdrift with
    ⟨fluctuationBound, T, hfluctuation⟩
  let d : ℝ := c / 2
  have hd : 0 < d := by
    dsimp [d]
    linarith
  have htail_lower :
      ∀ n : ℕ,
        (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          ∑ t ∈ Finset.range (n + T), ilvTailRadius D.r0 N t := by
    intro n
    have hprefix_nonneg :
        0 ≤ ∑ t ∈ Finset.range T, ilvTailRadius D.r0 N t := by
      exact Finset.sum_nonneg fun t _ht =>
        ilvTailRadius_nonneg (le_of_lt D.r0_pos) N t
    have htail_eq :
        (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) =
          ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) := by
      apply Finset.sum_congr rfl
      intro t _ht
      simp [ilvTailRadius, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    calc
      (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t)
          =
            ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) :=
            htail_eq
      _ ≤
            (∑ t ∈ Finset.range T, ilvTailRadius D.r0 N t) +
              ∑ t ∈ Finset.range n, ilvTailRadius D.r0 N (T + t) := by
            linarith
      _ =
            ∑ t ∈ Finset.range (T + n), ilvTailRadius D.r0 N t := by
            rw [Finset.sum_range_add]
      _ =
            ∑ t ∈ Finset.range (n + T), ilvTailRadius D.r0 N t := by
            rw [Nat.add_comm]
  have hlower :
      ∀ n : ℕ,
        -fluctuationBound +
            d * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA
              (n + (N + T))) := by
    intro n
    let m : ℕ := n + T
    have hm_ge_T : T ≤ m := by
      dsimp [m]
      exact Nat.le_add_left T n
    have hfluctuation_m := hfluctuation m hm_ge_T
    have hscaled_tail :
        d * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          d * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) := by
      have htail := htail_lower n
      simpa [d, m] using mul_le_mul_of_nonneg_left htail (le_of_lt hd)
    have htarget :
        -fluctuationBound +
            d * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t) ≤
          theorem3ConcreteFiniteFieldProjection M xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA (m + N)) := by
      calc
        -fluctuationBound +
            d * (∑ t ∈ Finset.range n, ilvTailRadius D.r0 (N + T) t)
            ≤
              -fluctuationBound +
                d * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) := by
              linarith
        _ =
            d * (∑ t ∈ Finset.range m, ilvTailRadius D.r0 N t) -
              fluctuationBound := by
              ring
        _ ≤ theorem3ConcreteFiniteFieldProjection M xstar
              (E.trajectory SourceNorm.l2 VoterResponseModel.modelA (m + N)) := by
              simpa [d] using hfluctuation_m
    simpa [m, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htarget
  have hproj_tendsto :
      Filter.Tendsto
        (fun n : ℕ =>
          theorem3ConcreteFiniteFieldProjection M xstar
            (E.trajectory SourceNorm.l2 VoterResponseModel.modelA
              (n + (N + T))))
        Filter.atTop
        (nhds (theorem3ConcreteFiniteFieldProjection M xstar xstar)) := by
    simpa [theorem3ConcreteFiniteFieldProjection_eq M,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      theorem3FiniteFieldProjection_tendsto_model_nat_add
        (E := E) (xstar := xstar) hConverges (N + T)
  exact
    scalar_convergence_contradiction_of_accumulated_drift
      (s := fun n =>
        theorem3ConcreteFiniteFieldProjection M xstar
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelA
            (n + (N + T))))
      (limit := theorem3ConcreteFiniteFieldProjection M xstar xstar)
      (base := -fluctuationBound)
      (c := d)
      (radiusTail := fun t => ilvTailRadius D.r0 (N + T) t)
      hd
      (ilvTailRadius_sum_tendsto_atTop D.r0_pos (N + T))
      hlower
      hproj_tendsto

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotSampledRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotHoeffdingShell
    M
    (FiniteTheorem3ConcreteFiniteDotSampledRawHoeffdingSemantics.toFiniteDotHoeffdingShellSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotExactSampledRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotSampledRawHoeffding
    M
    (FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics.toSampledRawHoeffdingSemantics
      (FiniteTheorem3ConcreteFiniteDotExactSampledRawHoeffdingSemantics.toProjectedRawHoeffdingSemantics
        D))
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotSampledRawHoeffding
    M
    (FiniteTheorem3ConcreteFiniteDotProjectedRawHoeffdingSemantics.toSampledRawHoeffdingSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedResidualHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedRawHoeffding
    M
    (FiniteTheorem3ConcreteFiniteDotProjectedResidualHoeffdingSemantics.toProjectedRawHoeffdingSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedTracePathwise
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteFiniteDotProjectedResidualHoeffding
    M
    (FiniteTheorem3ConcreteFiniteDotProjectedTracePathwiseSemantics.toProjectedResidualHoeffdingSemantics
      D)
    hC hContinuous hResponse hConverges

/--
Theorem 3 from the paper's neighborhood-escape shape.  Finite-coordinate
convergence eventually keeps the trajectory inside any positive `L2` ball around
`x*`; the escape property supplies a later iterate outside a half-radius ball,
contradicting convergence.
-/
theorem theorem3_finite_directionalEquilibrium_of_concretePaperNeighborhoodEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperNeighborhoodEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  unfold IsDirectionalEquilibrium
  by_contra hne
  have hneConcrete :
      (finiteTheorem3DirectionalField M.weight M.utilityGradient xstar ≠
        fun _ => (0 : ℝ)) := by
    intro hzero
    apply hne
    calc
      E.directionalField xstar =
          finiteTheorem3DirectionalField M.weight M.utilityGradient xstar := by
            rw [M.directionalField_eq]
      _ = (fun _ => 0) := hzero
      _ = E.zeroDirection := by
            rw [M.zeroDirection_eq]
  rcases D.neighborhood_escape hC hContinuous hResponse hConverges hneConcrete with
    ⟨δ, hδpos, hescape⟩
  let δ₂ : ℝ := δ / 2
  have hδ₂pos : 0 < δ₂ := by
    dsimp [δ₂]
    linarith
  have hδ₂lt : δ₂ < δ := by
    dsimp [δ₂]
    linarith
  have hdist_tendsto :=
    finiteCoordinateILVTrajectory_l2Distance_tendsto_zero hConverges
  have heventually_close :
      ∀ᶠ n in Filter.atTop,
        finiteCoordinateDistance SourceNorm.l2
          (E.trajectory SourceNorm.l2 VoterResponseModel.modelB n)
          xstar < δ₂ :=
    hdist_tendsto.eventually (eventually_lt_nhds hδ₂pos)
  rcases Filter.eventually_atTop.1 heventually_close with ⟨T, hT⟩
  rcases hescape δ₂ hδ₂pos hδ₂lt T with ⟨τ, hTτ, hfar⟩
  have hclose := hT τ hTτ
  linarith

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperNeighborhoodEscape
    M
    (FiniteTheorem3ConcreteCoordinateEscapeSemantics.toPaperNeighborhoodEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateDriftEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    M
    (FiniteTheorem3ConcreteCoordinateDriftEscapeSemantics.toCoordinateEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateAccumulation
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateAccumulationSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateDriftEscape
    M
    (FiniteTheorem3ConcreteCoordinateAccumulationSemantics.toCoordinateDriftEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateStepProgress
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateStepProgressSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateAccumulation
    M
    (FiniteTheorem3ConcreteCoordinateStepProgressSemantics.toCoordinateAccumulationSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateExpectedFluctuation
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateAccumulation
    M
    (FiniteTheorem3ConcreteCoordinateExpectedFluctuationSemantics.toCoordinateAccumulationSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateAccumulation
    M
    (FiniteTheorem3ConcreteCoordinateHoeffdingShellSemantics.toCoordinateAccumulationSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateEventualHoeffdingShell
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    M
    (FiniteTheorem3ConcreteCoordinateEventualHoeffdingShellSemantics.toCoordinateEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateSampledRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    M
    (FiniteTheorem3ConcreteCoordinateSampledRawHoeffdingSemantics.toCoordinateEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concreteCoordinateProjectedRawHoeffding
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concreteCoordinateEscape
    M
    (FiniteTheorem3ConcreteCoordinateProjectedRawHoeffdingSemantics.toCoordinateEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEscape
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusEscapeSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEventualEscape
    M
    (FiniteTheorem3ConcretePaperRadiusEscapeSemantics.toPaperRadiusEventualEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

theorem theorem3_finite_directionalEquilibrium_of_concretePaperRadiusProgress
    {Voter Coord : Type*} [Fintype Voter] [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteTheorem3DirectionalFieldModel E)
    (D : FiniteTheorem3ConcretePaperRadiusProgressSemantics M)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Coord → ℝ}
    (hConverges :
      FiniteCoordinateILVTrajectoryConvergesTo E SourceNorm.l2
        VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar := by
  exact theorem3_finite_directionalEquilibrium_of_concretePaperRadiusEscape
    M
    (FiniteTheorem3ConcretePaperRadiusProgressSemantics.toPaperRadiusEscapeSemantics
      D)
    hC hContinuous hResponse hConverges

/-- Exact paper-facing formula for Theorem 1. -/
def theorem1Statement {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ p q model,
    ConditionsC123 E →
      IsLpNormedUtilities E p →
        (model = VoterResponseModel.modelA ∨ model = VoterResponseModel.modelB) →
          E.respondsAccordingTo model →
            Theorem1NormPair p q →
              ILVConvergesToSocietalOptimal E q model

theorem theorem1Statement_l2_l2_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l2)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelA :=
  h SourceNorm.l2 SourceNorm.l2 VoterResponseModel.modelA
    hC hUtil (Or.inl rfl) hResponse theorem1NormPair_l2_l2

theorem theorem1Statement_l2_l2_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l2)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelB :=
  h SourceNorm.l2 SourceNorm.l2 VoterResponseModel.modelB
    hC hUtil (Or.inr rfl) hResponse theorem1NormPair_l2_l2

theorem theorem1Statement_l1_linf_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.linfty VoterResponseModel.modelA :=
  h SourceNorm.l1 SourceNorm.linfty VoterResponseModel.modelA
    hC hUtil (Or.inl rfl) hResponse theorem1NormPair_l1_linf

theorem theorem1Statement_l1_linf_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.l1)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.linfty VoterResponseModel.modelB :=
  h SourceNorm.l1 SourceNorm.linfty VoterResponseModel.modelB
    hC hUtil (Or.inr rfl) hResponse theorem1NormPair_l1_linf

theorem theorem1Statement_linf_l1_modelA
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l1 VoterResponseModel.modelA :=
  h SourceNorm.linfty SourceNorm.l1 VoterResponseModel.modelA
    hC hUtil (Or.inl rfl) hResponse theorem1NormPair_linf_l1

theorem theorem1Statement_linf_l1_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem1Statement E)
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E SourceNorm.linfty)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l1 VoterResponseModel.modelB :=
  h SourceNorm.linfty SourceNorm.l1 VoterResponseModel.modelB
    hC hUtil (Or.inr rfl) hResponse theorem1NormPair_linf_l1

/--
Case certificate for the theorem-shaped Theorem 1 SSGM interface.  It packages
the source hypotheses for one norm/model branch so the future convergence
theorem can consume a structured input rather than the final paper endpoint.
-/
structure Theorem1SSGMCaseCertificate {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p q : SourceNorm)
    (model : VoterResponseModel) : Prop where
  conditions : ConditionsC123 E
  utilities : IsLpNormedUtilities E p
  model_choice :
    model = VoterResponseModel.modelA ∨
      model = VoterResponseModel.modelB
  response : E.respondsAccordingTo model
  norm_pair : Theorem1NormPair p q

/--
Deterministic source-semantics bridge for Theorem 1.  It converts the visible
source hypotheses for each branch into the structured case certificate consumed
by the future SSGM theorem.
-/
structure Theorem1SourceToSSGMBridge {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop where
  case_certificate :
    ∀ {p q model},
      ConditionsC123 E →
        IsLpNormedUtilities E p →
          (model = VoterResponseModel.modelA ∨
            model = VoterResponseModel.modelB) →
            E.respondsAccordingTo model →
              Theorem1NormPair p q →
                Theorem1SSGMCaseCertificate E p q model

/--
The theorem-shaped SSGM boundary for Theorem 1.  A reusable convergence theorem
should prove this record from stochastic approximation hypotheses, then the
paper statement follows without assuming `theorem1Statement` directly.
-/
structure Theorem1SSGMConvergenceTheorem {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop where
  converges :
    ∀ {p q model},
      Theorem1SSGMCaseCertificate E p q model →
        ILVConvergesToSocietalOptimal E q model

theorem theorem1Statement_of_sourceBridge_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Theorem1SourceToSSGMBridge E)
    (hSSGM : Theorem1SSGMConvergenceTheorem E) :
    theorem1Statement E := by
  intro p q model hC hUtil hmodel hResponse hpq
  exact hSSGM.converges
    (hSource.case_certificate hC hUtil hmodel hResponse hpq)

/-- Exact paper-facing formula for Theorem 2. -/
def theorem2Statement {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ p q,
    ConditionsC123 E →
      IsLpNormedUtilities E (SourceNorm.lp p) →
        E.respondsAccordingTo VoterResponseModel.modelB →
          HolderDualFinite p q →
            ILVConvergesToSocietalOptimal E (SourceNorm.lp q) VoterResponseModel.modelB

theorem theorem2Statement_modelB
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem2Statement E)
    {p q : ℝ}
    (hC : ConditionsC123 E)
    (hUtil : IsLpNormedUtilities E (SourceNorm.lp p))
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    (hdual : HolderDualFinite p q) :
    ILVConvergesToSocietalOptimal E (SourceNorm.lp q) VoterResponseModel.modelB :=
  h p q hC hUtil hResponse hdual

/--
Deterministic source-semantics bridge needed before applying the future Theorem
2 stochastic approximation theorem.

For finite-coordinate environments, this is the non-stochastic statement that
source C1-C3, Definition 1 utilities, Model B response semantics, and
Holder-duality construct the concrete finite SSGM certificate.
-/
structure Theorem2SourceToFiniteSSGMBridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  finite_bridge :
    ∀ {p q : ℝ},
      ConditionsC123 E →
        IsLpNormedUtilities E (SourceNorm.lp p) →
          E.respondsAccordingTo VoterResponseModel.modelB →
            HolderDualFinite p q →
              Theorem2FiniteSSGMBridge E p q

/--
Deterministic source semantics needed to construct Theorem 2's finite SSGM
input package.  This record is intentionally non-stochastic: it interprets the
paper's finite-dimensional norm, C3 full-space bounded-density data, initial radius, and
Model B Algorithm 1 trace before the SSGM convergence theorem is invoked.
-/
structure Theorem2SourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  hNorm : UsesFiniteCoordinateNormDistance E
  c3Data : FiniteCoordinateIdealDistributionData Coord
  modelB_trace :
    ∀ {p q : ℝ},
      IsLpNormedUtilities E (SourceNorm.lp p) →
        E.respondsAccordingTo VoterResponseModel.modelB →
          HolderDualFinite p q →
            FiniteModelBILVAlgorithm1TraceSource E p q r0

/--
More primitive Theorem 2 source semantics.  The Model B Algorithm 1 trace is
given with coordinate noncollision, matching the paper's Lemma 3/C3
non-equality condition; the bad-event trace source is derived from it.
-/
structure Theorem2PrimitiveSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  hNorm : UsesFiniteCoordinateNormDistance E
  c3Data : FiniteCoordinateIdealDistributionData Coord
  modelB_primitive_trace :
    ∀ {p q : ℝ},
      IsLpNormedUtilities E (SourceNorm.lp p) →
        E.respondsAccordingTo VoterResponseModel.modelB →
          HolderDualFinite p q →
            FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0

def theorem2SourceSemantics_of_primitive
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2PrimitiveSourceSemantics E) :
    Theorem2SourceSemantics E where
  r0 := S.r0
  r0_pos := S.r0_pos
  hNorm := S.hNorm
  c3Data := S.c3Data
  modelB_trace hUtil hResponse hdual :=
    finiteModelBILVAlgorithm1TraceSource_of_primitive
      (S.modelB_primitive_trace hUtil hResponse hdual)

def theorem2SourceToFiniteSSGMBridge_of_semantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E) :
    Theorem2SourceToFiniteSSGMBridge E where
  finite_bridge hC hUtil hResponse hdual :=
    { r0 := S.r0
      r0_pos := S.r0_pos
      hNorm := S.hNorm
      c3 := FiniteCoordinateC3Carrier.of_conditions S.c3Data hC
      trace := finiteModelBILVTrace_of_source
        (finiteModelBILVTraceSource_of_algorithm1TraceSource hdual
          (S.modelB_trace hUtil hResponse hdual)) }

/--
The theorem-shaped SSGM boundary for Theorem 2 once deterministic source
semantics have produced a `Theorem2FiniteSSGMBridge`.

This is the local interface a reusable library stochastic subgradient theorem
should eventually discharge; it consumes finite SSGM inputs instead of assuming
the final Theorem 2 endpoint directly.
-/
structure Theorem2SSGMConvergenceTheorem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop where
  converges :
    ∀ {p q : ℝ},
      HolderDualFinite p q →
        Theorem2FiniteSSGMBridge E p q →
          ILVConvergesToSocietalOptimal E (SourceNorm.lp q)
            VoterResponseModel.modelB

theorem theorem2Statement_of_sourceBridge_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Theorem2SourceToFiniteSSGMBridge E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  intro p q hC hUtil hResponse hdual
  exact hSSGM.converges hdual
    (hSource.finite_bridge hC hUtil hResponse hdual)

theorem theorem2Statement_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Theorem2SourceSemantics E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceBridge_ssgmConvergence
    (theorem2SourceToFiniteSSGMBridge_of_semantics S) hSSGM

/-- Exact paper-facing formula for Proposition 1. -/
def proposition1Statement {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ (Component : Type),
    ConditionsC123 E →
      (∃ W : WeightedEuclideanStructure Voter Point Component,
        IsWeightedEuclideanUtilitiesWith E W) →
        ∀ model,
          (model = VoterResponseModel.modelA ∨ model = VoterResponseModel.modelB) →
            E.respondsAccordingTo model →
              ILVConvergesToSocietalOptimal E SourceNorm.l2 model

theorem proposition1Statement_modelA
    {Voter Point : Type*} {Component : Type} {E : ILVEnvironment Voter Point}
    (h : proposition1Statement E)
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter Point Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelA :=
  h Component hC hWeighted VoterResponseModel.modelA (Or.inl rfl) hResponse

theorem proposition1Statement_modelB
    {Voter Point : Type*} {Component : Type} {E : ILVEnvironment Voter Point}
    (h : proposition1Statement E)
    (hC : ConditionsC123 E)
    (hWeighted :
      ∃ W : WeightedEuclideanStructure Voter Point Component,
        IsWeightedEuclideanUtilitiesWith E W)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToSocietalOptimal E SourceNorm.l2 VoterResponseModel.modelB :=
  h Component hC hWeighted VoterResponseModel.modelB (Or.inr rfl) hResponse

/--
Finite-coordinate deterministic data for Proposition 1 after weighted-Euclidean
source semantics have been converted into an `L2` SSGM recurrence and an
objective whose minimizers are the paper's social optima.
-/
structure Proposition1FiniteSSGMBridge
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (W : WeightedEuclideanStructure Voter (Coord → ℝ) Component)
    (model : VoterResponseModel) where
  r0 : ℝ
  inputs : WeightedEuclideanL2SSGMInputs E W model r0
  objective : WeightedEuclideanSocialObjectiveBridge E W

theorem Proposition1FiniteSSGMBridge.trajectory_mem_solutionSpace
    {Voter Coord Component : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
    {model : VoterResponseModel}
    (B : Proposition1FiniteSSGMBridge E W model) :
    ∀ t : ℕ, E.trajectory SourceNorm.l2 model t ∈ E.solutionSpace :=
  B.inputs.trajectory_mem_solutionSpace

/--
Deterministic source-semantics bridge for Proposition 1.  It constructs the
finite weighted-Euclidean SSGM/objective certificate from the source C1-C3,
weighted-Euclidean utilities, and Model A/B response semantics.
-/
structure Proposition1SourceToFiniteSSGMBridge
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  finite_bridge :
    ∀ {Component : Type},
      ConditionsC123 E →
        (∃ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
          IsWeightedEuclideanUtilitiesWith E W) →
          ∀ model,
              (model = VoterResponseModel.modelA ∨
                model = VoterResponseModel.modelB) →
                E.respondsAccordingTo model →
                  Σ W : WeightedEuclideanStructure Voter (Coord → ℝ) Component,
                  Σ' _hWeightedW : IsWeightedEuclideanUtilitiesWith E W,
                    Proposition1FiniteSSGMBridge E W model

/--
Deterministic source semantics for Proposition 1.  It supplies the
weighted-Euclidean projected SSGM recurrence data and the objective/minimizer
identification for each visible weighted-Euclidean source instance.
-/
structure Proposition1SourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  weighted_l2_inputs :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
        ConditionsC123 E →
          IsWeightedEuclideanUtilitiesWith E W →
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ r0 : ℝ, WeightedEuclideanL2SSGMTraceSource E W model r0
  weighted_objective :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
      ConditionsC123 E →
        IsWeightedEuclideanUtilitiesWith E W →
          WeightedEuclideanSocialObjectiveFormulaSource E W

/--
Primitive component-level source semantics for Proposition 1.  The full
weighted sample-subgradient trace is derived from component subgradients,
nonnegative weighted-Euclidean coefficients, and the projected Algorithm 1
trace fields in `WeightedEuclideanL2ComponentTraceSource`.
-/
structure Proposition1ComponentSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  weighted_l2_component_inputs :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
        ConditionsC123 E →
          IsWeightedEuclideanUtilitiesWith E W →
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ r0 : ℝ, WeightedEuclideanL2ComponentTraceSource E W model r0
  weighted_objective :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
      ConditionsC123 E →
        IsWeightedEuclideanUtilitiesWith E W →
          WeightedEuclideanSocialObjectiveFormulaSource E W

/--
Concrete component-distance source semantics for Proposition 1.  This variant
derives the component subgradient certificates from finite `L2` component
distance formulas before building the component-level source semantics.
-/
structure Proposition1ConcreteComponentSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  weighted_l2_concrete_component_inputs :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
        ConditionsC123 E →
          IsWeightedEuclideanUtilitiesWith E W →
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ r0 : ℝ,
                  WeightedEuclideanL2ConcreteComponentTraceSource E W model r0
  weighted_objective :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
      ConditionsC123 E →
        IsWeightedEuclideanUtilitiesWith E W →
          WeightedEuclideanSocialObjectiveFormulaSource E W

noncomputable def proposition1ComponentSourceSemantics_of_concreteComponentSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ConcreteComponentSourceSemantics E) :
    Proposition1ComponentSourceSemantics E where
  weighted_l2_component_inputs := by
    intro Component W model hC hW hmodel hResponse
    rcases S.weighted_l2_concrete_component_inputs hC hW hmodel hResponse with
      ⟨r0, T⟩
    exact
      ⟨r0, weightedEuclideanL2ComponentTraceSource_of_concreteComponentTraceSource T⟩
  weighted_objective := S.weighted_objective

noncomputable def proposition1SourceSemantics_of_componentSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1ComponentSourceSemantics E) :
    Proposition1SourceSemantics E where
  weighted_l2_inputs := by
    intro Component W model hC hW hmodel hResponse
    rcases S.weighted_l2_component_inputs hC hW hmodel hResponse with
      ⟨r0, T⟩
    exact
      ⟨r0, weightedEuclideanL2SSGMTraceSource_of_componentTraceSource hW T⟩
  weighted_objective := S.weighted_objective

noncomputable def proposition1SourceToFiniteSSGMBridge_of_semantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E) :
    Proposition1SourceToFiniteSSGMBridge E where
  finite_bridge hC hWeighted model hmodel hResponse := by
      let W := Classical.choose hWeighted
      have hW : IsWeightedEuclideanUtilitiesWith E W :=
        Classical.choose_spec hWeighted
      rcases S.weighted_l2_inputs hC hW hmodel hResponse with
        ⟨r0, hInputsTraceSource⟩
      exact
        ⟨W, hW,
          { r0 := r0
            inputs := weightedEuclideanL2SSGMInputs_of_source hW
              (weightedEuclideanL2SSGMSource_of_traceSource hInputsTraceSource)
            objective :=
              weightedEuclideanSocialObjectiveBridge_of_source hW
                (weightedEuclideanSocialObjectiveSource_of_formulaSource
                  (S.weighted_objective hC hW)) }⟩

/--
The theorem-shaped SSGM boundary for Proposition 1 once deterministic source
semantics have produced finite weighted-Euclidean SSGM/objective data.
-/
structure Proposition1SSGMConvergenceTheorem
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop where
  converges :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
      (model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB) →
        Proposition1FiniteSSGMBridge E W model →
          ILVConvergesToSocietalOptimal E SourceNorm.l2 model

theorem proposition1Statement_of_sourceBridge_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (hSource : Proposition1SourceToFiniteSSGMBridge E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  intro Component hC hWeighted model hmodel hResponse
  rcases hSource.finite_bridge hC hWeighted model hmodel hResponse with
    ⟨W, _hWeightedW, hBridge⟩
  exact hSSGM.converges hmodel hBridge

theorem proposition1Statement_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition1SourceSemantics E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceBridge_ssgmConvergence
    (proposition1SourceToFiniteSSGMBridge_of_semantics S) hSSGM

/-- Exact paper-facing formula for Proposition 2. -/
def proposition2Statement {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  ∀ (Coord : Type),
    ConditionsC123 E →
      (∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D) →
        ∀ model,
          (model = VoterResponseModel.modelA ∨ model = VoterResponseModel.modelB) →
            E.respondsAccordingTo model →
              ILVConvergesToMedianSet E SourceNorm.linfty model

/--
Finite-coordinate reading of Proposition 2.  The paper proof reasons about the
ambient coordinates `x^m`; this statement therefore requires the supplied
decomposition to use the identity coordinate projections on `Coord → ℝ`.
-/
def proposition2FiniteCoordinateStatement {Voter Coord : Type*}
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop :=
  ∀ (D : DecomposableStructure Voter (Coord → ℝ) Coord),
    ConditionsC123 E →
      IsDecomposableUtilitiesWith E D →
        (∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m) →
          ∀ model,
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                ILVConvergesToMedianSet E SourceNorm.linfty model

theorem proposition2FiniteCoordinateStatement_modelA
    {Voter Coord : Type*} {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (h : proposition2FiniteCoordinateStatement E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (hCoordinate :
      ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelA :=
  h D hC hD hCoordinate VoterResponseModel.modelA (Or.inl rfl) hResponse

theorem proposition2FiniteCoordinateStatement_modelB
    {Voter Coord : Type*} {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (h : proposition2FiniteCoordinateStatement E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (hCoordinate :
      ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelB :=
  h D hC hD hCoordinate VoterResponseModel.modelB (Or.inr rfl) hResponse

theorem proposition2Statement_modelA
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    (h : proposition2Statement E)
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelA) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelA :=
  h Coord hC hDecomposable VoterResponseModel.modelA (Or.inl rfl) hResponse

theorem proposition2Statement_modelB
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    (h : proposition2Statement E)
    (hC : ConditionsC123 E)
    (hDecomposable :
      ∃ D : DecomposableStructure Voter Point Coord,
        IsDecomposableUtilitiesWith E D)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB) :
    ILVConvergesToMedianSet E SourceNorm.linfty VoterResponseModel.modelB :=
  h Coord hC hDecomposable VoterResponseModel.modelB (Or.inr rfl) hResponse

/--
Finite/decomposable certificate for Proposition 2.  It records the
deterministic median-set identification target together with the visible source
hypotheses for one response model.
-/
structure Proposition2SSGMCaseCertificate
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord)
    (model : VoterResponseModel) where
  conditions : ConditionsC123 E
  decomposable : IsDecomposableUtilitiesWith E D
  model_choice :
    model = VoterResponseModel.modelA ∨
      model = VoterResponseModel.modelB
  response : E.respondsAccordingTo model
  median : DecomposableMedianCarrier E D
  linf_response : DecomposableLinfLocalResponseBridge E D

/--
Deterministic source-semantics bridge for Proposition 2.  It chooses the
decomposable structure and median-set certificate that the future SSGM theorem
should consume.
-/
structure Proposition2SourceToSSGMBridge {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) where
  case_certificate :
    ∀ {Coord : Type},
      ConditionsC123 E →
        (∃ D : DecomposableStructure Voter Point Coord,
          IsDecomposableUtilitiesWith E D) →
          ∀ model,
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ D : DecomposableStructure Voter Point Coord,
                  Proposition2SSGMCaseCertificate E D model

/--
Deterministic source semantics for Proposition 2.  It supplies the
coordinate-wise median-set identification and the local `L∞` response
decomposition for each visible decomposable-utility source instance.
-/
structure Proposition2SourceSemantics {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) where
  medianCarrier :
    ∀ {Coord : Type}
      {D : DecomposableStructure Voter Point Coord},
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableMedianCarrier E D
  linfResponse :
    ∀ {Coord : Type}
      {D : DecomposableStructure Voter Point Coord},
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableLinfLocalResponseBridge E D

/--
Fixed-decomposition source semantics for Proposition 2.  This is closer to the
paper proof sketch, which reasons about the supplied coordinate decomposition
rather than every possible decomposition of the point space.
-/
structure Proposition2FixedSourceSemantics {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) where
  medianSetSource :
    ConditionsC123 E →
      IsDecomposableUtilitiesWith E D →
        DecomposableMedianSetSource E D
  coordinateReplacement :
    ConditionsC123 E →
      IsDecomposableUtilitiesWith E D →
        DecomposableLinfCoordinateReplacement E D

def Proposition2FixedSourceSemantics.medianCarrier
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D) :
    DecomposableMedianCarrier E D :=
  decomposableMedianCarrier_of_medianSetSource hD
    (S.medianSetSource hC hD)

def Proposition2FixedSourceSemantics.linfResponse
    {Voter Point Coord : Type*}
    {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D) :
    DecomposableLinfLocalResponseBridge E D :=
  decomposableLinfLocalResponseBridge_of_coordinateReplacement hD
    (S.coordinateReplacement hC hD)

/--
Finite-coordinate fixed-decomposition Proposition 2 source semantics.  For the
identity coordinate decomposition, the replacement property is derived from the
finite `L∞` norm-distance semantics and product-box solution-space closure.
-/
structure Proposition2FiniteCoordinateFixedSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ))
    (D : DecomposableStructure Voter (Coord → ℝ) Coord) where
  medianSetSource :
    ConditionsC123 E →
      IsDecomposableUtilitiesWith E D →
        DecomposableMedianSetSource E D
  coordinateReplacementSource :
    ConditionsC123 E →
      IsDecomposableUtilitiesWith E D →
        FiniteCoordinateLinfCoordinateReplacementSource E D

/--
Finite-coordinate Proposition 2 source semantics.  This is the source layer for
the paper-faithful ambient-coordinate reading: median-set formulas are supplied
for identity-coordinate decompositions, while `L∞` coordinate replacement is
derived from concrete finite norm semantics and product-box solution-space
closure.
-/
structure Proposition2FiniteCoordinateSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  normDistance : UsesFiniteCoordinateNormDistance E
  productBox : FiniteCoordinateProductBoxSolutionSpaceSource E
  medianSetSource :
    ∀ {D : DecomposableStructure Voter (Coord → ℝ) Coord},
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableMedianSetSource E D

noncomputable def
    Proposition2FiniteCoordinateSourceSemantics.fixedSource
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (hCoordinate :
      ∀ m, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m) :
    Proposition2FiniteCoordinateFixedSourceSemantics E D where
  medianSetSource := S.medianSetSource
  coordinateReplacementSource := fun _hC _hD =>
    { normDistance := S.normDistance
      productBox := S.productBox
      coordinate_eq := hCoordinate }

noncomputable def
    Proposition2FiniteCoordinateFixedSourceSemantics.toFixedSourceSemantics
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (S : Proposition2FiniteCoordinateFixedSourceSemantics E D) :
    Proposition2FixedSourceSemantics E D where
  medianSetSource := S.medianSetSource
  coordinateReplacement := fun hC hD =>
    decomposableLinfCoordinateReplacement_of_finiteCoordinate
      (S.coordinateReplacementSource hC hD)

noncomputable def proposition2FixedSourceSemantics_of_medianSetSource_productBox
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (hMedian :
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableMedianSetSource E D)
    (hNorm : UsesFiniteCoordinateNormDistance E)
    (hProductBox : FiniteCoordinateProductBoxSolutionSpaceSource E)
    (hCoordinate :
      ∀ m : Coord, m ∈ D.coords → ∀ x : Coord → ℝ, D.coordinate m x = x m) :
    Proposition2FixedSourceSemantics E D where
  medianSetSource := hMedian
  coordinateReplacement := fun _hC _hD =>
    decomposableLinfCoordinateReplacement_of_finiteCoordinate
      { normDistance := hNorm
        productBox := hProductBox
        coordinate_eq := hCoordinate }

noncomputable def proposition2SourceToSSGMBridge_of_semantics
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E) :
    Proposition2SourceToSSGMBridge E where
  case_certificate hC hDecomposable model hmodel hResponse := by
    let D := Classical.choose hDecomposable
    have hD : IsDecomposableUtilitiesWith E D :=
      Classical.choose_spec hDecomposable
    exact
      ⟨D,
        { conditions := hC
          decomposable := hD
          model_choice := hmodel
          response := hResponse
          median := S.medianCarrier hC hD
          linf_response := S.linfResponse hC hD }⟩

/--
Build Proposition 2 source semantics when the source layer supplies the
coordinate-wise median identification and the product-coordinate replacement
property for local `L∞` queries.  The local response bridge is then proved from
Model A optimality and decomposable additivity, rather than assumed directly.
-/
noncomputable def proposition2SourceSemantics_of_medianCarrier_coordinateReplacement
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hMedian :
      ∀ {Coord : Type}
        {D : DecomposableStructure Voter Point Coord},
        ConditionsC123 E →
          IsDecomposableUtilitiesWith E D →
            DecomposableMedianCarrier E D)
    (hReplacement :
      ∀ {Coord : Type}
        {D : DecomposableStructure Voter Point Coord},
        ConditionsC123 E →
          IsDecomposableUtilitiesWith E D →
            DecomposableLinfCoordinateReplacement E D) :
    Proposition2SourceSemantics E where
  medianCarrier := hMedian
  linfResponse := fun hC hD =>
    decomposableLinfLocalResponseBridge_of_coordinateReplacement hD
      (hReplacement hC hD)

/--
Build Proposition 2 source semantics from the visible median-set membership
formula and the product-coordinate replacement property.  Both proof-facing
carrier fields are then derived locally.
-/
noncomputable def proposition2SourceSemantics_of_medianSetSource_coordinateReplacement
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hMedian :
      ∀ {Coord : Type}
        {D : DecomposableStructure Voter Point Coord},
        ConditionsC123 E →
          IsDecomposableUtilitiesWith E D →
            DecomposableMedianSetSource E D)
    (hReplacement :
      ∀ {Coord : Type}
        {D : DecomposableStructure Voter Point Coord},
        ConditionsC123 E →
          IsDecomposableUtilitiesWith E D →
            DecomposableLinfCoordinateReplacement E D) :
    Proposition2SourceSemantics E where
  medianCarrier := fun hC hD =>
    decomposableMedianCarrier_of_medianSetSource hD (hMedian hC hD)
  linfResponse := fun hC hD =>
    decomposableLinfLocalResponseBridge_of_coordinateReplacement hD
      (hReplacement hC hD)

/--
The theorem-shaped SSGM boundary for Proposition 2.  It consumes the explicit
decomposable/median certificate instead of assuming `proposition2Statement`
directly.
-/
structure Proposition2SSGMConvergenceTheorem {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop where
  converges :
    ∀ {Coord : Type}
      {D : DecomposableStructure Voter Point Coord}
      {model : VoterResponseModel},
      Proposition2SSGMCaseCertificate E D model →
        ILVConvergesToMedianSet E SourceNorm.linfty model

theorem proposition2Statement_of_sourceBridge_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (hSource : Proposition2SourceToSSGMBridge E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2Statement E := by
  intro Coord hC hDecomposable model hmodel hResponse
  rcases hSource.case_certificate hC hDecomposable model hmodel hResponse with
    ⟨D, hCase⟩
  exact hSSGM.converges hCase

theorem proposition2Statement_of_sourceSemantics_ssgmConvergence
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (S : Proposition2SourceSemantics E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceBridge_ssgmConvergence
    (proposition2SourceToSSGMBridge_of_semantics S) hSSGM

theorem proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence
    {Voter Point : Type*} {Coord : Type} {E : ILVEnvironment Voter Point}
    {D : DecomposableStructure Voter Point Coord}
    (S : Proposition2FixedSourceSemantics E D)
    (hSSGM : Proposition2SSGMConvergenceTheorem E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ILVConvergesToMedianSet E SourceNorm.linfty model := by
  exact
    hSSGM.converges
      { conditions := hC
        decomposable := hD
        model_choice := hmodel
        response := hResponse
        median := S.medianCarrier hC hD
        linf_response := S.linfResponse hC hD }

theorem proposition2_fixedDecomposition_convergence_of_finiteCoordinateSourceSemantics_ssgmConvergence
    {Voter : Type*} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    {D : DecomposableStructure Voter (Coord → ℝ) Coord}
    (S : Proposition2FiniteCoordinateFixedSourceSemantics E D)
    (hSSGM : Proposition2SSGMConvergenceTheorem E)
    (hC : ConditionsC123 E)
    (hD : IsDecomposableUtilitiesWith E D)
    (model : VoterResponseModel)
    (hmodel :
      model = VoterResponseModel.modelA ∨
        model = VoterResponseModel.modelB)
    (hResponse : E.respondsAccordingTo model) :
    ILVConvergesToMedianSet E SourceNorm.linfty model := by
  exact
    proposition2_fixedDecomposition_convergence_of_sourceSemantics_ssgmConvergence
      S.toFixedSourceSemantics hSSGM hC hD model hmodel hResponse

theorem proposition2FiniteCoordinateStatement_of_finiteCoordinateSourceSemantics_ssgmConvergence
    {Voter : Type*} {Coord : Type} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (S : Proposition2FiniteCoordinateSourceSemantics E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2FiniteCoordinateStatement E := by
  intro D hC hD hCoordinate model hmodel hResponse
  exact
    hSSGM.converges
      { conditions := hC
        decomposable := hD
        model_choice := hmodel
        response := hResponse
        median :=
          decomposableMedianCarrier_of_medianSetSource hD
            (S.medianSetSource hC hD)
        linf_response :=
          decomposableLinfLocalResponseBridge_of_coordinateReplacement hD
            (decomposableLinfCoordinateReplacement_of_finiteCoordinate
              { normDistance := S.normDistance
                productBox := S.productBox
                coordinate_eq := hCoordinate }) }

/--
Concrete finite-coordinate interpretation of the deterministic source model.

This record is the non-SSGM layer that turns the abstract `ILVEnvironment`
fields into the paper's finite-coordinate Algorithm 1 semantics: concrete norm
distance, full-space bounded-density C3 data, positive radius and Model B trace data,
weighted-Euclidean projected-SSGM inputs and objective identification,
decomposable median-set source formulas, and `L∞` coordinate-replacement
semantics.  It deliberately contains no stochastic convergence conclusion.
-/
structure FiniteCoordinateILVConcreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  r0 : ℝ
  r0_pos : 0 < r0
  normDistance : UsesFiniteCoordinateNormDistance E
  c3Data : FiniteCoordinateIdealDistributionData Coord
  modelB_trace :
    ∀ {p q : ℝ},
      IsLpNormedUtilities E (SourceNorm.lp p) →
        E.respondsAccordingTo VoterResponseModel.modelB →
          HolderDualFinite p q →
            FiniteModelBILVAlgorithm1PrimitiveTraceSource E p q r0
  weighted_l2_inputs :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component}
      {model : VoterResponseModel},
        ConditionsC123 E →
          IsWeightedEuclideanUtilitiesWith E W →
            (model = VoterResponseModel.modelA ∨
              model = VoterResponseModel.modelB) →
              E.respondsAccordingTo model →
                Σ r0 : ℝ, WeightedEuclideanL2SSGMTraceSource E W model r0
  weighted_objective :
    ∀ {Component : Type}
      {W : WeightedEuclideanStructure Voter (Coord → ℝ) Component},
      ConditionsC123 E →
        IsWeightedEuclideanUtilitiesWith E W →
          WeightedEuclideanSocialObjectiveFormulaSource E W
  decomposable_medianSetSource :
    ∀ {Axis : Type}
      {D : DecomposableStructure Voter (Coord → ℝ) Axis},
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableMedianSetSource E D
  decomposable_linfReplacement :
    ∀ {Axis : Type}
      {D : DecomposableStructure Voter (Coord → ℝ) Axis},
      ConditionsC123 E →
        IsDecomposableUtilitiesWith E D →
          DecomposableLinfCoordinateReplacement E D

/--
Full finite-coordinate source model for the paper, excluding only the reusable
SSGM convergence theorem.  It keeps the existing source model for Theorem 2 and
Propositions 1/2, and adds the concrete finite Theorem 3 directional-field
model plus the corrected global-radius deterministic projected trace source.
-/
structure FiniteCoordinateILVFullConcreteSourceModel
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) where
  convergence_source : FiniteCoordinateILVConcreteSourceModel E
  theorem3_field : FiniteTheorem3DirectionalFieldModel E
  theorem3_convex_solutionSpace :
    C1ConvexSolutionSpaceSource E
  theorem3_convergence :
    FiniteCoordinateConvergenceSource E
  theorem3_continuity :
    FiniteTheorem3ConcreteFieldContinuitySource theorem3_field
  theorem3_trace :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceCoreSource
      theorem3_field

def FiniteCoordinateILVFullConcreteSourceModel.theorem3_traceSource
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E) :
    FiniteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource
      M.theorem3_field :=
  finiteTheorem3ConcreteFiniteDotProjectedTraceGlobalDeterministicTraceSource_of_core
    M.theorem3_continuity M.theorem3_trace

theorem FiniteCoordinateILVFullConcreteSourceModel.theorem3_convex
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E) :
    ConditionsC123 E → Convex ℝ E.solutionSpace :=
  fun _ => M.theorem3_convex_solutionSpace.convex_solutionSpace

def theorem2SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Theorem2SourceSemantics E :=
  theorem2SourceSemantics_of_primitive
    { r0 := M.r0
      r0_pos := M.r0_pos
      hNorm := M.normDistance
      c3Data := M.c3Data
      modelB_primitive_trace := M.modelB_trace }

def theorem2PrimitiveSourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Theorem2PrimitiveSourceSemantics E where
  r0 := M.r0
  r0_pos := M.r0_pos
  hNorm := M.normDistance
  c3Data := M.c3Data
  modelB_primitive_trace := M.modelB_trace

def proposition1SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Proposition1SourceSemantics E where
  weighted_l2_inputs := M.weighted_l2_inputs
  weighted_objective := M.weighted_objective

noncomputable def proposition2SourceSemantics_of_concreteSourceModel
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E) :
    Proposition2SourceSemantics E :=
  proposition2SourceSemantics_of_medianSetSource_coordinateReplacement
    M.decomposable_medianSetSource M.decomposable_linfReplacement

theorem theorem2Statement_of_concreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hSSGM : Theorem2SSGMConvergenceTheorem E) :
    theorem2Statement E := by
  exact theorem2Statement_of_sourceSemantics_ssgmConvergence
    (theorem2SourceSemantics_of_concreteSourceModel M) hSSGM

theorem proposition1Statement_of_concreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hSSGM : Proposition1SSGMConvergenceTheorem E) :
    proposition1Statement E := by
  exact proposition1Statement_of_sourceSemantics_ssgmConvergence
    (proposition1SourceSemantics_of_concreteSourceModel M) hSSGM

theorem proposition2Statement_of_concreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (hSSGM : Proposition2SSGMConvergenceTheorem E) :
    proposition2Statement E := by
  exact proposition2Statement_of_sourceSemantics_ssgmConvergence
    (proposition2SourceSemantics_of_concreteSourceModel M) hSSGM

def theorem1SourceToSSGMBridge_of_visible_hypotheses
    {Voter Point : Type*} (E : ILVEnvironment Voter Point) :
    Theorem1SourceToSSGMBridge E where
  case_certificate hC hUtil hmodel hResponse hpq :=
    { conditions := hC
      utilities := hUtil
      model_choice := hmodel
      response := hResponse
      norm_pair := hpq }

/--
Single theorem-shaped SSGM convergence bundle used by the final paper route.

This is deliberately only the stochastic convergence layer.  It does not
construct finite-coordinate source semantics; those are supplied separately by
`FiniteCoordinateILVConcreteSourceModel`.
-/
structure FiniteCoordinateILVSSGMConvergenceTheorems
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (E : ILVEnvironment Voter (Coord → ℝ)) : Prop where
  theorem1_convergence : Theorem1SSGMConvergenceTheorem E
  theorem2_convergence : Theorem2SSGMConvergenceTheorem E
  proposition1_convergence : Proposition1SSGMConvergenceTheorem E
  proposition2_convergence : Proposition2SSGMConvergenceTheorem E

/-- Exact paper-facing formula for Theorem 3. -/
def theorem3Statement {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop :=
  Theorem3DirectionalFieldFormula E →
    ConditionsC123 E →
      E.directionalFieldUniformlyContinuous →
        E.respondsAccordingTo VoterResponseModel.modelB →
          ∀ xstar,
            ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar →
              IsDirectionalEquilibrium E xstar

theorem theorem3Statement_directionalEquilibrium
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (h : theorem3Statement E)
    (hG : Theorem3DirectionalFieldFormula E)
    (hC : ConditionsC123 E)
    (hContinuous : E.directionalFieldUniformlyContinuous)
    (hResponse : E.respondsAccordingTo VoterResponseModel.modelB)
    {xstar : Point}
    (hConverges :
      ILVTrajectoryConvergesTo E SourceNorm.l2 VoterResponseModel.modelB xstar) :
    IsDirectionalEquilibrium E xstar :=
  h hG hC hContinuous hResponse xstar hConverges

theorem theorem3Statement_of_deterministicBridge
    {Voter Point : Type*} {E : ILVEnvironment Voter Point}
    (B : Theorem3DeterministicBridge E) :
    theorem3Statement E := by
  intro _hG hC hContinuous hResponse xstar hConverges
  exact
    (B.drift_certificate hC hContinuous hResponse hConverges).isDirectionalEquilibrium

/--
Structured bundle of paper endpoint consequences whose remaining proof debt is
the library-level stochastic subgradient convergence layer.

Keeping this as a named structure makes the boundary auditable: the paper-local
assumption imports one convergence bundle for the four SSGM convergence
endpoints, and the interface rows project named fields rather than destructing
an anonymous conjunction of final results. Theorem 3 is not included because it
is a deterministic post-convergence statement once the environment supplies the
Model B drift contradiction semantics.
-/
structure ILVSSGMConvergenceConsequences {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) : Prop where
  theorem1_consequence : theorem1Statement E
  theorem2_consequence : theorem2Statement E
  proposition1_consequence : proposition1Statement E
  proposition2_consequence : proposition2Statement E

theorem ilvSSGMConvergenceConsequences_of_sourceSemantics_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (T2 : Theorem2SourceSemantics E)
    (P1 : Proposition1SourceSemantics E)
    (P2 : Proposition2SourceSemantics E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact theorem1Statement_of_sourceBridge_ssgmConvergence
      (theorem1SourceToSSGMBridge_of_visible_hypotheses E)
      S.theorem1_convergence
  · exact theorem2Statement_of_sourceSemantics_ssgmConvergence
      T2 S.theorem2_convergence
  · exact proposition1Statement_of_sourceSemantics_ssgmConvergence
      P1 S.proposition1_convergence
  · exact proposition2Statement_of_sourceSemantics_ssgmConvergence
      P2 S.proposition2_convergence

theorem ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  refine
    { theorem1_consequence := ?_
      theorem2_consequence := ?_
      proposition1_consequence := ?_
      proposition2_consequence := ?_ }
  · exact theorem1Statement_of_sourceBridge_ssgmConvergence
      (theorem1SourceToSSGMBridge_of_visible_hypotheses E)
      S.theorem1_convergence
  · exact theorem2Statement_of_concreteSourceModel_ssgmConvergence
      M S.theorem2_convergence
  · exact proposition1Statement_of_concreteSourceModel_ssgmConvergence
      M S.proposition1_convergence
  · exact proposition2Statement_of_concreteSourceModel_ssgmConvergence
      M S.proposition2_convergence

theorem ilvSSGMConvergenceConsequences_of_fullConcreteSourceModel_ssgmConvergence
    {Voter Coord : Type*} [Fintype Voter]
    [MeasurableSpace Voter] [MeasurableSingletonClass Voter]
    [Fintype Coord] [Nonempty Coord]
    {E : ILVEnvironment Voter (Coord → ℝ)}
    (M : FiniteCoordinateILVFullConcreteSourceModel E)
    (S : FiniteCoordinateILVSSGMConvergenceTheorems E) :
    ILVSSGMConvergenceConsequences E := by
  exact ilvSSGMConvergenceConsequences_of_concreteSourceModel_ssgmConvergence
    M.convergence_source S

theorem ilvRadius_formula (r0 : ℝ) (t : ℕ) :
    ilvRadius r0 t = r0 / (t : ℝ) := by
  rfl

theorem conditionsC123_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) :
    ConditionsC123 E ↔
      E.solutionSpace_nonempty_bounded_closed_convex ∧
        E.uniqueIdealSolutions ∧
          E.idealDistribution_bounded_measurable_density := by
  rfl

theorem lpNormedUtilities_formula {Voter Point : Type*}
    (E : ILVEnvironment Voter Point) (p : SourceNorm) :
    IsLpNormedUtilities E p ↔
      ∀ v x, E.utility v x = -E.normDistance p x (E.ideal v) := by
  rfl

theorem weightedEuclideanUtilities_formula
    {Voter Point Component : Type*}
    (E : ILVEnvironment Voter Point)
    (W : WeightedEuclideanStructure Voter Point Component) :
    IsWeightedEuclideanUtilitiesWith E W ↔
      ∀ v x, E.utility v x = -W.components.sum
        (fun k => (W.weight v k / W.weightNorm2 v) * W.componentDistance k x v) := by
  rfl

theorem decomposableUtilities_formula
    {Voter Point Coord : Type*}
    (E : ILVEnvironment Voter Point)
    (D : DecomposableStructure Voter Point Coord) :
    IsDecomposableUtilitiesWith E D ↔
      ∀ v x, E.utility v x =
        D.coords.sum (fun m => D.coordinateUtility m v (D.coordinate m x)) := by
  rfl

end GKGMM19IterativeLocalVoting
