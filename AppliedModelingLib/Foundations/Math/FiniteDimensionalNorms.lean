import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Order.Compact

/-!
# Finite-Coordinate Norm Formulas

Paper-neutral formulas for the finite-coordinate `L1`, `L2`, `L∞`, and finite
`Lp` quantities that occur in continuous-space voting and optimization models.
Deep normed-space and differentiability facts should live in later analysis
modules; this file keeps the finite sums explicit.
-/

open Filter
open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteDimensionalNorms

noncomputable section

/-- Finite-coordinate `L1` quantity, written as a sum of absolute values. -/
def l1 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i : ι, |x i|

/-- Squared finite-coordinate `L2` quantity. -/
def l2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ∑ i : ι, x i ^ 2

/-- Finite-coordinate Euclidean dot product, written as an explicit sum. -/
def dot {ι : Type*} [Fintype ι] (x y : ι → ℝ) : ℝ :=
  ∑ i : ι, x i * y i

/-- Finite-coordinate `L2` quantity, written as the square root of `l2Sq`. -/
def l2 {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (l2Sq x)

/-- Finite-coordinate `L∞` quantity, written as the maximum absolute coordinate. -/
def linf {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) : ℝ :=
  (Finset.univ : Finset ι).sup' Finset.univ_nonempty (fun i => |x i|)

/-- Finite-coordinate `Lp` power sum, `sum_i |x_i|^p`. -/
def lpPower {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i : ι, |x i| ^ p

/-- Finite-coordinate `Lp` quantity, `(sum_i |x_i|^p)^(1/p)`. -/
def lp {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) : ℝ :=
  (lpPower p x) ^ (1 / p)

/-- The finite-coordinate `L^1` quantity agrees with the explicit `L1` sum. -/
theorem lp_one {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    lp 1 x = l1 x := by
  simp [lp, lpPower, l1]

theorem normL1_eq_sum_abs {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 x = ∑ i : ι, |x i| := rfl

theorem normL2Sq_eq_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2Sq x = ∑ i : ι, x i ^ 2 := rfl

theorem dot_eq_sum_mul {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    dot x y = ∑ i : ι, x i * y i := rfl

theorem dot_self_eq_l2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    dot x x = l2Sq x := by
  simp [dot, l2Sq, pow_two]

theorem dot_comm {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    dot x y = dot y x := by
  simp [dot, mul_comm]

/-- Distributing a difference through the left input of the finite-coordinate
dot product. -/
theorem dot_sub_left {ι : Type*} [Fintype ι] (x y z : ι → ℝ) :
    dot (fun i => x i - y i) z = dot x z - dot y z := by
  unfold dot
  calc
    (∑ i, (x i - y i) * z i) = ∑ i, (x i * z i - y i * z i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, x i * z i) - ∑ i, y i * z i := by
      rw [Finset.sum_sub_distrib]

/-- The squared finite-coordinate Euclidean norm of a difference. -/
theorem l2Sq_sub_eq {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    l2Sq (fun i => x i - y i) = l2Sq x - 2 * dot x y + l2Sq y := by
  unfold l2Sq dot
  calc
    (∑ i, (x i - y i) ^ 2) = ∑ i, (x i ^ 2 - 2 * (x i * y i) + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i, x i ^ 2) - 2 * (∑ i, x i * y i) + ∑ i, y i ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Scaling a finite-coordinate vector scales its squared Euclidean quantity quadratically. -/
theorem l2Sq_smul {ι : Type*} [Fintype ι] (a : ℝ) (x : ι → ℝ) :
    l2Sq (fun i => a * x i) = a ^ 2 * l2Sq x := by
  unfold l2Sq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/--
The squared Euclidean quantity is additive for vectors with disjoint
coordinate support.
-/
theorem l2Sq_add_eq_of_coordinatewise_disjoint
    {ι : Type*} [Fintype ι] (x y : ι → ℝ)
    (hdisjoint : ∀ i, x i = 0 ∨ y i = 0) :
    l2Sq (fun i => x i + y i) = l2Sq x + l2Sq y := by
  unfold l2Sq
  calc
    (∑ i, (x i + y i) ^ 2) = ∑ i, (x i ^ 2 + y i ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rcases hdisjoint i with hx | hy
      · simp [hx]
      · simp [hy]
    _ = (∑ i, x i ^ 2) + ∑ i, y i ^ 2 := Finset.sum_add_distrib

/--
Weighted coordinatewise-disjoint vectors have squared Euclidean quantity
equal to the corresponding weighted sum of squared quantities.
-/
theorem l2Sq_weighted_add_eq_of_coordinatewise_disjoint
    {ι : Type*} [Fintype ι] (a b : ℝ) (x y : ι → ℝ)
    (hdisjoint : ∀ i, x i = 0 ∨ y i = 0) :
    l2Sq (fun i => a * x i + b * y i) =
      a ^ 2 * l2Sq x + b ^ 2 * l2Sq y := by
  calc
    l2Sq (fun i => a * x i + b * y i) =
        l2Sq (fun i => a * x i) + l2Sq (fun i => b * y i) := by
      apply l2Sq_add_eq_of_coordinatewise_disjoint
      intro i
      rcases hdisjoint i with hx | hy
      · left
        simp [hx]
      · right
        simp [hy]
    _ = a ^ 2 * l2Sq x + b ^ 2 * l2Sq y := by
      rw [l2Sq_smul, l2Sq_smul]

/--
For a finite family whose vectors have disjoint coordinate supports, the
squared Euclidean quantity of a weighted sum is the sum of the weighted
squared quantities.
-/
theorem l2Sq_finset_weighted_sum_eq_of_coordinatewise_disjoint
    {ι κ : Type*} [Fintype ι] (s : Finset κ) (a : κ → ℝ) (x : κ → ι → ℝ)
    (hdisjoint : ∀ i k l, k ∈ s → l ∈ s → k ≠ l → x k i = 0 ∨ x l i = 0) :
    l2Sq (fun i => ∑ k ∈ s, a k * x k i) =
      ∑ k ∈ s, a k ^ 2 * l2Sq (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2Sq]
  | @insert k s hks ih =>
      have hrestrict :
          ∀ i l m, l ∈ s → m ∈ s → l ≠ m → x l i = 0 ∨ x m i = 0 := by
        intro i l m hl hm hlm
        exact hdisjoint i l m (Finset.mem_insert_of_mem hl)
          (Finset.mem_insert_of_mem hm) hlm
      have hsum_disjoint :
          ∀ i, a k * x k i = 0 ∨ (∑ l ∈ s, a l * x l i) = 0 := by
        intro i
        by_cases hkzero : x k i = 0
        · left
          simp [hkzero]
        · right
          apply Finset.sum_eq_zero
          intro l hl
          have hkl : x k i = 0 ∨ x l i = 0 :=
            hdisjoint i k l (Finset.mem_insert_self k s)
              (Finset.mem_insert_of_mem hl) (by
                intro hkl
                subst l
                exact hks hl)
          rcases hkl with hzero | hzero
          · exact False.elim (hkzero hzero)
          · simp [hzero]
      calc
        l2Sq (fun i => ∑ l ∈ insert k s, a l * x l i) =
            l2Sq (fun i => a k * x k i + ∑ l ∈ s, a l * x l i) := by
          congr 1
          funext i
          rw [Finset.sum_insert hks]
        _ = l2Sq (fun i => a k * x k i) +
            l2Sq (fun i => ∑ l ∈ s, a l * x l i) :=
          l2Sq_add_eq_of_coordinatewise_disjoint _ _ hsum_disjoint
        _ = a k ^ 2 * l2Sq (x k) + ∑ l ∈ s, a l ^ 2 * l2Sq (x l) := by
          rw [l2Sq_smul, ih hrestrict]
        _ = ∑ l ∈ insert k s, a l ^ 2 * l2Sq (x l) := by
          rw [Finset.sum_insert hks]

/--
A coordinatewise-disjoint weighted sum of unit vectors has Euclidean quantity
one when the coefficients have unit squared sum.
-/
theorem l2_finset_weighted_sum_eq_one_of_coordinatewise_disjoint
    {ι κ : Type*} [Fintype ι] (s : Finset κ) (a : κ → ℝ) (x : κ → ι → ℝ)
    (hdisjoint : ∀ i k l, k ∈ s → l ∈ s → k ≠ l → x k i = 0 ∨ x l i = 0)
    (hunit : ∀ k, k ∈ s → l2Sq (x k) = 1)
    (hweights : ∑ k ∈ s, a k ^ 2 = 1) :
    l2 (fun i => ∑ k ∈ s, a k * x k i) = 1 := by
  rw [l2, l2Sq_finset_weighted_sum_eq_of_coordinatewise_disjoint s a x hdisjoint]
  have hsum : ∑ k ∈ s, a k ^ 2 * l2Sq (x k) = 1 := by
    calc
      (∑ k ∈ s, a k ^ 2 * l2Sq (x k)) = ∑ k ∈ s, a k ^ 2 * 1 := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hunit k hk]
      _ = ∑ k ∈ s, a k ^ 2 := by
        simp
      _ = 1 := hweights
  rw [hsum, Real.sqrt_one]

/-- The finite-coordinate dot product commutes with a finite weighted sum in its right input. -/
theorem dot_weighted_sum_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → ℝ) (weights : κ → ℝ) (y : κ → ι → ℝ) :
    dot x (fun i => ∑ k, weights k * y k i) =
      ∑ k, weights k * dot x (y k) := by
  unfold dot
  change (∑ i, x i * ∑ k, weights k * y k i) =
    ∑ k, weights k * ∑ i, x i * y k i
  calc
    (∑ i, x i * ∑ k, weights k * y k i) =
        ∑ i, ∑ k, x i * (weights k * y k i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ = ∑ k, ∑ i, x i * (weights k * y k i) := Finset.sum_comm
    _ = ∑ k, weights k * ∑ i, x i * y k i := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/--
Squared distance to an affine combination is determined by the squared
distances to its finitely many anchors.  This identity is the deterministic
finite-dimensional ingredient that lets minimizer-set convergence arguments
use one common event for finitely many anchor potentials.
-/
theorem l2Sq_sub_eq_weighted_sum_sub
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x target : ι → ℝ) (weights : κ → ℝ) (anchor : κ → ι → ℝ)
    (hweights : ∑ k, weights k = 1)
    (htarget : ∀ i, target i = ∑ k, weights k * anchor k i) :
    l2Sq (fun i => x i - target i) =
      (∑ k, weights k * l2Sq (fun i => x i - anchor k i)) -
        ∑ k, weights k * l2Sq (fun i => target i - anchor k i) := by
  have hsum_const : ∀ z : ℝ, ∑ k, weights k * z = z := by
    intro z
    rw [← Finset.sum_mul, hweights, one_mul]
  have hdot_x : dot x target = ∑ k, weights k * dot x (anchor k) := by
    calc
      dot x target = dot x (fun i => ∑ k, weights k * anchor k i) := by
        congr
        funext i
        exact htarget i
      _ = ∑ k, weights k * dot x (anchor k) :=
        dot_weighted_sum_right x weights anchor
  have hdot_target : dot target target = ∑ k, weights k * dot target (anchor k) := by
    calc
      dot target target = dot target (fun i => ∑ k, weights k * anchor k i) := by
        congr
        funext i
        exact htarget i
      _ = ∑ k, weights k * dot target (anchor k) :=
        dot_weighted_sum_right target weights anchor
  have hfirst :
      ∑ k, weights k * l2Sq (fun i => x i - anchor k i) =
        l2Sq x - 2 * dot x target + ∑ k, weights k * l2Sq (anchor k) := by
    simp_rw [l2Sq_sub_eq]
    calc
      (∑ k, weights k * (l2Sq x - 2 * dot x (anchor k) + l2Sq (anchor k))) =
          ∑ k, (weights k * l2Sq x - 2 * (weights k * dot x (anchor k)) +
            weights k * l2Sq (anchor k)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ =
          (∑ k, weights k * l2Sq x) -
            2 * (∑ k, weights k * dot x (anchor k)) +
              ∑ k, weights k * l2Sq (anchor k) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = l2Sq x - 2 * dot x target + ∑ k, weights k * l2Sq (anchor k) := by
        rw [hsum_const, hdot_x]
  have hsecond :
      ∑ k, weights k * l2Sq (fun i => target i - anchor k i) =
        l2Sq target - 2 * dot target target + ∑ k, weights k * l2Sq (anchor k) := by
    simp_rw [l2Sq_sub_eq]
    calc
      (∑ k, weights k * (l2Sq target - 2 * dot target (anchor k) + l2Sq (anchor k))) =
          ∑ k, (weights k * l2Sq target - 2 * (weights k * dot target (anchor k)) +
            weights k * l2Sq (anchor k)) := by
        apply Finset.sum_congr rfl
        intro k _hk
        ring
      _ =
          (∑ k, weights k * l2Sq target) -
            2 * (∑ k, weights k * dot target (anchor k)) +
              ∑ k, weights k * l2Sq (anchor k) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = l2Sq target - 2 * dot target target +
          ∑ k, weights k * l2Sq (anchor k) := by
        rw [hsum_const, hdot_target]
  rw [l2Sq_sub_eq, hfirst, hsecond, dot_self_eq_l2Sq]
  ring

/--
Convergence of squared distances to finitely many affine anchors implies
convergence of the squared distance to every affine combination of them.
The anchor limits may be different; the conclusion identifies the induced
limit explicitly.
-/
theorem exists_tendsto_l2Sq_sub_of_affine_combination
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : ℕ → ι → ℝ} (target : ι → ℝ) (weights : κ → ℝ)
    (anchor : κ → ι → ℝ)
    (hweights : ∑ k, weights k = 1)
    (htarget : ∀ i, target i = ∑ k, weights k * anchor k i)
    (hpotential : ∀ k, ∃ limit : ℝ,
      Tendsto (fun n => l2Sq (fun i => f n i - anchor k i)) atTop (nhds limit)) :
    ∃ limit : ℝ, Tendsto
      (fun n => l2Sq (fun i => f n i - target i)) atTop (nhds limit) := by
  choose anchorLimit hanchorLimit using hpotential
  refine ⟨(∑ k, weights k * anchorLimit k) -
    ∑ k, weights k * l2Sq (fun i => target i - anchor k i), ?_⟩
  have hweighted : Tendsto
      (fun n => ∑ k, weights k * l2Sq (fun i => f n i - anchor k i)) atTop
        (nhds (∑ k, weights k * anchorLimit k)) := by
    apply tendsto_finset_sum Finset.univ
    intro k _hk
    exact (hanchorLimit k).const_mul (weights k)
  have hrewrite : (fun n => l2Sq (fun i => f n i - target i)) =
      fun n => (∑ k, weights k * l2Sq (fun i => f n i - anchor k i)) -
        ∑ k, weights k * l2Sq (fun i => target i - anchor k i) := by
    funext n
    exact l2Sq_sub_eq_weighted_sum_sub (f n) target weights anchor hweights htarget
  rw [hrewrite]
  exact hweighted.sub tendsto_const_nhds

/--
Every set of finite-coordinate real vectors has a finite subset with the same
affine span.  In particular, minimizer-set convergence arguments can choose a
finite anchor family from the minimizer set itself.
-/
theorem exists_finset_subset_affineSpan_eq
    {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) :
    ∃ anchor : Finset (ι → ℝ), (↑anchor : Set (ι → ℝ)) ⊆ s ∧
      affineSpan ℝ (↑anchor : Set (ι → ℝ)) = affineSpan ℝ s := by
  classical
  rcases exists_affineIndependent ℝ (ι → ℝ) s with
    ⟨t, hsubset, hspan, hindependent⟩
  have hfinite : Set.Finite t := finite_set_of_fin_dim_affineIndependent ℝ hindependent
  let anchor : Finset (ι → ℝ) := hfinite.toFinset
  refine ⟨anchor, ?_, ?_⟩
  · simpa [anchor] using hsubset
  · simpa [anchor] using hspan

/--
Every point of a finite-coordinate set is an affine combination of a finite
subfamily of that same set.  The coefficients are allowed to have either sign:
this is an affine-span statement, not a convexity statement.
-/
theorem exists_finset_affine_combination_representation
    {ι : Type*} [Fintype ι] (s : Set (ι → ℝ)) :
    ∃ anchor : Finset (ι → ℝ), (↑anchor : Set (ι → ℝ)) ⊆ s ∧
      ∀ target, target ∈ s → ∃ weights : (↑anchor) → ℝ,
        (∑ a, weights a = 1) ∧
          ∀ i, target i = ∑ a, weights a * ((a : ι → ℝ) i) := by
  classical
  rcases exists_finset_subset_affineSpan_eq s with ⟨anchor, hanchor, hspan⟩
  refine ⟨anchor, hanchor, ?_⟩
  intro target htarget
  let p : (↑anchor) → (ι → ℝ) := fun a => a
  have hrange : Set.range p = (↑anchor : Set (ι → ℝ)) := by
    ext x
    simp [p]
  have htarget_span : target ∈ affineSpan ℝ (Set.range p) := by
    rw [hrange, hspan]
    exact subset_affineSpan ℝ s htarget
  rcases eq_affineCombination_of_mem_affineSpan_of_fintype htarget_span with
    ⟨weights, hweights, htarget_weights⟩
  refine ⟨weights, hweights, ?_⟩
  have hlinear : target = ∑ a, weights a • p a := by
    rw [htarget_weights,
      Finset.affineCombination_eq_linear_combination Finset.univ p weights]
    simpa using hweights
  intro i
  exact congrFun hlinear i |>.trans (by simp [p, smul_eq_mul])

/--
Hilbert-space projection estimate used to turn one strong alignment and one
small cross-alignment into a same-family correlation bound.
-/
theorem real_inner_le_abs_cross_add_sqrt_one_sub_sq_of_unit
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {u v w : F} {alpha beta : ℝ}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (halpha : alpha ≤ inner ℝ u w) (halpha_nonneg : 0 ≤ alpha)
    (hcross : |inner ℝ v w| ≤ beta) :
    inner ℝ u v ≤ beta + Real.sqrt (1 - alpha ^ 2) := by
  let a : ℝ := inner ℝ u w
  let b : ℝ := inner ℝ v w
  let uperp : F := u - a • w
  let vperp : F := v - b • w
  have ha_nonneg : 0 ≤ a := le_trans halpha_nonneg halpha
  have ha_abs_le_one : |a| ≤ 1 := by
    have h := abs_real_inner_le_norm u w
    rw [hu, hw, mul_one] at h
    simpa [a] using h
  have ha_le_one : a ≤ 1 := (le_abs_self a).trans ha_abs_le_one
  have hdecomp : inner ℝ u v = a * b + inner ℝ uperp vperp := by
    dsimp [uperp, vperp, a, b]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, hw]
  have hab_le_beta : a * b ≤ beta := by
    have hab_le_abs : a * b ≤ |b| := by
      by_cases hb : 0 ≤ b
      · have hb_abs : |b| = b := abs_of_nonneg hb
        rw [hb_abs]
        nlinarith
      · have hbneg : b < 0 := lt_of_not_ge hb
        have hb_abs : |b| = -b := abs_of_neg hbneg
        rw [hb_abs]
        nlinarith
    exact hab_le_abs.trans hcross
  have huperp_sq : ‖uperp‖ ^ 2 = 1 - a ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [uperp, a]
    rw [inner_sub_sub_self]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, norm_smul, hu, hw]
    ring_nf
  have hvperp_sq : ‖vperp‖ ^ 2 = 1 - b ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp [vperp, b]
    rw [inner_sub_sub_self]
    simp [inner_smul_left, inner_smul_right, real_inner_comm, norm_smul, hv, hw]
    ring_nf
  have huperp_norm_le : ‖uperp‖ ≤ Real.sqrt (1 - alpha ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    rw [huperp_sq]
    nlinarith
  have hvperp_norm_le_one : ‖vperp‖ ≤ 1 := by
    have hs : ‖vperp‖ ^ 2 ≤ 1 := by
      rw [hvperp_sq]
      nlinarith [sq_nonneg b]
    have h := Real.le_sqrt_of_sq_le hs
    simpa using h
  have hperp_le : inner ℝ uperp vperp ≤ Real.sqrt (1 - alpha ^ 2) := by
    have h1 : inner ℝ uperp vperp ≤ |inner ℝ uperp vperp| := le_abs_self _
    have h2 := abs_real_inner_le_norm uperp vperp
    have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - alpha ^ 2) := Real.sqrt_nonneg _
    have h3 : ‖uperp‖ * ‖vperp‖ ≤ Real.sqrt (1 - alpha ^ 2) * 1 := by
      exact mul_le_mul huperp_norm_le hvperp_norm_le_one (norm_nonneg _) hsqrt_nonneg
    nlinarith
  rw [hdecomp]
  nlinarith

theorem normL2_eq_sqrt_sum_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x = Real.sqrt (∑ i : ι, x i ^ 2) := rfl

theorem linf_eq_sup_abs {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) :
    linf x = (Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i => |x i|) := rfl

theorem lpPower_eq_sum_abs_rpow {ι : Type*} [Fintype ι]
    (p : ℝ) (x : ι → ℝ) :
    lpPower p x = ∑ i : ι, |x i| ^ p := rfl

theorem lp_eq_power_sum_rpow {ι : Type*} [Fintype ι]
    (p : ℝ) (x : ι → ℝ) :
    lp p x = (∑ i : ι, |x i| ^ p) ^ (1 / p) := rfl

/--
Finite-coordinate Hölder inequality in the repository's explicit `lp`
notation.  The exponents are related by Mathlib's `HolderConjugate`
predicate, so all positivity and reciprocal identities remain part of the
mathematical premise rather than being reconstructed ad hoc at every use.
-/
theorem dot_le_lp_mul_lp
    {ι : Type*} [Fintype ι] (x y : ι → ℝ) {p q : ℝ}
    (hpq : p.HolderConjugate q) :
    dot x y ≤ lp p x * lp q y := by
  simpa only [dot, lp, lpPower] using
    (Real.inner_le_Lp_mul_Lq (s := (Finset.univ : Finset ι)) x y hpq)

theorem lpPower_smul {ι : Type*} [Fintype ι]
    (p a : ℝ) (x : ι → ℝ) :
    lpPower p (fun i => a * x i) = |a| ^ p * lpPower p x := by
  rw [lpPower, lpPower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg (x i))]

theorem normL1_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l1 x := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg (x i)

theorem normL2Sq_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l2Sq x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- A uniform coordinate bound controls the squared finite-coordinate Euclidean norm. -/
theorem normL2Sq_le_card_mul_sq_of_abs_le
    {ι : Type*} [Fintype ι] (x : ι → ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ i, |x i| ≤ B) :
    l2Sq x ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
  unfold l2Sq
  calc
    ∑ i, x i ^ 2 ≤ ∑ i, B ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (x i)) hB).mpr (hbound i)
    _ = (Fintype.card ι : ℝ) * B ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ]
      norm_num

theorem normL2_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    0 ≤ l2 x :=
  Real.sqrt_nonneg _

/-- A squared Euclidean bound yields the corresponding Euclidean bound. -/
theorem normL2_le_of_normL2Sq_le
    {ι : Type*} [Fintype ι] (x : ι → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hbound : l2Sq x ≤ K ^ 2) :
    l2 x ≤ K := by
  rw [l2, ← Real.sqrt_sq hK]
  exact Real.sqrt_le_sqrt hbound

/-- Squared Euclidean distance to a fixed finite-coordinate target is continuous. -/
theorem continuous_l2Sq_sub
    {ι : Type*} [Fintype ι] (target : ι → ℝ) :
    Continuous (fun x : ι → ℝ => l2Sq (fun i => x i - target i)) := by
  unfold l2Sq
  exact continuous_finset_sum Finset.univ fun i _ =>
    ((continuous_apply i).sub continuous_const).pow 2

/-- The finite-coordinate Euclidean norm is continuous in the product topology. -/
theorem continuous_l2 {ι : Type*} [Fintype ι] :
    Continuous (l2 : (ι → ℝ) → ℝ) := by
  unfold l2 l2Sq
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum Finset.univ fun i _ => (continuous_apply i).pow 2)

/-- A finite-coordinate Euclidean distance to a fixed target is continuous. -/
theorem continuous_l2_sub
    {ι : Type*} [Fintype ι] (target : ι → ℝ) :
    Continuous (fun x : ι → ℝ => l2 (fun i => x i - target i)) := by
  apply continuous_l2.comp
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub continuous_const

/-- The finite-coordinate `L∞` quantity is continuous in the product topology. -/
theorem continuous_linf {ι : Type*} [Fintype ι] [Nonempty ι] :
    Continuous (linf : (ι → ℝ) → ℝ) := by
  unfold linf
  apply Continuous.finset_sup'_apply
  intro i _hi
  exact (continuous_apply i).abs

/-- A positive finite-coordinate `Lp` quantity is continuous. -/
theorem continuous_lp
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 ≤ p) :
    Continuous (lp p : (ι → ℝ) → ℝ) := by
  unfold lp lpPower
  apply (Real.continuous_rpow_const (one_div_nonneg.mpr hp)).comp
  exact continuous_finset_sum Finset.univ fun i _ =>
    (Real.continuous_rpow_const hp).comp (continuous_abs.comp (continuous_apply i))

/--
A compact set of finite-coordinate vectors has a uniform Euclidean-distance
bound from any fixed target.  This is the paper-neutral compactness estimate
used to turn feasible-set compactness into stochastic-process integrability.
-/
theorem exists_l2_bound_on_isCompact
    {ι : Type*} [Fintype ι] {X : Set (ι → ℝ)}
    (hcompact : IsCompact X) (target : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ∈ X → l2 (fun i => x i - target i) ≤ C := by
  let distanceToTarget : (ι → ℝ) → ℝ :=
    fun x => l2 (fun i => x i - target i)
  have hcontinuous : Continuous distanceToTarget := by
    apply continuous_l2.comp
    apply continuous_pi
    intro i
    exact (continuous_apply i).sub continuous_const
  rcases (hcompact.image hcontinuous).bddAbove with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact le_trans (hC ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- A compact finite-coordinate set has a uniform Euclidean diameter bound. -/
theorem exists_l2_diameter_on_isCompact
    {ι : Type*} [Fintype ι] {X : Set (ι → ℝ)}
    (hcompact : IsCompact X) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ∈ X → ∀ y, y ∈ X →
      l2 (fun i => x i - y i) ≤ C := by
  let displacement : (ι → ℝ) × (ι → ℝ) → ι → ℝ :=
    fun z i => z.1 i - z.2 i
  have hdisplacement : Continuous displacement := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)
  let distance : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => l2 (displacement z)
  have hdistance : Continuous distance := continuous_l2.comp hdisplacement
  rcases ((hcompact.prod hcompact).image hdistance).bddAbove with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  exact le_trans (hC ⟨(x, y), ⟨hx, hy⟩, rfl⟩) (le_max_left _ _)

/-- A compact set has a uniform positive finite-`Lp` distance bound from any target. -/
theorem exists_lp_bound_on_isCompact
    {ι : Type*} [Fintype ι] {X : Set (ι → ℝ)} {p : ℝ}
    (hcompact : IsCompact X) (hp : 0 ≤ p) (target : ι → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ∈ X → lp p (fun i => target i - x i) ≤ C := by
  let distanceToTarget : (ι → ℝ) → ℝ :=
    fun x => lp p (fun i => target i - x i)
  have hcontinuous : Continuous distanceToTarget := by
    apply (continuous_lp hp).comp
    apply continuous_pi
    intro i
    exact continuous_const.sub (continuous_apply i)
  rcases (hcompact.image hcontinuous).bddAbove with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx
  exact le_trans (hC ⟨x, hx, rfl⟩) (le_max_left _ _)

/-- A compact set has a uniform positive finite-`Lp` diameter bound. -/
theorem exists_lp_diameter_on_isCompact
    {ι : Type*} [Fintype ι] {X : Set (ι → ℝ)} {p : ℝ}
    (hcompact : IsCompact X) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, x ∈ X → ∀ y, y ∈ X →
      lp p (fun i => x i - y i) ≤ C := by
  let displacement : (ι → ℝ) × (ι → ℝ) → ι → ℝ :=
    fun z i => z.1 i - z.2 i
  have hdisplacement : Continuous displacement := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp continuous_fst).sub
      ((continuous_apply i).comp continuous_snd)
  let distance : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => lp p (displacement z)
  have hdistance : Continuous distance := (continuous_lp hp).comp hdisplacement
  rcases ((hcompact.prod hcompact).image hdistance).bddAbove with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  exact le_trans (hC ⟨(x, y), ⟨hx, hy⟩, rfl⟩) (le_max_left _ _)

/-- A closed bounded set of finite real-coordinate vectors is compact. -/
theorem isCompact_of_isClosed_of_bounded
    {ι : Type*} [Fintype ι] {X : Set (ι → ℝ)}
    (hclosed : IsClosed X) (hbounded : Bornology.IsBounded X) :
    IsCompact X :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩

/-- Convergence of a squared finite-coordinate Euclidean norm to zero implies norm convergence. -/
theorem tendsto_l2_zero_of_tendsto_l2Sq_zero
    {α ι : Type*} [Fintype ι] {l : Filter α} {x : α → ι → ℝ}
    (h : Tendsto (fun n => l2Sq (x n)) l (nhds 0)) :
    Tendsto (fun n => l2 (x n)) l (nhds 0) := by
  simpa only [l2, Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp h

/-- Finite-dimensional Cauchy--Schwarz: squared `l1` norm is at most dimension times squared `l2` norm. -/
theorem normL1_sq_le_card_mul_normL2Sq
    {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 x ^ 2 ≤ (Fintype.card ι : ℝ) * l2Sq x := by
  simpa [normL1_eq_sum_abs, normL2Sq_eq_sum_sq, sq_abs] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : ι => |x i|))

theorem normL2_sq_eq_normL2Sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x ^ 2 = l2Sq x := by
  rw [l2]
  exact Real.sq_sqrt (normL2Sq_nonneg x)

theorem abs_dot_le_l2_mul_l2 {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    |dot x y| ≤ l2 x * l2 y := by
  have hpos :
      dot x y ≤ l2 x * l2 y := by
    simpa [dot, l2, l2Sq] using
      (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) x y)
  have hneg :
      -dot x y ≤ l2 x * l2 y := by
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt
        (Finset.univ : Finset ι) (fun i => -x i) y
    simpa [dot, l2, l2Sq, Finset.sum_neg_distrib] using h
  have hleft : -(l2 x * l2 y) ≤ dot x y := by
    linarith
  exact abs_le.mpr ⟨hleft, hpos⟩

/-- Squared finite-dimensional Cauchy--Schwarz in the `l2Sq` normalization. -/
theorem dot_sq_le_l2Sq_mul_l2Sq {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    dot x y ^ 2 ≤ l2Sq x * l2Sq y := by
  have habs := abs_dot_le_l2_mul_l2 x y
  have hsq : dot x y ^ 2 ≤ (l2 x * l2 y) ^ 2 := by
    rw [← sq_abs (dot x y)]
    exact sq_le_sq₀ (abs_nonneg _) (mul_nonneg (normL2_nonneg _) (normL2_nonneg _)) |>.mpr habs
  calc
    dot x y ^ 2 ≤ (l2 x * l2 y) ^ 2 := hsq
    _ = l2Sq x * l2Sq y := by
      rw [mul_pow, normL2_sq_eq_normL2Sq, normL2_sq_eq_normL2Sq]

/-- Each coordinate is bounded by the finite-coordinate `L2` norm. -/
theorem normL2_coord_abs_le {ι : Type*} [Fintype ι]
    (x : ι → ℝ) (i : ι) :
    |x i| ≤ l2 x := by
  rw [l2]
  exact Real.abs_le_sqrt <| by
    rw [l2Sq]
    exact Finset.single_le_sum
      (fun j _hj => sq_nonneg (x j))
      (Finset.mem_univ i)

/-- Squared Euclidean convergence gives convergence of each finite coordinate. -/
theorem tendsto_apply_of_tendsto_l2Sq_sub_zero
    {α ι : Type*} [Fintype ι] {l : Filter α}
    {f : α → ι → ℝ} {x : ι → ℝ}
    (h : Tendsto (fun n => l2Sq (fun i => f n i - x i)) l (nhds 0))
    (i : ι) :
    Tendsto (fun n => f n i) l (nhds (x i)) := by
  rw [← tendsto_sub_nhds_zero_iff]
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero (fun _ => abs_nonneg _)
  · intro n
    exact normL2_coord_abs_le (fun j => f n j - x j) i
  · exact tendsto_l2_zero_of_tendsto_l2Sq_zero h

/-- Squared Euclidean convergence implies convergence in the finite coordinate product space. -/
theorem tendsto_pi_of_tendsto_l2Sq_sub_zero
    {α ι : Type*} [Fintype ι] {l : Filter α}
    {f : α → ι → ℝ} {x : ι → ℝ}
    (h : Tendsto (fun n => l2Sq (fun i => f n i - x i)) l (nhds 0)) :
    Tendsto f l (nhds x) := by
  exact tendsto_pi_nhds.mpr fun i =>
    tendsto_apply_of_tendsto_l2Sq_sub_zero h i

/--
A finite-coordinate quasi-Fejér terminal principle.  If the squared Euclidean
potential to a candidate target has a limit and one strictly increasing
subsequence reaches that target, the whole sequence reaches the target.  This
is the final deterministic step in convergence-to-a-minimizer-set arguments:
the stochastic analysis supplies potential convergence, while compactness and
objective descent supply the convergent minimizer subsequence.
-/
theorem tendsto_pi_of_tendsto_l2Sq_sub_of_tendsto_subseq
    {ι : Type*} [Fintype ι] {f : ℕ → ι → ℝ} {target : ι → ℝ}
    {limit : ℝ} {subseq : ℕ → ℕ}
    (hpotential : Tendsto
      (fun n => l2Sq (fun i => f n i - target i)) atTop (nhds limit))
    (hsubseq_strict : StrictMono subseq)
    (hsubseq : Tendsto (fun n => f (subseq n)) atTop (nhds target)) :
    Tendsto f atTop (nhds target) := by
  have hpotential_subseq : Tendsto
      (fun n => l2Sq (fun i => f (subseq n) i - target i)) atTop
        (nhds limit) :=
    hpotential.comp hsubseq_strict.tendsto_atTop
  have hsubseq_l2Sq : Tendsto
      (fun n => l2Sq (fun i => f (subseq n) i - target i)) atTop (nhds 0) := by
    simpa [Function.comp_def, l2Sq] using
      ((continuous_l2Sq_sub target).tendsto target).comp hsubseq
  have hlimit : limit = 0 :=
    tendsto_nhds_unique hpotential_subseq hsubseq_l2Sq
  exact tendsto_pi_of_tendsto_l2Sq_sub_zero (by
    simpa [hlimit] using hpotential)

/--
On a compact domain, a continuous function with a unique minimizer has a
strictly positive objective gap outside every positive squared Euclidean ball
around that minimizer.
-/
theorem exists_pos_le_objective_gap_of_isCompact_of_continuousOn_of_unique_min
    {ι : Type*} [Fintype ι]
    {X : Set (ι → ℝ)} {objective : (ι → ℝ) → ℝ} {target : ι → ℝ}
    (hcompact : IsCompact X) (hcontinuous : ContinuousOn objective X)
    (hmin : IsMinOn objective X target)
    (hunique : ∀ x, x ∈ X → objective x = objective target → x = target)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ x, x ∈ X → epsilon ≤ l2Sq (fun i => x i - target i) →
        delta ≤ objective x - objective target := by
  let far : Set (ι → ℝ) := {x | epsilon ≤ l2Sq (fun i => x i - target i)}
  have hfar_closed : IsClosed far := by
    exact isClosed_le continuous_const (continuous_l2Sq_sub target)
  by_cases hfar_nonempty : (X ∩ far).Nonempty
  · have hcompact_far : IsCompact (X ∩ far) := hcompact.inter_right hfar_closed
    rcases hcompact_far.exists_isMinOn hfar_nonempty
      (hcontinuous.mono Set.inter_subset_left) with ⟨x0, hx0, hx0_min⟩
    refine ⟨objective x0 - objective target, ?_, ?_⟩
    · have htarget_le : objective target ≤ objective x0 := hmin hx0.1
      have hx0_ne : x0 ≠ target := by
        intro hx0_eq
        subst x0
        have hzero : epsilon ≤ 0 := by
          simpa [far, l2Sq] using hx0.2
        linarith
      have hvalue_ne : objective target ≠ objective x0 := by
        intro hvalue
        exact hx0_ne (hunique x0 hx0.1 hvalue.symm)
      exact sub_pos.mpr (lt_of_le_of_ne htarget_le hvalue_ne)
    · intro x hx hfar_x
      have hx_far : x ∈ X ∩ far := ⟨hx, hfar_x⟩
      have hmin_le := hx0_min hx_far
      change objective x0 ≤ objective x at hmin_le
      linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x hx hfar_x
    exact (hfar_nonempty ⟨x, hx, hfar_x⟩).elim

theorem normL2_smul {ι : Type*} [Fintype ι]
    (a : ℝ) (x : ι → ℝ) :
    l2 (fun i => a * x i) = |a| * l2 x := by
  rw [l2, l2]
  have hsum :
      l2Sq (fun i => a * x i) = a ^ 2 * l2Sq x := by
    rw [l2Sq, l2Sq, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

/-- Squared Euclidean distance is symmetric in finite coordinates. -/
theorem normL2Sq_sub_rev {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    l2Sq (fun i => x i - y i) = l2Sq (fun i => y i - x i) := by
  unfold l2Sq
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Euclidean distance is symmetric in finite coordinates. -/
theorem normL2_sub_rev {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    l2 (fun i => x i - y i) = l2 (fun i => y i - x i) := by
  unfold l2
  rw [normL2Sq_sub_rev]

/-- The squared Euclidean norm of a sum of three finite-coordinate vectors. -/
theorem normL2Sq_add_three_le {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    l2Sq (fun i => x i + y i + z i) ≤
      3 * (l2Sq x + l2Sq y + l2Sq z) := by
  unfold l2Sq
  calc
    ∑ i, (x i + y i + z i) ^ 2 ≤
        ∑ i, 3 * (x i ^ 2 + y i ^ 2 + z i ^ 2) := by
          apply Finset.sum_le_sum
          intro i _hi
          have hxy : 0 ≤ (x i - y i) ^ 2 := sq_nonneg _
          have hxz : 0 ≤ (x i - z i) ^ 2 := sq_nonneg _
          have hyz : 0 ≤ (y i - z i) ^ 2 := sq_nonneg _
          nlinarith
    _ = 3 * ((∑ i, x i ^ 2) + (∑ i, y i ^ 2) + (∑ i, z i ^ 2)) := by
      calc
        ∑ i, 3 * (x i ^ 2 + y i ^ 2 + z i ^ 2) =
            3 * ∑ i, (x i ^ 2 + y i ^ 2 + z i ^ 2) :=
              by rw [Finset.mul_sum]
        _ = 3 * ((∑ i, x i ^ 2) + (∑ i, y i ^ 2) + (∑ i, z i ^ 2)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- A bound on the Euclidean norm yields the corresponding squared-norm bound. -/
theorem normL2Sq_le_sq_of_normL2_le {ι : Type*} [Fintype ι]
    {x : ι → ℝ} {C : ℝ} (hC : 0 ≤ C) (hx : l2 x ≤ C) :
    l2Sq x ≤ C ^ 2 := by
  rw [← normL2_sq_eq_normL2Sq x]
  nlinarith [normL2_nonneg x]

/-- Uniform Euclidean bounds control the squared norm of a sum of three vectors. -/
theorem normL2Sq_add_three_le_of_normL2_le {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) {Cx Cy Cz : ℝ}
    (hCx : 0 ≤ Cx) (hCy : 0 ≤ Cy) (hCz : 0 ≤ Cz)
    (hx : l2 x ≤ Cx) (hy : l2 y ≤ Cy) (hz : l2 z ≤ Cz) :
    l2Sq (fun i => x i + y i + z i) ≤
      3 * (Cx ^ 2 + Cy ^ 2 + Cz ^ 2) := by
  calc
    l2Sq (fun i => x i + y i + z i) ≤
        3 * (l2Sq x + l2Sq y + l2Sq z) := normL2Sq_add_three_le x y z
    _ ≤ 3 * (Cx ^ 2 + Cy ^ 2 + Cz ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · exact add_le_add
          (add_le_add
            (normL2Sq_le_sq_of_normL2_le hCx hx)
            (normL2Sq_le_sq_of_normL2_le hCy hy))
          (normL2Sq_le_sq_of_normL2_le hCz hz)
      · norm_num

theorem linf_nonneg {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    0 ≤ linf x := by
  rw [linf]
  exact Finset.le_sup'_of_le _ Finset.univ_nonempty.choose_spec
    (abs_nonneg (x Finset.univ_nonempty.choose))

/-- Each finite coordinate is bounded in absolute value by the Euclidean quantity. -/
theorem abs_le_l2 {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    |x i| ≤ l2 x := by
  have hsquare : x i ^ 2 ≤ l2Sq x := by
    unfold l2Sq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  calc
    |x i| = Real.sqrt (x i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (l2Sq x) := Real.sqrt_le_sqrt hsquare
    _ = l2 x := rfl

/-- The finite `L∞` quantity is bounded by the Euclidean quantity. -/
theorem linf_le_l2 {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    linf x ≤ l2 x := by
  rw [linf]
  apply Finset.sup'_le
  intro i _hi
  exact abs_le_l2 x i

/-- The finite-coordinate `L∞` quantity satisfies the triangle inequality. -/
theorem linf_add_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y : ι → ℝ) :
    linf (fun i => x i + y i) ≤ linf x + linf y := by
  rw [linf]
  apply Finset.sup'_le
  intro i _hi
  calc
    |x i + y i| ≤ |x i| + |y i| := abs_add_le _ _
    _ ≤ linf x + linf y := add_le_add
      (Finset.le_sup' (s := (Finset.univ : Finset ι))
        (f := fun j => |x j|) (Finset.mem_univ i))
      (Finset.le_sup' (s := (Finset.univ : Finset ι))
        (f := fun j => |y j|) (Finset.mem_univ i))

/-- Moving the first point changes finite `L∞` distance by at most that move. -/
theorem linf_sub_le_linf_sub_add_linf_sub
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (x y target : ι → ℝ) :
    linf (fun i => x i - target i) ≤
      linf (fun i => y i - target i) + linf (fun i => x i - y i) := by
  have htriangle := linf_add_le
    (fun i => x i - y i) (fun i => y i - target i)
  rw [show (fun i => x i - target i) =
      (fun i => (x i - y i) + (y i - target i)) by
        funext i; ring]
  exact htriangle.trans (by rw [add_comm])

theorem lpPower_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) :
    0 ≤ lpPower p x := by
  exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg (x i)) p

/-- Each coordinate is bounded by a positive finite-coordinate `Lp` norm. -/
theorem abs_le_lp
    {ι : Type*} [Fintype ι] {p : ℝ} (hp : 0 < p)
    (x : ι → ℝ) (i : ι) :
    |x i| ≤ lp p x := by
  rw [lp, one_div]
  apply (Real.le_rpow_inv_iff_of_pos (abs_nonneg (x i)) (lpPower_nonneg p x) hp).mpr
  unfold lpPower
  exact Finset.single_le_sum
    (fun j _hj => Real.rpow_nonneg (abs_nonneg (x j)) p)
    (Finset.mem_univ i)

theorem lpPower_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < lpPower p x := by
  rcases hx with ⟨i, hi⟩
  rw [lpPower]
  exact Finset.sum_pos'
    (fun j _ => Real.rpow_nonneg (abs_nonneg (x j)) p)
    ⟨i, Finset.mem_univ i, Real.rpow_pos_of_pos (abs_pos.mpr hi) p⟩

theorem normL1_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l1 x := by
  rcases hx with ⟨i, hi⟩
  rw [l1]
  exact Finset.sum_pos'
    (fun j _ => abs_nonneg (x j))
    ⟨i, Finset.mem_univ i, abs_pos.mpr hi⟩

theorem normL2Sq_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l2Sq x := by
  rcases hx with ⟨i, hi⟩
  rw [l2Sq]
  exact Finset.sum_pos'
    (fun j _ => sq_nonneg (x j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem normL2_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < l2 x := by
  exact Real.sqrt_pos_of_pos (normL2Sq_pos_of_exists_ne_zero hx)

theorem linf_pos_of_exists_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι]
    {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < linf x := by
  rcases hx with ⟨i, hi⟩
  rw [linf]
  exact lt_of_lt_of_le (abs_pos.mpr hi)
    (Finset.le_sup'
      (s := (Finset.univ : Finset ι))
      (f := fun j => |x j|)
      (Finset.mem_univ i))

theorem lp_nonneg {ι : Type*} [Fintype ι] (p : ℝ) (x : ι → ℝ) :
    0 ≤ lp p x := by
  exact Real.rpow_nonneg (lpPower_nonneg p x) (1 / p)

theorem lp_smul_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (a : ℝ) (x : ι → ℝ) :
    lp p (fun i => a * x i) = |a| * lp p x := by
  have hp_ne : p ≠ 0 := ne_of_gt hp
  rw [lp, lpPower_smul, Real.mul_rpow
    (Real.rpow_nonneg (abs_nonneg a) p)
    (lpPower_nonneg p x)]
  congr 1
  rw [← Real.rpow_mul (abs_nonneg a) p (1 / p)]
  have hmul : p * (1 / p) = 1 := by field_simp [hp_ne]
  rw [hmul, Real.rpow_one]

theorem lp_pos_of_exists_ne_zero {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) {x : ι → ℝ} (hx : ∃ i, x i ≠ 0) :
    0 < lp p x := by
  rw [lp]
  exact Real.rpow_pos_of_pos (lpPower_pos_of_exists_ne_zero hp hx) (1 / p)

theorem normL1_zero {ι : Type*} [Fintype ι] :
    l1 (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l1]

theorem normL2Sq_zero {ι : Type*} [Fintype ι] :
    l2Sq (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l2Sq]

theorem normL2_zero {ι : Type*} [Fintype ι] :
    l2 (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [l2, l2Sq]

theorem linf_zero {ι : Type*} [Fintype ι] [Nonempty ι] :
    linf (fun _ : ι => (0 : ℝ)) = 0 := by
  rw [linf]
  exact Finset.sup'_eq_of_forall
    (s := (Finset.univ : Finset ι))
    (H := Finset.univ_nonempty)
    (f := fun _ : ι => |(0 : ℝ)|)
    (a := 0)
    (fun _ _ => by simp)

theorem lpPower_zero_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) :
    lpPower p (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [lpPower, Real.zero_rpow hp.ne']

theorem lp_zero_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) :
    lp p (fun _ : ι => (0 : ℝ)) = 0 := by
  simp [lp, lpPower_zero_of_pos (ι := ι) hp, Real.zero_rpow, hp.ne']

theorem normL1_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 (fun i => x i - x i) = 0 := by
  simpa using (normL1_zero (ι := ι))

theorem normL2Sq_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2Sq (fun i => x i - x i) = 0 := by
  simpa using (normL2Sq_zero (ι := ι))

theorem normL2_sub_self {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 (fun i => x i - x i) = 0 := by
  simpa using (normL2_zero (ι := ι))

theorem linf_sub_self {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    linf (fun i => x i - x i) = 0 := by
  simpa using (linf_zero (ι := ι))

theorem lpPower_sub_self_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lpPower p (fun i => x i - x i) = 0 := by
  simpa using (lpPower_zero_of_pos (ι := ι) hp)

theorem lp_sub_self_of_pos {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 0 < p) (x : ι → ℝ) :
    lp p (fun i => x i - x i) = 0 := by
  simpa using (lp_zero_of_pos (ι := ι) hp)

/-! ## Bridges to mathlib finite-product Lp norms -/

/--
The explicit finite `L1` formula is mathlib's `PiLp 1` norm on a finite
real coordinate product.
-/
theorem normL1_eq_piLp_norm_L1 {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l1 x =
      ‖(WithLp.toLp (1 : ENNReal) x :
        @PiLp (1 : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [l1, PiLp.norm_eq_of_L1]
  simp

/--
The explicit finite `L2` formula is mathlib's `PiLp 2` norm on a finite
real coordinate product.
-/
theorem normL2_eq_piLp_norm_L2 {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2 x =
      ‖(WithLp.toLp (2 : ENNReal) x :
        @PiLp (2 : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [l2, l2Sq, PiLp.norm_eq_of_L2]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  simp [sq_abs]

/-- The finite-coordinate Euclidean norm satisfies the triangle inequality. -/
theorem normL2_add_le {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    l2 (fun i => x i + y i) ≤ l2 x + l2 y := by
  let E : Type _ := @PiLp (2 : ENNReal) ι (fun _ => ℝ)
  let toE : (ι → ℝ) → E := WithLp.toLp 2
  calc
    l2 (fun i => x i + y i) = ‖toE (fun i => x i + y i)‖ :=
      normL2_eq_piLp_norm_L2 _
    _ = ‖toE x + toE y‖ := by
      change ‖WithLp.toLp 2 (fun i => x i + y i)‖ =
        ‖WithLp.toLp 2 x + WithLp.toLp 2 y‖
      change ‖WithLp.toLp 2 (x + y)‖ =
        ‖WithLp.toLp 2 x + WithLp.toLp 2 y‖
      rw [← WithLp.toLp_add]
    _ ≤ ‖toE x‖ + ‖toE y‖ := norm_add_le _ _
    _ = l2 x + l2 y := by
      rw [← normL2_eq_piLp_norm_L2 x, ← normL2_eq_piLp_norm_L2 y]

/-- The finite-coordinate Euclidean norm of a finite vector sum is bounded
by the sum of the individual Euclidean norms. -/
theorem normL2_finset_sum_le {ι κ : Type*} [Fintype ι]
    (s : Finset κ) (x : κ → ι → ℝ) :
    l2 (fun i => ∑ k ∈ s, x k i) ≤ ∑ k ∈ s, l2 (x k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l2, l2Sq]
  | @insert k s hks ih =>
      simp only [Finset.sum_insert hks]
      calc
        l2 (fun i => x k i + ∑ l ∈ s, x l i) ≤
            l2 (x k) + l2 (fun i => ∑ l ∈ s, x l i) := normL2_add_le _ _
        _ ≤ l2 (x k) + ∑ l ∈ s, l2 (x l) := by
          exact (add_le_add_iff_left (l2 (x k))).mpr ih

theorem piLp_inner_eq_dot {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) :
    inner ℝ
      (WithLp.toLp (2 : ENNReal) x : @PiLp (2 : ENNReal) ι (fun _ => ℝ))
      (WithLp.toLp (2 : ENNReal) y : @PiLp (2 : ENNReal) ι (fun _ => ℝ)) =
      dot x y := by
  rw [PiLp.inner_apply]
  rw [dot]
  apply Finset.sum_congr rfl
  intro i _hi
  change RCLike.re (y i * (starRingEnd ℝ) (x i)) = x i * y i
  simp [mul_comm]

/--
Finite-coordinate projection estimate, stated with the explicit `l2` and
`dot` APIs used by paper formalizations.
-/
theorem dot_le_abs_cross_add_sqrt_one_sub_sq_of_l2_unit
    {ι : Type*} [Fintype ι] {u v w : ι → ℝ} {alpha beta : ℝ}
    (hu : l2 u = 1) (hv : l2 v = 1) (hw : l2 w = 1)
    (halpha : alpha ≤ dot u w) (halpha_nonneg : 0 ≤ alpha)
    (hcross : |dot v w| ≤ beta) :
    dot u v ≤ beta + Real.sqrt (1 - alpha ^ 2) := by
  let U : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) u
  let V : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) v
  let W : @PiLp (2 : ENNReal) ι (fun _ => ℝ) := WithLp.toLp (2 : ENNReal) w
  have hU : ‖U‖ = 1 := by
    simpa [U] using (normL2_eq_piLp_norm_L2 u).symm.trans hu
  have hV : ‖V‖ = 1 := by
    simpa [V] using (normL2_eq_piLp_norm_L2 v).symm.trans hv
  have hW : ‖W‖ = 1 := by
    simpa [W] using (normL2_eq_piLp_norm_L2 w).symm.trans hw
  have halpha' : alpha ≤ inner ℝ U W := by
    simpa [U, W, piLp_inner_eq_dot] using halpha
  have hcross' : |inner ℝ V W| ≤ beta := by
    simpa [V, W, piLp_inner_eq_dot] using hcross
  have h :=
    real_inner_le_abs_cross_add_sqrt_one_sub_sq_of_unit
      hU hV hW halpha' halpha_nonneg hcross'
  simpa [U, V, piLp_inner_eq_dot] using h

/--
The explicit finite `L∞` formula is mathlib's `PiLp ∞` norm on a finite
real coordinate product.
-/
theorem linf_eq_piLp_norm_Linf {ι : Type*} [Fintype ι] [Nonempty ι] (x : ι → ℝ) :
    linf x =
      ‖(WithLp.toLp (⊤ : ENNReal) x :
        @PiLp (⊤ : ENNReal) ι (fun _ => ℝ))‖ := by
  rw [linf, PiLp.norm_eq_ciSup]
  simpa using (Finset.sup'_univ_eq_ciSup (fun i : ι => |x i|))

/--
For a positive finite exponent represented in `ENNReal`, mathlib's `PiLp`
norm is the same explicit finite power-sum formula.
-/
theorem piLp_norm_eq_lp_of_ENNReal
    {ι : Type*} [Fintype ι] (p : ENNReal) (hp : 0 < p.toReal)
    (x : ι → ℝ) :
    ‖(WithLp.toLp p x : @PiLp p ι (fun _ => ℝ))‖ =
      (∑ i : ι, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simpa using
    (PiLp.norm_eq_sum (β := fun _ : ι => ℝ) hp
      (WithLp.toLp p x : @PiLp p ι (fun _ => ℝ)))

/--
For a positive finite exponent represented in `ENNReal`, the explicit
finite `Lp` formula at `p.toReal` equals mathlib's `PiLp p` norm.
-/
theorem lp_toReal_eq_piLp_norm
    {ι : Type*} [Fintype ι] (p : ENNReal) (hp : 0 < p.toReal)
    (x : ι → ℝ) :
    lp p.toReal x =
      ‖(WithLp.toLp p x : @PiLp p ι (fun _ => ℝ))‖ := by
  rw [lp, lpPower, piLp_norm_eq_lp_of_ENNReal p hp]
  apply congrArg (fun s => s ^ (1 / p.toReal))
  apply Finset.sum_congr rfl
  intro i _hi
  simp

end

end FiniteDimensionalNorms
end AppliedModelingLib
