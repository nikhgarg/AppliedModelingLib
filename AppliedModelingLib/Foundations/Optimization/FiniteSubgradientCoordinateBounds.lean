import AppliedModelingLib.Foundations.Optimization.ProjectedSubgradient

/-!
# Coordinate Bounds for Finite Subgradients

Small finite-dimensional convex-analysis lemmas shared by paper
formalizations.  The results use Lean's `FiniteSubgradientAt` inequality
directly; they do not inspect declaration syntax or depend on a paper model.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace Optimization

noncomputable section

/-- The real-valued unit vector at a finite coordinate. -/
def finiteCoordinateUnit {Coord : Type*} [DecidableEq Coord]
    (i : Coord) (a : ℝ) : Coord → ℝ :=
  fun j => if j = i then a else 0

/--
If moving either way by one coordinate unit changes a cost by at most one,
then every coordinate of every finite subgradient has magnitude at most one.
This is proved directly from the defining affine lower bound at the two unit
perturbations.
-/
theorem finiteSubgradientAt_coordinate_abs_le_one_of_unit_lipschitz
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {cost : (Coord → ℝ) → ℝ} {x g : Coord → ℝ}
    (hplus : ∀ z i,
      cost (fun j => z j + finiteCoordinateUnit i 1 j) ≤ cost z + 1)
    (hminus : ∀ z i,
      cost (fun j => z j - finiteCoordinateUnit i 1 j) ≤ cost z + 1)
    (hsub : FiniteSubgradientAt cost x g) (i : Coord) :
    |g i| ≤ 1 := by
  let e : Coord → ℝ := finiteCoordinateUnit i 1
  have hdote : FiniteDimensionalNorms.coordinateLinearFunctional g e = g i := by
    rw [coordinateLinearFunctional_apply]
    dsimp [e]
    simp [finiteCoordinateUnit]
  have hsubplus := hsub (fun j => x j + e j)
  have hsubplus' : cost x + FiniteDimensionalNorms.coordinateLinearFunctional g e ≤
      cost (fun j => x j + e j) := by
    simpa only [add_sub_cancel_left] using hsubplus
  rw [hdote] at hsubplus'
  have hplus' : cost (fun j => x j + e j) ≤ cost x + 1 := by
    simpa only [e] using hplus x i
  have hsubminus := hsub (fun j => x j - e j)
  have hdote_neg : FiniteDimensionalNorms.coordinateLinearFunctional g (fun j => -e j) =
      -g i := by
    rw [coordinateLinearFunctional_apply]
    dsimp [e]
    simp [finiteCoordinateUnit]
  have hsubminus' : cost x +
      FiniteDimensionalNorms.coordinateLinearFunctional g (fun j => -e j) ≤
      cost (fun j => x j - e j) := by
    have hdiff : (fun j => x j - e j - x j) = fun j => -e j := by
      funext j
      ring
    rw [hdiff] at hsubminus
    exact hsubminus
  rw [hdote_neg] at hsubminus'
  have hminus' : cost (fun j => x j - e j) ≤ cost x + 1 := by
    simpa only [e] using hminus x i
  rw [abs_le]
  constructor <;> linarith

/-- Every coordinate of a subgradient of a finite `L1` distance is at most one. -/
theorem finiteSubgradientAt_l1Distance_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {x ideal g : Coord → ℝ}
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ => FiniteDimensionalNorms.l1 (fun j => y j - ideal j)) x g)
    (i : Coord) :
    |g i| ≤ 1 := by
  apply finiteSubgradientAt_coordinate_abs_le_one_of_unit_lipschitz (hsub := hsub) (i := i)
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have he : FiniteDimensionalNorms.l1 e = 1 := by
      dsimp [e]
      rw [FiniteDimensionalNorms.l1]
      simp only [finiteCoordinateUnit, abs_ite, abs_one, abs_zero]
      rw [Finset.sum_ite_eq' Finset.univ j]
      norm_num
    rw [show (fun k => z k + finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + e k) by
      funext k
      simp only [e]
      ring]
    unfold FiniteDimensionalNorms.l1
    calc
      ∑ k, |(z k - ideal k) + e k| ≤ ∑ k, (|z k - ideal k| + |e k|) := by
        apply Finset.sum_le_sum
        intro k _
        exact abs_add_le _ _
      _ = (∑ k, |z k - ideal k|) + ∑ k, |e k| := Finset.sum_add_distrib
      _ = (∑ k, |z k - ideal k|) + 1 := by
        change (∑ k, |z k - ideal k|) + FiniteDimensionalNorms.l1 e =
          (∑ k, |z k - ideal k|) + 1
        rw [he]
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have he : FiniteDimensionalNorms.l1 e = 1 := by
      dsimp [e]
      rw [FiniteDimensionalNorms.l1]
      simp only [finiteCoordinateUnit, abs_ite, abs_one, abs_zero]
      rw [Finset.sum_ite_eq' Finset.univ j]
      norm_num
    rw [show (fun k => z k - finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + (-e k)) by
      funext k
      simp only [e]
      ring]
    unfold FiniteDimensionalNorms.l1
    calc
      ∑ k, |(z k - ideal k) + (-e k)| ≤ ∑ k, (|z k - ideal k| + |-e k|) := by
        apply Finset.sum_le_sum
        intro k _
        exact abs_add_le _ _
      _ = (∑ k, |z k - ideal k|) + ∑ k, |e k| := by
        simp only [abs_neg]
        rw [Finset.sum_add_distrib]
      _ = (∑ k, |z k - ideal k|) + 1 := by
        change (∑ k, |z k - ideal k|) + FiniteDimensionalNorms.l1 e =
          (∑ k, |z k - ideal k|) + 1
        rw [he]

/-- Every coordinate of a subgradient of a finite Euclidean distance is at most one. -/
theorem finiteSubgradientAt_l2Distance_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [DecidableEq Coord]
    {x ideal g : Coord → ℝ}
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ => FiniteDimensionalNorms.l2 (fun j => y j - ideal j)) x g)
    (i : Coord) :
    |g i| ≤ 1 := by
  apply finiteSubgradientAt_coordinate_abs_le_one_of_unit_lipschitz (hsub := hsub) (i := i)
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have he : FiniteDimensionalNorms.l2 e = 1 := by
      dsimp [e]
      rw [FiniteDimensionalNorms.l2]
      simp [FiniteDimensionalNorms.l2Sq, finiteCoordinateUnit]
    rw [show (fun k => z k + finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + e k) by
      funext k
      simp only [e]
      ring]
    calc
      FiniteDimensionalNorms.l2 (fun k => (z k - ideal k) + e k) ≤
          FiniteDimensionalNorms.l2 (fun k => z k - ideal k) + FiniteDimensionalNorms.l2 e :=
        FiniteDimensionalNorms.normL2_add_le _ _
      _ = FiniteDimensionalNorms.l2 (fun k => z k - ideal k) + 1 := by rw [he]
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have he : FiniteDimensionalNorms.l2 e = 1 := by
      dsimp [e]
      rw [FiniteDimensionalNorms.l2]
      simp [FiniteDimensionalNorms.l2Sq, finiteCoordinateUnit]
    have hneg : FiniteDimensionalNorms.l2 (fun k => -e k) = FiniteDimensionalNorms.l2 e := by
      unfold FiniteDimensionalNorms.l2 FiniteDimensionalNorms.l2Sq
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [show (fun k => z k - finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + (-e k)) by
      funext k
      simp only [e]
      ring]
    calc
      FiniteDimensionalNorms.l2 (fun k => (z k - ideal k) + (-e k)) ≤
          FiniteDimensionalNorms.l2 (fun k => z k - ideal k) +
            FiniteDimensionalNorms.l2 (fun k => -e k) :=
        FiniteDimensionalNorms.normL2_add_le _ _
      _ = FiniteDimensionalNorms.l2 (fun k => z k - ideal k) + 1 := by rw [hneg, he]

/-- Every coordinate of a subgradient of a finite `L∞` distance is at most one. -/
theorem finiteSubgradientAt_linfDistance_coordinate_abs_le_one
    {Coord : Type*} [Fintype Coord] [Nonempty Coord] [DecidableEq Coord]
    {x ideal g : Coord → ℝ}
    (hsub : FiniteSubgradientAt
      (fun y : Coord → ℝ => FiniteDimensionalNorms.linf (fun j => y j - ideal j)) x g)
    (i : Coord) :
    |g i| ≤ 1 := by
  apply finiteSubgradientAt_coordinate_abs_le_one_of_unit_lipschitz (hsub := hsub) (i := i)
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have he : FiniteDimensionalNorms.linf e ≤ 1 := by
      calc
        FiniteDimensionalNorms.linf e ≤ FiniteDimensionalNorms.l2 e :=
          FiniteDimensionalNorms.linf_le_l2 _
        _ = 1 := by
          dsimp [e]
          rw [FiniteDimensionalNorms.l2]
          simp [FiniteDimensionalNorms.l2Sq, finiteCoordinateUnit]
    rw [show (fun k => z k + finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + e k) by
      funext k
      simp only [e]
      ring]
    exact (FiniteDimensionalNorms.linf_add_le _ _).trans (add_le_add_right he _)
  · intro z j
    let e : Coord → ℝ := finiteCoordinateUnit j 1
    have hneg : FiniteDimensionalNorms.linf (fun k => -e k) ≤ 1 := by
      calc
        FiniteDimensionalNorms.linf (fun k => -e k) ≤ FiniteDimensionalNorms.l2 (fun k => -e k) :=
          FiniteDimensionalNorms.linf_le_l2 _
        _ = FiniteDimensionalNorms.l2 e := by
          unfold FiniteDimensionalNorms.l2 FiniteDimensionalNorms.l2Sq
          congr 1
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = 1 := by
          dsimp [e]
          rw [FiniteDimensionalNorms.l2]
          simp [FiniteDimensionalNorms.l2Sq, finiteCoordinateUnit]
    rw [show (fun k => z k - finiteCoordinateUnit j 1 k - ideal k) =
        (fun k => (z k - ideal k) + (-e k)) by
      funext k
      simp only [e]
      ring]
    exact (FiniteDimensionalNorms.linf_add_le _ _).trans (add_le_add_right hneg _)

/-- A coordinatewise unit bound yields this explicit, finite Euclidean bound. -/
theorem normL2_le_two_card_of_normL2Sq_le_four_card
    {Coord : Type*} [Fintype Coord] [Nonempty Coord]
    (x : Coord → ℝ)
    (hbound : FiniteDimensionalNorms.l2Sq x ≤ 4 * Fintype.card Coord) :
    FiniteDimensionalNorms.l2 x ≤ 2 * Fintype.card Coord := by
  have hcard_nat : 1 ≤ Fintype.card Coord := by
    exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr inferInstance)
  have hcard : (1 : ℝ) ≤ Fintype.card Coord := by
    exact_mod_cast hcard_nat
  apply FiniteDimensionalNorms.normL2_le_of_normL2Sq_le
  · positivity
  · nlinarith [hbound]

end
end Optimization
end AppliedModelingLib
