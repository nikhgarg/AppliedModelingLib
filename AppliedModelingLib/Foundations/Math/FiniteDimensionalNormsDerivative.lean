import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.InnerProductSpace.NormPow
import AppliedModelingLib.Foundations.Math.FiniteDimensionalNorms

/-!
# Derivatives of Finite-Coordinate Norm Power Sums

Reusable differentiability facts for the finite-coordinate norm formulas in
`AppliedModelingLib.FiniteDimensionalNorms`.
-/

open scoped BigOperators

namespace AppliedModelingLib
namespace FiniteDimensionalNorms

noncomputable section

/--
Linear functional represented by finite coordinates `g`, acting as
`h ↦ sum_i g_i * h_i`.
-/
def coordinateLinearFunctional {ι : Type*} [Fintype ι]
    (g : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i : ι, g i •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i :
      (ι → ℝ) →L[ℝ] ℝ)

theorem coordinateLinearFunctional_neg {ι : Type*} [Fintype ι]
    (g : ι → ℝ) :
    coordinateLinearFunctional (fun i => -g i) =
      -coordinateLinearFunctional g := by
  ext h
  simp [coordinateLinearFunctional, Finset.sum_neg_distrib]

/--
Fréchet derivative of the finite `Lp` power sum
`x ↦ sum_i |x_i|^p` at `d`, for `1 < p`.
-/
def lpPowerFDeriv {ι : Type*} [Fintype ι]
    (p : ℝ) (d : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i : ι, (p * |d i| ^ (p - 2) * d i) •
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i :
      (ι → ℝ) →L[ℝ] ℝ)

/--
The finite-coordinate `Lp` power sum is differentiable for `1 < p`, with the
coordinate derivative `p * |d_i|^(p-2) * d_i`.
-/
theorem hasFDerivAt_lpPower {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) (d : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => lpPower p y)
      (lpPowerFDeriv p d) d := by
  have hsum : HasFDerivAt
      (∑ i : ι, (fun y : ι → ℝ => |y i| ^ p : (ι → ℝ) → ℝ))
      (∑ i : ι, (p * |d i| ^ (p - 2) * d i) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i :
          (ι → ℝ) →L[ℝ] ℝ)) d := by
    refine HasFDerivAt.sum (𝕜 := ℝ) (E := ι → ℝ) (F := ℝ)
      (u := (Finset.univ : Finset ι)) (x := d) ?_
    intro i _hi
    have happly : HasFDerivAt (fun y : ι → ℝ => y i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i :
          (ι → ℝ) →L[ℝ] ℝ) d := by
      simpa using (hasFDerivAt_apply (𝕜 := ℝ) i d)
    have hcoord : HasFDerivAt (fun y : ι → ℝ => |y i| ^ p)
        ((p * |d i| ^ (p - 2) * d i) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i :
            (ι → ℝ) →L[ℝ] ℝ)) d := by
      simpa [Function.comp_def] using
        (HasDerivAt.comp_hasFDerivAt (x := d)
          (hh := hasDerivAt_abs_rpow (d i) hp)
          (hf := happly))
    exact hcoord
  convert hsum using 1
  · funext y
    simp [lpPower]

/-- Fréchet derivative of the finite-coordinate `Lp` norm away from zero. -/
def lpFDeriv {ι : Type*} [Fintype ι]
    (p : ℝ) (d : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ((1 / p) * (lpPower p d) ^ (1 / p - 1)) • lpPowerFDeriv p d

/--
The finite-coordinate `Lp` norm is differentiable away from the zero vector for
`1 < p`, with derivative obtained by the chain rule from `lpPower`.
-/
theorem hasFDerivAt_lp {ι : Type*} [Fintype ι]
    {p : ℝ} (hp : 1 < p) {d : ι → ℝ} (hd : ∃ i, d i ≠ 0) :
    HasFDerivAt (fun y : ι → ℝ => lp p y) (lpFDeriv p d) d := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hSpos : 0 < lpPower p d := lpPower_pos_of_exists_ne_zero hp_pos hd
  have houter : HasDerivAt (fun S : ℝ => S ^ (1 / p))
      ((1 / p) * (lpPower p d) ^ (1 / p - 1)) (lpPower p d) := by
    simpa using
      (Real.hasDerivAt_rpow_const (x := lpPower p d) (p := 1 / p)
        (Or.inl (ne_of_gt hSpos)))
  simpa [lp, lpFDeriv, Function.comp_def] using
    (HasDerivAt.comp_hasFDerivAt (x := d)
      (hh := houter)
      (hf := hasFDerivAt_lpPower hp d))

/-- The explicit squared Euclidean norm has its usual finite-coordinate derivative. -/
theorem hasFDerivAt_l2Sq {ι : Type*} [Fintype ι] (d : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => l2Sq y)
      ((2 : ℝ) • coordinateLinearFunctional d) d := by
  have h := hasFDerivAt_lpPower (ι := ι) (p := (2 : ℝ)) (by norm_num) d
  convert h using 1
  · funext y
    simp only [lpPower, l2Sq, Real.rpow_two, sq_abs]
  · ext h
    simp only [lpPowerFDeriv, coordinateLinearFunctional,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    norm_num
    ring

/--
Away from the zero vector, the derivative of the explicit finite-coordinate
Euclidean norm is the linear functional represented by the normalized vector.
-/
theorem hasFDerivAt_l2 {ι : Type*} [Fintype ι] {d : ι → ℝ}
    (hd : ∃ i, d i ≠ 0) :
    HasFDerivAt (fun y : ι → ℝ => l2 y)
      (coordinateLinearFunctional (fun i => d i / l2 d)) d := by
  have hsq_pos : 0 < l2Sq d := normL2Sq_pos_of_exists_ne_zero hd
  have hl2_pos : 0 < l2 d := normL2_pos_of_exists_ne_zero hd
  have h := (Real.hasDerivAt_sqrt hsq_pos.ne').comp_hasFDerivAt d
    (hasFDerivAt_l2Sq d)
  convert h using 1
  · ext z
    simp only [coordinateLinearFunctional, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    have hsqrt : Real.sqrt (l2Sq d) = l2 d := rfl
    rw [hsqrt]
    conv_rhs => rw [← mul_assoc]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    field_simp [hl2_pos.ne']

end

end FiniteDimensionalNorms
end AppliedModelingLib
