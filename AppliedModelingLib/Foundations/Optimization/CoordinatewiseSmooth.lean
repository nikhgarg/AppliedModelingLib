import AppliedModelingLib.Foundations.Optimization.SmoothComposition
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Coordinatewise lifting of scalar smooth maps

A scalar first-order smooth map lifts coordinatewise to every finite Euclidean
product without changing its value-Lipschitz, derivative-norm, or
derivative-Lipschitz constants.  This is the reusable dimension-free analytic
bridge used by standard elementwise neural-network activations.
-/

namespace AppliedModelingLib.Optimization

open scoped BigOperators

noncomputable section

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- Apply a scalar map coordinatewise to a finite Euclidean vector. -/
def coordinatewiseMap (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point : EuclideanSpace ℝ Index) : EuclideanSpace ℝ Index :=
  WithLp.toLp 2 fun index => scalar.toFun (point index)

/-- The diagonal derivative of a coordinatewise scalar map. -/
def coordinatewiseDeriv (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point : EuclideanSpace ℝ Index) :
    EuclideanSpace ℝ Index →L[ℝ] EuclideanSpace ℝ Index :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Index => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun index =>
      (scalar.deriv (point index)).comp (EuclideanSpace.proj (𝕜 := ℝ) index))

@[simp] theorem coordinatewiseMap_apply (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point : EuclideanSpace ℝ Index) (index : Index) :
    coordinatewiseMap scalar point index = scalar.toFun (point index) := rfl

@[simp] theorem coordinatewiseDeriv_apply (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point direction : EuclideanSpace ℝ Index) (index : Index) :
    coordinatewiseDeriv scalar point direction index =
      scalar.deriv (point index) (direction index) := rfl

/-- The coordinatewise lift has the expected diagonal Fréchet derivative. -/
theorem hasFDerivAt_coordinatewiseMap (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point : EuclideanSpace ℝ Index) :
    HasFDerivAt (coordinatewiseMap scalar) (coordinatewiseDeriv scalar point) point := by
  let coordinates : EuclideanSpace ℝ Index → Index → ℝ :=
    fun input index => scalar.toFun (input index)
  have hcoordinates :
      HasFDerivAt coordinates
        (ContinuousLinearMap.pi fun index =>
          (scalar.deriv (point index)).comp (EuclideanSpace.proj (𝕜 := ℝ) index)) point :=
    hasFDerivAt_pi.mpr fun index =>
      (scalar.hasFDerivAt (point index)).comp point
        (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 point index)
  have htoLp := PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (coordinates point)
  simpa only [coordinatewiseMap, coordinatewiseDeriv, coordinates] using
    htoLp.comp point hcoordinates

/-- Coordinatewise lifting preserves the scalar value-Lipschitz constant. -/
theorem coordinatewiseMap_lipschitz (scalar : FirstOrderSmoothMap ℝ ℝ)
    (first second : EuclideanSpace ℝ Index) :
    ‖coordinatewiseMap scalar first - coordinatewiseMap scalar second‖ ≤
      scalar.valueLipschitz * ‖first - second‖ := by
  have hsquares :
      ‖coordinatewiseMap scalar first - coordinatewiseMap scalar second‖ ^ 2 ≤
        (scalar.valueLipschitz * ‖first - second‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
      EuclideanSpace.real_norm_sq_eq]
    simp only [PiLp.sub_apply, coordinatewiseMap_apply]
    calc
      (∑ index : Index, (scalar.toFun (first index) - scalar.toFun (second index)) ^ 2) ≤
          ∑ index : Index, (scalar.valueLipschitz * (first index - second index)) ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        have h := scalar.value_lipschitz (first index) (second index)
        rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
        have hright : 0 ≤ scalar.valueLipschitz * |first index - second index| :=
          mul_nonneg scalar.valueLipschitz_nonneg (abs_nonneg _)
        have habs :
            |scalar.toFun (first index) - scalar.toFun (second index)| ^ 2 ≤
              (scalar.valueLipschitz * |first index - second index|) ^ 2 := by
          nlinarith [abs_nonneg (scalar.toFun (first index) - scalar.toFun (second index))]
        simpa only [mul_pow, sq_abs] using habs
      _ = scalar.valueLipschitz ^ 2 * ∑ index : Index, (first index - second index) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        ring
  have hright : 0 ≤ scalar.valueLipschitz * ‖first - second‖ :=
    mul_nonneg scalar.valueLipschitz_nonneg (norm_nonneg _)
  nlinarith [norm_nonneg (coordinatewiseMap scalar first - coordinatewiseMap scalar second)]

/-- The diagonal derivative has operator norm at most the scalar derivative bound. -/
theorem coordinatewiseDeriv_norm_le (scalar : FirstOrderSmoothMap ℝ ℝ)
    (point : EuclideanSpace ℝ Index) :
    ‖coordinatewiseDeriv scalar point‖ ≤ scalar.derivBound := by
  refine (coordinatewiseDeriv scalar point).opNorm_le_bound scalar.derivBound_nonneg ?_
  intro direction
  have hsquares :
      ‖coordinatewiseDeriv scalar point direction‖ ^ 2 ≤
        (scalar.derivBound * ‖direction‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
      EuclideanSpace.real_norm_sq_eq]
    simp only [coordinatewiseDeriv_apply]
    calc
      (∑ index : Index, (scalar.deriv (point index) (direction index)) ^ 2) ≤
          ∑ index : Index, (scalar.derivBound * direction index) ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        have happly := (scalar.deriv (point index)).le_opNorm (direction index)
        have hnorm := scalar.deriv_bound (point index)
        have hbound :
            |scalar.deriv (point index) (direction index)| ≤
              scalar.derivBound * |direction index| := by
          rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
          exact happly.trans (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
        have hright : 0 ≤ scalar.derivBound * |direction index| :=
          mul_nonneg scalar.derivBound_nonneg (abs_nonneg _)
        have hsquare :
            |scalar.deriv (point index) (direction index)| ^ 2 ≤
              (scalar.derivBound * |direction index|) ^ 2 := by
          nlinarith [abs_nonneg (scalar.deriv (point index) (direction index))]
        simpa only [mul_pow, sq_abs] using hsquare
      _ = scalar.derivBound ^ 2 * ∑ index : Index, direction index ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        ring
  have hright : 0 ≤ scalar.derivBound * ‖direction‖ :=
    mul_nonneg scalar.derivBound_nonneg (norm_nonneg _)
  nlinarith [norm_nonneg (coordinatewiseDeriv scalar point direction)]

/-- Coordinatewise lifting preserves the derivative-Lipschitz constant. -/
theorem coordinatewiseDeriv_lipschitz (scalar : FirstOrderSmoothMap ℝ ℝ)
    (first second : EuclideanSpace ℝ Index) :
    ‖coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second‖ ≤
      scalar.derivSmoothness * ‖first - second‖ := by
  let bound := scalar.derivSmoothness * ‖first - second‖
  have hbound : 0 ≤ bound :=
    mul_nonneg scalar.derivSmoothness_nonneg (norm_nonneg _)
  refine (coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second).opNorm_le_bound
    hbound ?_
  intro direction
  have hcoordinate : ∀ index : Index,
      |(coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second) direction index| ≤
        bound * |direction index| := by
    intro index
    have happly :=
      (scalar.deriv (first index) - scalar.deriv (second index)).le_opNorm (direction index)
    have hlocal := scalar.deriv_lipschitz (first index) (second index)
    have hcoordinateNorm : ‖first index - second index‖ ≤ ‖first - second‖ := by
      simpa only [PiLp.sub_apply] using PiLp.norm_apply_le (first - second) index
    change |scalar.deriv (first index) (direction index) -
      scalar.deriv (second index) (direction index)| ≤ bound * |direction index|
    rw [ContinuousLinearMap.sub_apply] at happly
    simp only [Real.norm_eq_abs] at happly
    calc
      |scalar.deriv (first index) (direction index) -
          scalar.deriv (second index) (direction index)| ≤
          ‖scalar.deriv (first index) - scalar.deriv (second index)‖ *
            |direction index| := happly
      _ ≤ (scalar.derivSmoothness * ‖first index - second index‖) *
            |direction index| :=
        mul_le_mul_of_nonneg_right hlocal (abs_nonneg _)
      _ ≤ bound * |direction index| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hcoordinateNorm scalar.derivSmoothness_nonneg
  have hsquares :
      ‖(coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second) direction‖ ^ 2 ≤
        (bound * ‖direction‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, mul_pow,
      EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ index : Index,
          ((coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second)
            direction index) ^ 2) ≤
          ∑ index : Index, (bound * direction index) ^ 2 := by
        apply Finset.sum_le_sum
        intro index _
        have h := hcoordinate index
        have hright : 0 ≤ bound * |direction index| :=
          mul_nonneg hbound (abs_nonneg _)
        have hsquare :
            |(coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second)
                direction index| ^ 2 ≤
              (bound * |direction index|) ^ 2 := by
          nlinarith [abs_nonneg
            ((coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second)
              direction index)]
        simpa only [mul_pow, sq_abs] using hsquare
      _ = bound ^ 2 * ∑ index : Index, direction index ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro index _
        ring
  have hright : 0 ≤ bound * ‖direction‖ := mul_nonneg hbound (norm_nonneg _)
  nlinarith [norm_nonneg
    ((coordinatewiseDeriv scalar first - coordinatewiseDeriv scalar second) direction)]

/-- Lift a scalar smooth map coordinatewise without changing its constants. -/
def FirstOrderSmoothMap.coordinatewise (scalar : FirstOrderSmoothMap ℝ ℝ) :
    FirstOrderSmoothMap (EuclideanSpace ℝ Index) (EuclideanSpace ℝ Index) where
  toFun := coordinatewiseMap scalar
  deriv := coordinatewiseDeriv scalar
  valueLipschitz := scalar.valueLipschitz
  derivBound := scalar.derivBound
  derivSmoothness := scalar.derivSmoothness
  valueLipschitz_nonneg := scalar.valueLipschitz_nonneg
  derivBound_nonneg := scalar.derivBound_nonneg
  derivSmoothness_nonneg := scalar.derivSmoothness_nonneg
  hasFDerivAt := hasFDerivAt_coordinatewiseMap scalar
  value_lipschitz := coordinatewiseMap_lipschitz scalar
  deriv_bound := coordinatewiseDeriv_norm_le scalar
  deriv_lipschitz := coordinatewiseDeriv_lipschitz scalar

end
end AppliedModelingLib.Optimization
