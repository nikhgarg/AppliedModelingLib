import AppliedModelingLib.Foundations.Math.FiniteSum
import AppliedModelingLib.Foundations.Optimization.SmoothComposition
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite Euclidean average pooling

Average pooling over an arbitrary finite family of windows, with a reusable
operator-norm bound in terms of the minimum and maximum window sizes and the
maximum input-coordinate overlap.  This is the dimension-free counting
argument used for convolutional pooling layers.
-/

namespace AppliedModelingLib.Optimization

open scoped BigOperators

noncomputable section

variable {InputIndex OutputIndex : Type*}
variable [Fintype InputIndex] [DecidableEq InputIndex]
variable [Fintype OutputIndex] [DecidableEq OutputIndex]

/-- Combinatorial parameters controlling a finite family of pooling windows. -/
structure AveragePoolingData (InputIndex OutputIndex : Type*)
    [Fintype InputIndex] [DecidableEq InputIndex]
    [Fintype OutputIndex] [DecidableEq OutputIndex] where
  window : OutputIndex → Finset InputIndex
  lowerSize : ℝ
  upperSize : ℝ
  overlap : ℝ
  lowerSize_pos : 0 < lowerSize
  upperSize_nonneg : 0 ≤ upperSize
  overlap_nonneg : 0 ≤ overlap
  window_lower : ∀ output, lowerSize ≤ ((window output).card : ℝ)
  window_upper : ∀ output, ((window output).card : ℝ) ≤ upperSize
  coordinate_overlap : ∀ input,
    (((Finset.univ.filter fun output => input ∈ window output).card : ℕ) : ℝ) ≤ overlap

namespace AveragePoolingData

variable (data : AveragePoolingData InputIndex OutputIndex)

/-- The average of the input coordinates in one pooling window. -/
def coordinate (output : OutputIndex) :
    EuclideanSpace ℝ InputIndex →L[ℝ] ℝ :=
  (((data.window output).card : ℝ)⁻¹) •
    ∑ input ∈ data.window output, EuclideanSpace.proj (𝕜 := ℝ) input

/-- The finite Euclidean average-pooling continuous linear map. -/
def linear :
    EuclideanSpace ℝ InputIndex →L[ℝ] EuclideanSpace ℝ OutputIndex :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : OutputIndex => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi data.coordinate)

@[simp] theorem coordinate_apply (output : OutputIndex)
    (point : EuclideanSpace ℝ InputIndex) :
    data.coordinate output point =
      (∑ input ∈ data.window output, point input) / (data.window output).card := by
  simp only [coordinate, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, inv_mul_eq_div]
  congr 1

@[simp] theorem linear_apply (point : EuclideanSpace ℝ InputIndex) (output : OutputIndex) :
    data.linear point output =
      (∑ input ∈ data.window output, point input) / (data.window output).card := by
  change data.coordinate output point = _
  exact data.coordinate_apply output point

/-- The source constant `sqrt(overlap * upperSize) / lowerSize`. -/
def lipschitzConstant : ℝ :=
  Real.sqrt (data.overlap * data.upperSize) / data.lowerSize

theorem lipschitzConstant_nonneg : 0 ≤ data.lipschitzConstant := by
  exact div_nonneg (Real.sqrt_nonneg _) data.lowerSize_pos.le

/-- Reindex the window energy by input coordinate and use the overlap cap. -/
theorem sum_window_squares_le_overlap (point : EuclideanSpace ℝ InputIndex) :
    (∑ output : OutputIndex,
        ∑ input ∈ data.window output, (point input) ^ 2) ≤
      data.overlap * ∑ input : InputIndex, (point input) ^ 2 := by
  classical
  have hrewrite :
      (∑ output : OutputIndex,
          ∑ input ∈ data.window output, (point input) ^ 2) =
        ∑ input : InputIndex,
          (((Finset.univ.filter fun output : OutputIndex =>
              input ∈ data.window output).card : ℕ) : ℝ) * (point input) ^ 2 := by
    calc
      (∑ output : OutputIndex,
          ∑ input ∈ data.window output, (point input) ^ 2) =
          ∑ output : OutputIndex, ∑ input : InputIndex,
            if input ∈ data.window output then (point input) ^ 2 else 0 := by
              apply Finset.sum_congr rfl
              intro output _
              simp
      _ = ∑ input : InputIndex, ∑ output : OutputIndex,
          if input ∈ data.window output then (point input) ^ 2 else 0 :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro input _
        calc
          (∑ output : OutputIndex,
              if input ∈ data.window output then (point input) ^ 2 else 0) =
              (∑ output : OutputIndex,
                if input ∈ data.window output then (1 : ℝ) else 0) *
                (point input) ^ 2 := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro output _
                  split_ifs <;> ring
          _ = _ := by rw [Finset.sum_boole]
  rw [hrewrite, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro input _
  exact mul_le_mul_of_nonneg_right (data.coordinate_overlap input)
    (sq_nonneg (point input))

/-- One pooling coordinate obeys the source's lower/upper window-size bound. -/
theorem linear_apply_sq_le (point : EuclideanSpace ℝ InputIndex)
    (output : OutputIndex) :
    (data.linear point output) ^ 2 ≤
      (data.upperSize / data.lowerSize ^ 2) *
        ∑ input ∈ data.window output, (point input) ^ 2 := by
  let card : ℝ := (data.window output).card
  let energy : ℝ := ∑ input ∈ data.window output, (point input) ^ 2
  have hcardLower : data.lowerSize ≤ card := data.window_lower output
  have hcardUpper : card ≤ data.upperSize := data.window_upper output
  have hcardPos : 0 < card := data.lowerSize_pos.trans_le hcardLower
  have henergy : 0 ≤ energy := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlowerUpper : data.lowerSize ≤ data.upperSize := hcardLower.trans hcardUpper
  have hproduct : data.lowerSize ^ 2 ≤ data.upperSize * card := by
    rw [pow_two]
    exact mul_le_mul hlowerUpper hcardLower data.lowerSize_pos.le data.upperSize_nonneg
  have hscale : card ≤ (data.upperSize / data.lowerSize ^ 2) * card ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos data.lowerSize_pos)).2
    nlinarith
  rw [data.linear_apply, div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hcardPos)).2
  calc
    (∑ input ∈ data.window output, point input) ^ 2 ≤
        card * energy := by
      exact AppliedModelingLib.FiniteSum.sq_sum_le_card_mul_sum_sq
        (data.window output) point
    _ ≤ ((data.upperSize / data.lowerSize ^ 2) * card ^ 2) * energy :=
      mul_le_mul_of_nonneg_right hscale henergy
    _ = ((data.upperSize / data.lowerSize ^ 2) * energy) * card ^ 2 := by ring

/-- The average-pooling operator has the source's overlap/window-size norm bound. -/
theorem norm_linear_apply_le (point : EuclideanSpace ℝ InputIndex) :
    ‖data.linear point‖ ≤ data.lipschitzConstant * ‖point‖ := by
  have hcoefficient : 0 ≤ data.upperSize / data.lowerSize ^ 2 :=
    div_nonneg data.upperSize_nonneg (sq_nonneg _)
  have hsquares :
      ‖data.linear point‖ ^ 2 ≤ (data.lipschitzConstant * ‖point‖) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (∑ output : OutputIndex, (data.linear point output) ^ 2) ≤
          ∑ output : OutputIndex,
            (data.upperSize / data.lowerSize ^ 2) *
              ∑ input ∈ data.window output, (point input) ^ 2 := by
        apply Finset.sum_le_sum
        intro output _
        exact data.linear_apply_sq_le point output
      _ = (data.upperSize / data.lowerSize ^ 2) *
          ∑ output : OutputIndex,
            ∑ input ∈ data.window output, (point input) ^ 2 := by
        rw [Finset.mul_sum]
      _ ≤ (data.upperSize / data.lowerSize ^ 2) *
          (data.overlap * ∑ input : InputIndex, (point input) ^ 2) :=
        mul_le_mul_of_nonneg_left (data.sum_window_squares_le_overlap point) hcoefficient
      _ = (data.lipschitzConstant * ‖point‖) ^ 2 := by
        rw [lipschitzConstant, mul_pow, div_pow,
          Real.sq_sqrt (mul_nonneg data.overlap_nonneg data.upperSize_nonneg),
          EuclideanSpace.real_norm_sq_eq]
        ring
  have hright : 0 ≤ data.lipschitzConstant * ‖point‖ :=
    mul_nonneg data.lipschitzConstant_nonneg (norm_nonneg _)
  nlinarith [norm_nonneg (data.linear point)]

/-- Operator-norm form of the average-pooling estimate. -/
theorem norm_linear_le : ‖data.linear‖ ≤ data.lipschitzConstant := by
  exact data.linear.opNorm_le_bound data.lipschitzConstant_nonneg data.norm_linear_apply_le

/-- Average pooling as a globally first-order smooth map with zero derivative variation. -/
def smoothMap :
    FirstOrderSmoothMap (EuclideanSpace ℝ InputIndex) (EuclideanSpace ℝ OutputIndex) where
  toFun := data.linear
  deriv := fun _ => data.linear
  valueLipschitz := data.lipschitzConstant
  derivBound := data.lipschitzConstant
  derivSmoothness := 0
  valueLipschitz_nonneg := data.lipschitzConstant_nonneg
  derivBound_nonneg := data.lipschitzConstant_nonneg
  derivSmoothness_nonneg := le_rfl
  hasFDerivAt := fun _ => data.linear.hasFDerivAt
  value_lipschitz := by
    intro first second
    rw [← map_sub]
    exact data.norm_linear_apply_le (first - second)
  deriv_bound := fun _ => data.norm_linear_le
  deriv_lipschitz := by simp

@[simp] theorem smoothMap_apply (point : EuclideanSpace ℝ InputIndex)
    (output : OutputIndex) :
    data.smoothMap.toFun point output =
      (∑ input ∈ data.window output, point input) / (data.window output).card :=
  data.linear_apply point output

@[simp] theorem smoothMap_valueLipschitz :
    data.smoothMap.valueLipschitz =
      Real.sqrt (data.overlap * data.upperSize) / data.lowerSize := rfl

@[simp] theorem smoothMap_derivSmoothness :
    data.smoothMap.derivSmoothness = 0 := rfl

end AveragePoolingData

end
end AppliedModelingLib.Optimization
