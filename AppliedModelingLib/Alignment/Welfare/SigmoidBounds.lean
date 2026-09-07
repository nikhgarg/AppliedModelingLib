import AppliedModelingLib.Alignment.Welfare.BradleyTerry
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Elementary sigmoid bounds for Bradley--Terry models

This module records real-analysis facts used by the finite Bradley--Terry
linearization interface.  The first bound is the tangent bound at zero used
in the upper half of the published argument of Gölz--Haghtalab--Yang (2025).
-/

namespace AppliedModelingLib
namespace Alignment
namespace Welfare

/-- The derivative of the real sigmoid is at most its value at zero, `1 / 4`. -/
theorem sigmoid_deriv_le_one_quarter (z : ℝ) :
    deriv Real.sigmoid z ≤ (1 : ℝ) / 4 := by
  rw [Real.deriv_sigmoid]
  nlinarith [sq_nonneg (Real.sigmoid z - (1 : ℝ) / 2)]

/-- On the nonnegative half-line, the sigmoid lies below its tangent at zero. -/
theorem sigmoid_centered_le_zero_tangent {z : ℝ} (hz : 0 ≤ z) :
    Real.sigmoid z - (1 : ℝ) / 2 ≤ z / 4 := by
  have h := image_sub_le_mul_sub_of_deriv_le differentiable_sigmoid
    sigmoid_deriv_le_one_quarter hz
  rw [Real.sigmoid_zero] at h
  nlinarith

/-- The second derivative of the real sigmoid in a factorized form. -/
theorem deriv2_sigmoid (z : ℝ) :
    deriv^[2] Real.sigmoid z =
      Real.sigmoid z * (1 - Real.sigmoid z) * (1 - 2 * Real.sigmoid z) := by
  simp only [Function.iterate_succ, Function.iterate_zero, Function.id_comp,
    Function.comp_apply]
  rw [Real.deriv_sigmoid]
  convert ((Real.hasDerivAt_sigmoid z).mul
    ((hasDerivAt_const z (1 : ℝ)).sub (Real.hasDerivAt_sigmoid z))).deriv using 1
  all_goals
    try simp only [Pi.sub_apply]
    ring

/-- The real sigmoid is concave on every nonnegative bounded interval. -/
theorem sigmoid_concaveOn_Icc_zero (beta : ℝ) :
    ConcaveOn ℝ (Set.Icc 0 beta) Real.sigmoid := by
  apply concaveOn_of_deriv2_nonpos (convex_Icc _ _) continuous_sigmoid.continuousOn
    differentiable_sigmoid.differentiableOn
  · rw [Real.deriv_sigmoid]
    fun_prop
  · intro z hz
    rw [interior_Icc] at hz
    rw [deriv2_sigmoid]
    have hhalf : (1 : ℝ) / 2 ≤ Real.sigmoid z := by
      calc
        (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
        _ ≤ Real.sigmoid z := Real.sigmoid_le hz.1.le
    have hleft : 0 ≤ Real.sigmoid z * (1 - Real.sigmoid z) := by
      exact mul_nonneg (Real.sigmoid_nonneg _) (sub_nonneg.mpr (Real.sigmoid_le_one _))
    have hright : 1 - 2 * Real.sigmoid z ≤ 0 := by
      linarith
    exact mul_nonpos_of_nonneg_of_nonpos hleft hright

/-- The source chord slope `ℓ_β = (σ(β) - 1/2) / β`. -/
noncomputable def sigmoidChordSlope (beta : ℝ) : ℝ :=
  (Real.sigmoid beta - (1 : ℝ) / 2) / beta

/-- On `[0, β]`, sigmoid lies above its chord through zero and `β`. -/
theorem sigmoidChordSlope_mul_le_sigmoid_centered
    {beta z : ℝ} (hbeta : 0 < beta) (hz : z ∈ Set.Icc 0 beta) :
    sigmoidChordSlope beta * z ≤ Real.sigmoid z - (1 : ℝ) / 2 := by
  have hconcave := sigmoid_concaveOn_Icc_zero beta
  have hweight_nonneg : 0 ≤ z / beta := div_nonneg hz.1 hbeta.le
  have hcomplement_nonneg : 0 ≤ 1 - z / beta := by
    exact sub_nonneg.mpr ((div_le_one₀ hbeta).mpr hz.2)
  have hweight_sum : z / beta + (1 - z / beta) = 1 := by ring
  have hchord := hconcave.2 (show beta ∈ Set.Icc 0 beta by exact ⟨hbeta.le, le_rfl⟩)
    (show (0 : ℝ) ∈ Set.Icc 0 beta by exact ⟨le_rfl, hbeta.le⟩)
    hweight_nonneg hcomplement_nonneg hweight_sum
  have hargument : (z / beta) • beta + (1 - z / beta) • (0 : ℝ) = z := by
    simp only [smul_eq_mul, mul_zero, add_zero]
    exact div_mul_cancel₀ z hbeta.ne'
  rw [hargument, Real.sigmoid_zero] at hchord
  change (z / beta) * Real.sigmoid beta + (1 - z / beta) * (2 : ℝ)⁻¹ ≤
    Real.sigmoid z at hchord
  have hrewrite :
      (z / beta) * Real.sigmoid beta + (1 - z / beta) * (2 : ℝ)⁻¹ =
        (2 : ℝ)⁻¹ + sigmoidChordSlope beta * z := by
    unfold sigmoidChordSlope
    field_simp [hbeta.ne']
    ring
  rw [hrewrite] at hchord
  norm_num at hchord ⊢
  linarith

/-- The source chord slope is nonnegative. -/
theorem sigmoidChordSlope_nonneg {beta : ℝ} (hbeta : 0 < beta) :
    0 ≤ sigmoidChordSlope beta := by
  unfold sigmoidChordSlope
  apply div_nonneg
  · apply sub_nonneg.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ ≤ Real.sigmoid beta := Real.sigmoid_le hbeta.le
  · exact hbeta.le

/-- The source chord slope is strictly positive at a positive temperature. -/
theorem sigmoidChordSlope_pos {beta : ℝ} (hbeta : 0 < beta) :
    0 < sigmoidChordSlope beta := by
  unfold sigmoidChordSlope
  apply div_pos
  · apply sub_pos.mpr
    calc
      (1 : ℝ) / 2 = Real.sigmoid 0 := by norm_num [Real.sigmoid_zero]
      _ < Real.sigmoid beta := Real.sigmoid_lt hbeta
  · exact hbeta

/-- The source chord slope is at most the zero-tangent slope `1 / 4`. -/
theorem sigmoidChordSlope_le_one_quarter {beta : ℝ} (hbeta : 0 < beta) :
    sigmoidChordSlope beta ≤ (1 : ℝ) / 4 := by
  unfold sigmoidChordSlope
  apply (div_le_iff₀ hbeta).mpr
  have htangent := sigmoid_centered_le_zero_tangent hbeta.le
  nlinarith

/-- On the negative half of the source interval, sigmoid lies below the reflected chord. -/
theorem sigmoid_centered_le_sigmoidChordSlope_mul
    {beta z : ℝ} (hbeta : 0 < beta) (hz : z ∈ Set.Icc (-beta) 0) :
    Real.sigmoid z - (1 : ℝ) / 2 ≤ sigmoidChordSlope beta * z := by
  have hneg_mem : -z ∈ Set.Icc 0 beta := by
    constructor <;> linarith [hz.1, hz.2]
  have hchord := sigmoidChordSlope_mul_le_sigmoid_centered hbeta hneg_mem
  rw [Real.sigmoid_neg] at hchord
  nlinarith

/-- The upper, per-user Bradley--Terry affine bound from Lemma 1 of the source paper. -/
theorem sigmoid_centered_bradleyTerry_upper
    {beta firstUtility secondUtility : ℝ} (hbeta : 0 < beta)
    (hfirst : firstUtility ∈ Set.Icc 0 1) (hsecond : secondUtility ∈ Set.Icc 0 1) :
    Real.sigmoid (beta * (firstUtility - secondUtility)) - (1 : ℝ) / 2 ≤
      beta * ((1 : ℝ) / 4 * firstUtility - sigmoidChordSlope beta * secondUtility) := by
  have hslope := sigmoidChordSlope_le_one_quarter hbeta
  by_cases hnonneg : 0 ≤ firstUtility - secondUtility
  · have htangent := sigmoid_centered_le_zero_tangent
      (mul_nonneg hbeta.le hnonneg)
    have hinner : (1 : ℝ) / 4 * (firstUtility - secondUtility) ≤
        (1 : ℝ) / 4 * firstUtility - sigmoidChordSlope beta * secondUtility := by
      have hnonneg_second : 0 ≤ secondUtility := hsecond.1
      nlinarith [mul_nonneg (sub_nonneg.mpr hslope) hnonneg_second]
    calc
      Real.sigmoid (beta * (firstUtility - secondUtility)) - (1 : ℝ) / 2 ≤
          (beta * (firstUtility - secondUtility)) / 4 := htangent
      _ = beta * ((1 : ℝ) / 4 * (firstUtility - secondUtility)) := by ring
      _ ≤ beta * ((1 : ℝ) / 4 * firstUtility - sigmoidChordSlope beta * secondUtility) :=
        mul_le_mul_of_nonneg_left hinner hbeta.le
  · have hnegative : firstUtility - secondUtility ≤ 0 := le_of_not_ge hnonneg
    have hdiff_lower : -(1 : ℝ) ≤ firstUtility - secondUtility := by
      linarith [hfirst.1, hsecond.2]
    have hscaled_lower : -beta ≤ beta * (firstUtility - secondUtility) := by
      have hscaled := mul_le_mul_of_nonneg_left hdiff_lower hbeta.le
      nlinarith
    have hscaled_upper : beta * (firstUtility - secondUtility) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hbeta.le hnegative
    have hchord := sigmoid_centered_le_sigmoidChordSlope_mul hbeta
      (show beta * (firstUtility - secondUtility) ∈ Set.Icc (-beta) 0 by
        exact ⟨hscaled_lower, hscaled_upper⟩)
    have hinner : sigmoidChordSlope beta * (firstUtility - secondUtility) ≤
        (1 : ℝ) / 4 * firstUtility - sigmoidChordSlope beta * secondUtility := by
      have hfirst_nonneg : 0 ≤ firstUtility := hfirst.1
      have hfirst_slope := mul_le_mul_of_nonneg_right hslope hfirst_nonneg
      nlinarith
    calc
      Real.sigmoid (beta * (firstUtility - secondUtility)) - (1 : ℝ) / 2 ≤
          sigmoidChordSlope beta * (beta * (firstUtility - secondUtility)) := hchord
      _ = beta * (sigmoidChordSlope beta * (firstUtility - secondUtility)) := by ring
      _ ≤ beta * ((1 : ℝ) / 4 * firstUtility - sigmoidChordSlope beta * secondUtility) :=
        mul_le_mul_of_nonneg_left hinner hbeta.le

end Welfare
end Alignment
end AppliedModelingLib
