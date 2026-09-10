import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-!
# Admitted-population loss for uniform skill

The average loss is an integral over the actual admitted score distribution.
Increasing marginal loss per unit of score gives nonnegative partial
derivatives and curvature after integration by parts.
-/

namespace LBG22StrategicRanking

open Set MeasureTheory
open scoped Interval Topology
open Filter
noncomputable section

/-- Conditional average loss when skill is uniform and the produced-score
range of admitted applicants is `[x,a]`. -/
noncomputable def admittedLoss (L : ℝ → ℝ) (x a : ℝ) : ℝ :=
  x * a / (a - x) * ∫ z in x..a, L z / z ^ 2

private theorem pos_interval {x a z s : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (ha : a < s) (hz : z ∈ uIcc x a) : z ∈ Ioo 0 s := by
  rw [uIcc_of_le hxa] at hz
  exact ⟨hx.trans_le hz.1, hz.2.trans_lt ha⟩

private theorem integrable_pos {f : ℝ → ℝ} {s : ℝ}
    (hf : ContinuousOn f (Ioo 0 s)) {x a : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (ha : a < s) :
    IntervalIntegrable f volume x a :=
  (hf.mono fun _ hz => pos_interval hx hxa ha hz).intervalIntegrable

private theorem integral_left_pos {f : ℝ → ℝ} {s : ℝ}
    (hf : ContinuousOn f (Ioo 0 s)) {x a : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (ha : a < s) :
    HasDerivAt (fun y => ∫ z in y..a, f z) (-f x) x := by
  exact intervalIntegral.integral_hasDerivAt_left (integrable_pos hf hx hxa ha)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf x ⟨hx, hxa.trans_lt ha⟩)
    (hf.continuousAt (Ioo_mem_nhds hx (hxa.trans_lt ha)))

private theorem integral_right_pos {f : ℝ → ℝ} {s : ℝ}
    (hf : ContinuousOn f (Ioo 0 s)) {x a : ℝ} (hx : 0 < x) (hxa : x ≤ a)
    (ha : a < s) :
    HasDerivAt (fun y => ∫ z in x..y, f z) (f a) a := by
  have ha0 := hx.trans_le hxa
  exact intervalIntegral.integral_hasDerivAt_right (integrable_pos hf hx hxa ha)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf a ⟨ha0, ha⟩)
    (hf.continuousAt (Ioo_mem_nhds ha0 ha))

/-- Marginal loss per unit of produced score. -/
def lossSlope (L₁ : ℝ → ℝ) (z : ℝ) : ℝ := L₁ z / z

private theorem continuousOn_lossSlope {L₁ : ℝ → ℝ} {s : ℝ}
    (hL₁ : ContinuousOn L₁ (Ioo 0 s)) : ContinuousOn (lossSlope L₁) (Ioo 0 s) :=
  hL₁.div continuousOn_id fun _ hz => ne_of_gt hz.1

/-- The primitive inequality `z L'' ≥ L'` makes marginal loss per score increase. -/
theorem hasDerivAt_lossSlope {L₁ L₂ : ℝ → ℝ} {z : ℝ}
    (hz : 0 < z) (hL₁ : HasDerivAt L₁ (L₂ z) z) :
    HasDerivAt (lossSlope L₁) ((z * L₂ z - L₁ z) / z ^ 2) z := by
  simpa only [lossSlope, id_eq, mul_one, mul_comm] using
    hL₁.div (hasDerivAt_id z) (ne_of_gt hz)

private theorem continuousOn_of_derivative_pos {L L₁ : ℝ → ℝ} {s : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z) : ContinuousOn L (Ioo 0 s) :=
  fun z hz => (hL z hz).continuousAt.continuousWithinAt

private theorem continuousOn_lossIntegrand {L : ℝ → ℝ} {s : ℝ}
    (hL : ContinuousOn L (Ioo 0 s)) :
    ContinuousOn (fun z => L z / z ^ 2) (Ioo 0 s) :=
  hL.div (continuousOn_id.pow 2) fun _ hz => pow_ne_zero 2 (ne_of_gt hz.1)

/-- Integration by parts for the linear kernels appearing in the partial derivatives. -/
theorem admittedLoss_weighted_identity {L L₁ : ℝ → ℝ} {s : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ContinuousOn L₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) (r : ℝ) :
    (∫ z in x..a, (r - z) * lossSlope L₁ z) =
      r * (∫ z in x..a, L z / z ^ 2) +
        (r - a) * (L a / a) - (r - x) * (L x / x) := by
  have hc := continuousOn_of_derivative_pos hL
  have hk := continuousOn_lossSlope hL₁
  have hj := continuousOn_lossIntegrand hc
  have hd (z : ℝ) (hz : z ∈ uIcc x a) :
      HasDerivAt (fun z => (r - z) * (L z / z))
        ((r - z) * lossSlope L₁ z - r * (L z / z ^ 2)) z := by
    have hz0 := pos_interval hx hxa.le ha hz
    convert ((hasDerivAt_const z r).sub (hasDerivAt_id z)).mul
      ((hL z hz0).div (hasDerivAt_id z) hz0.1.ne') using 1
    dsimp [lossSlope]
    field_simp
    ring
  have hiA : IntervalIntegrable (fun z => (r - z) * lossSlope L₁ z) volume x a :=
    integrable_pos ((continuousOn_const.sub continuousOn_id).mul hk) hx hxa.le ha
  have hiJ : IntervalIntegrable (fun z => r * (L z / z ^ 2)) volume x a :=
    integrable_pos (continuousOn_const.mul hj) hx hxa.le ha
  have hi := hiA.sub hiJ
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_sub hiA hiJ,
    intervalIntegral.integral_const_mul] at he
  linarith

/-- First partial derivative with respect to the lowest admitted produced score. -/
theorem admittedLoss_hasDerivAt_left {L L₁ : ℝ → ℝ} {s : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ContinuousOn L₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun y => admittedLoss L y a)
      (a / (a - x) ^ 2 * ∫ z in x..a, (a - z) * lossSlope L₁ z) x := by
  have hj := continuousOn_lossIntegrand (continuousOn_of_derivative_pos hL)
  have hd := (((hasDerivAt_id x).mul_const a).div
    ((hasDerivAt_const x a).sub (hasDerivAt_id x)) (sub_ne_zero.mpr hxa.ne'))
    |>.mul (integral_left_pos hj hx hxa.le ha)
  have he := admittedLoss_weighted_identity hL hL₁ hx hxa ha a
  simp only [sub_self, zero_mul, add_zero] at he
  convert hd using 1
  dsimp
  rw [he]
  field_simp
  ring

/-- First partial derivative with respect to the highest admitted produced score. -/
theorem admittedLoss_hasDerivAt_right {L L₁ : ℝ → ℝ} {s : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ContinuousOn L₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun y => admittedLoss L x y)
      (x / (a - x) ^ 2 * ∫ z in x..a, (z - x) * lossSlope L₁ z) a := by
  have hj := continuousOn_lossIntegrand (continuousOn_of_derivative_pos hL)
  have hd := (((hasDerivAt_id a).const_mul x).div
    ((hasDerivAt_id a).sub_const x) (sub_ne_zero.mpr hxa.ne'))
    |>.mul (integral_right_pos hj hx hxa.le ha)
  have he := admittedLoss_weighted_identity hL hL₁ hx hxa ha x
  have hn : (∫ z in x..a, (z - x) * lossSlope L₁ z) =
      -(∫ z in x..a, (x - z) * lossSlope L₁ z) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  simp only [sub_self, zero_mul, sub_zero] at he
  convert hd using 1
  dsimp
  rw [hn, he]
  field_simp
  ring

/-- Integral expression for the first partial in the lower score. -/
def admittedLossLeft (k : ℝ → ℝ) (x a : ℝ) : ℝ :=
  a / (a - x) ^ 2 * ∫ z in x..a, (a - z) * k z

/-- Integral expression for the first partial in the upper score. -/
def admittedLossRight (k : ℝ → ℝ) (x a : ℝ) : ℝ :=
  x / (a - x) ^ 2 * ∫ z in x..a, (z - x) * k z

/-- Integration by parts with a squared affine kernel. -/
theorem admittedLoss_square_identity {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) (r : ℝ) :
    (∫ z in x..a, (r - z) ^ 2 * k₁ z) =
      (r - a) ^ 2 * k a - (r - x) ^ 2 * k x +
        2 * ∫ z in x..a, (r - z) * k z := by
  have hc := continuousOn_of_derivative_pos hk
  have hd (z : ℝ) (hz : z ∈ uIcc x a) :
      HasDerivAt (fun z => (r - z) ^ 2 * k z)
        ((r - z) ^ 2 * k₁ z - 2 * ((r - z) * k z)) z := by
    convert (((hasDerivAt_const z r).sub (hasDerivAt_id z)).pow 2).mul
      (hk z (pos_interval hx hxa.le ha hz)) using 1
    dsimp
    ring
  have hiA : IntervalIntegrable (fun z => (r - z) ^ 2 * k₁ z) volume x a :=
    integrable_pos (((continuousOn_const.sub continuousOn_id).pow 2).mul hk₁)
      hx hxa.le ha
  have hiB : IntervalIntegrable (fun z => 2 * ((r - z) * k z)) volume x a :=
    integrable_pos (continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).mul hc)) hx hxa.le ha
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hiA.sub hiB)
  rw [intervalIntegral.integral_sub hiA hiB, intervalIntegral.integral_const_mul] at he
  linarith

/-- The lower-score first partial differentiates to a nonnegative squared kernel. -/
theorem admittedLossLeft_hasDerivAt_left {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun y => admittedLossLeft k y a)
      (a / (a - x) ^ 3 * ∫ z in x..a, (a - z) ^ 2 * k₁ z) x := by
  have hc := continuousOn_of_derivative_pos hk
  have hi : ContinuousOn (fun z => (a - z) * k z) (Ioo 0 s) :=
    (continuousOn_const.sub continuousOn_id).mul hc
  have hd := ((hasDerivAt_const x a).div
    (((hasDerivAt_const x a).sub (hasDerivAt_id x)).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hxa.ne'))).mul
    (integral_left_pos hi hx hxa.le ha)
  have he := admittedLoss_square_identity hk hk₁ hx hxa ha a
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_sub] at he
  convert hd using 1
  dsimp
  rw [he]
  field_simp
  ring

/-- The upper-score first partial differentiates to a nonnegative squared kernel. -/
theorem admittedLossRight_hasDerivAt_right {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun y => admittedLossRight k x y)
      (x / (a - x) ^ 3 * ∫ z in x..a, (z - x) ^ 2 * k₁ z) a := by
  have hc := continuousOn_of_derivative_pos hk
  have hi : ContinuousOn (fun z => (z - x) * k z) (Ioo 0 s) :=
    (continuousOn_id.sub continuousOn_const).mul hc
  have hd := ((hasDerivAt_const a x).div
    (((hasDerivAt_id a).sub_const x).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hxa.ne'))).mul
    (integral_right_pos hi hx hxa.le ha)
  have he := admittedLoss_square_identity hk hk₁ hx hxa ha x
  have heq : (∫ z in x..a, (z - x) ^ 2 * k₁ z) =
      (∫ z in x..a, (x - z) ^ 2 * k₁ z) := by
    apply intervalIntegral.integral_congr
    intro z _
    ring
  have hn : (∫ z in x..a, (x - z) * k z) =
      -(∫ z in x..a, (z - x) * k z) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  simp only [sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul, sub_zero] at he
  convert hd using 1
  dsimp
  rw [heq, he, hn]
  field_simp
  ring

private theorem left_moment_eq {k : ℝ → ℝ} {s : ℝ}
    (hk : ContinuousOn k (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    (∫ z in x..a, (a - z) * k z) =
      a * (∫ z in x..a, k z) - ∫ z in x..a, z * k z := by
  have hiZ : IntervalIntegrable (fun z => z * k z) volume x a :=
    integrable_pos (continuousOn_id.mul hk) hx hxa.le ha
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      ((integrable_pos hk hx hxa.le ha).const_mul a)
      hiZ]
  apply intervalIntegral.integral_congr
  intro z _
  ring

private theorem left_moment_hasDerivAt_right {k : ℝ → ℝ} {s : ℝ}
    (hk : ContinuousOn k (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun a => ∫ z in x..a, (a - z) * k z)
      (∫ z in x..a, k z) a := by
  have hd := ((hasDerivAt_id a).mul (integral_right_pos hk hx hxa.le ha)).sub
    (integral_right_pos (continuousOn_id.mul hk) hx hxa.le ha)
  have heq : (fun a => ∫ z in x..a, (a - z) * k z) =ᶠ[𝓝 a]
      (fun a => a * (∫ z in x..a, k z) - ∫ z in x..a, z * k z) := by
    filter_upwards [eventually_gt_nhds hxa, eventually_lt_nhds ha] with y hyx hys
    exact left_moment_eq hk hx hyx hys
  convert hd.congr_of_eventuallyEq heq using 1
  dsimp
  ring

/-- The cubic integration-by-parts kernel for the mixed partial. -/
theorem admittedLoss_mixed_identity {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    (∫ z in x..a, (a - z) * ((a - x) ^ 2 + (a + x) * (z - x)) * k₁ z) =
      2 * (a * (a - x) * (∫ z in x..a, k z) -
        (a + x) * (∫ z in x..a, (a - z) * k z)) - (a - x) ^ 3 * k x := by
  have hc := continuousOn_of_derivative_pos hk
  let P : ℝ → ℝ := fun z => (a - z) * ((a - x) ^ 2 + (a + x) * (z - x))
  have hp : Continuous P := by dsimp [P]; fun_prop
  have hd (z : ℝ) (hz : z ∈ uIcc x a) :
      HasDerivAt (fun z => P z * k z)
        (P z * k₁ z - 2 * (a * (a - x) * k z - (a + x) * ((a - z) * k z))) z := by
    have hP : HasDerivAt P (-2 * ((a + x) * z - 2 * a * x)) z := by
      dsimp [P]
      convert ((hasDerivAt_const z a).sub (hasDerivAt_id z)).mul
        ((hasDerivAt_const z ((a - x) ^ 2)).add
          (((hasDerivAt_id z).sub_const x).const_mul (a + x))) using 1
      dsimp
      ring
    convert hP.mul (hk z (pos_interval hx hxa.le ha hz)) using 1
    dsimp [P]
    ring
  have hiP : IntervalIntegrable (fun z => P z * k₁ z) volume x a :=
    integrable_pos (hp.continuousOn.mul hk₁) hx hxa.le ha
  have hiA : IntervalIntegrable (fun z => a * (a - x) * k z) volume x a :=
    (integrable_pos hc hx hxa.le ha).const_mul _
  have hiB : IntervalIntegrable (fun z => (a + x) * ((a - z) * k z)) volume x a :=
    integrable_pos (continuousOn_const.mul
      ((continuousOn_const.sub continuousOn_id).mul hc)) hx hxa.le ha
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hiP.sub ((hiA.sub hiB).const_mul 2))
  rw [intervalIntegral.integral_sub hiP ((hiA.sub hiB).const_mul 2),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hiA hiB,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  dsimp [P] at he ⊢
  nlinarith only [he]

/-- Mixed partial of the lower-score derivative, written with a positive kernel. -/
theorem admittedLossLeft_hasDerivAt_right {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    HasDerivAt (fun y => admittedLossLeft k x y)
      (k x / 2 + 1 / (2 * (a - x) ^ 3) *
        ∫ z in x..a, (a - z) * ((a - x) ^ 2 + (a + x) * (z - x)) * k₁ z) a := by
  have hc := continuousOn_of_derivative_pos hk
  have hd := ((hasDerivAt_id a).div (((hasDerivAt_id a).sub_const x).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hxa.ne'))).mul
    (left_moment_hasDerivAt_right hc hx hxa ha)
  have he := admittedLoss_mixed_identity hk hk₁ hx hxa ha
  convert hd using 1
  dsimp
  rw [he]
  field_simp [sub_ne_zero.mpr hxa.ne']
  ring

/-- The five integral kernels have the signs needed along an increasing convex path. -/
theorem admittedLoss_kernel_nonneg {k k₁ : ℝ → ℝ} {x a : ℝ}
    (hx : 0 < x) (hxa : x < a)
    (hk : ∀ z ∈ Icc x a, 0 ≤ k z)
    (hk₁ : ∀ z ∈ Icc x a, 0 ≤ k₁ z) :
    0 ≤ admittedLossLeft k x a ∧
    0 ≤ admittedLossRight k x a ∧
    0 ≤ a / (a - x) ^ 3 * (∫ z in x..a, (a - z) ^ 2 * k₁ z) ∧
    0 ≤ x / (a - x) ^ 3 * (∫ z in x..a, (z - x) ^ 2 * k₁ z) ∧
    0 ≤ k x / 2 + 1 / (2 * (a - x) ^ 3) *
      (∫ z in x..a, (a - z) * ((a - x) ^ 2 + (a + x) * (z - x)) * k₁ z) := by
  have ha := hx.trans hxa
  have hb := sub_pos.mpr hxa
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply mul_nonneg (div_nonneg ha.le (sq_nonneg _))
    exact intervalIntegral.integral_nonneg hxa.le fun z hz =>
      mul_nonneg (sub_nonneg.mpr hz.2) (hk z hz)
  · apply mul_nonneg (div_nonneg hx.le (sq_nonneg _))
    exact intervalIntegral.integral_nonneg hxa.le fun z hz =>
      mul_nonneg (sub_nonneg.mpr hz.1) (hk z hz)
  · apply mul_nonneg (div_nonneg ha.le (pow_pos hb 3).le)
    exact intervalIntegral.integral_nonneg hxa.le fun z hz =>
      mul_nonneg (sq_nonneg _) (hk₁ z hz)
  · apply mul_nonneg (div_nonneg hx.le (pow_pos hb 3).le)
    exact intervalIntegral.integral_nonneg hxa.le fun z hz =>
      mul_nonneg (sq_nonneg _) (hk₁ z hz)
  · apply add_nonneg (div_nonneg (hk x ⟨le_rfl, hxa.le⟩) (by norm_num))
    apply mul_nonneg (div_nonneg (by norm_num) (mul_pos (by norm_num) (pow_pos hb 3)).le)
    apply intervalIntegral.integral_nonneg hxa.le
    intro z hz
    exact mul_nonneg (mul_nonneg (sub_nonneg.mpr hz.2)
      (add_nonneg (sq_nonneg _) (mul_nonneg (add_nonneg ha.le hx.le)
        (sub_nonneg.mpr hz.1)))) (hk₁ z hz)

private theorem integral_curve_pos {f A : ℝ → ℝ} {s x A₁ : ℝ}
    (hf : ContinuousOn f (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => ∫ z in y..A y, f z) (f (A x) * A₁ - f x) x := by
  have hd := intervalIntegral.integral_hasFDerivAt (integrable_pos hf hx hxa.le ha)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf x ⟨hx, hxa.trans ha⟩)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hf (A x) ⟨hx.trans hxa, ha⟩)
    (hf.continuousAt (Ioo_mem_nhds hx (hxa.trans ha)))
    (hf.continuousAt (Ioo_mem_nhds (hx.trans hxa) ha))
  have hp : HasDerivAt (fun y => (y, A y)) (1, A₁) x :=
    HasDerivAt.prodMk (hasDerivAt_id x) hA
  simpa [Function.comp_def, mul_comm] using hd.comp_hasDerivAt x hp

private theorem right_moment_eq {k : ℝ → ℝ} {s : ℝ}
    (hk : ContinuousOn k (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    (∫ z in x..a, (z - x) * k z) =
      (∫ z in x..a, z * k z) - x * ∫ z in x..a, k z := by
  have hiZ : IntervalIntegrable (fun z => z * k z) volume x a :=
    integrable_pos (continuousOn_id.mul hk) hx hxa.le ha
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub hiZ
      ((integrable_pos hk hx hxa.le ha).const_mul x)]
  apply intervalIntegral.integral_congr
  intro z _
  ring

private theorem curve_feasible_eventually {A : ℝ → ℝ} {s x : ℝ}
    (hx : 0 < x) (hxa : x < A x) (ha : A x < s) (hA : ContinuousAt A x) :
    ∀ᶠ y in 𝓝 x, 0 < y ∧ y < A y ∧ A y < s := by
  filter_upwards [eventually_gt_nhds hx,
    (continuousAt_id.sub hA).eventually (gt_mem_nhds (by linarith : x - A x < 0)),
    hA.eventually (gt_mem_nhds ha)] with y hy hya hys
  exact ⟨hy, by dsimp at hya; linarith, hys⟩

private theorem left_moment_hasDerivAt_curve {k A : ℝ → ℝ} {s x A₁ : ℝ}
    (hk : ContinuousOn k (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => ∫ z in y..A y, (A y - z) * k z)
      (A₁ * (∫ z in x..A x, k z) - (A x - x) * k x) x := by
  have hd := (hA.mul (integral_curve_pos hk hx hxa ha hA)).sub
    (integral_curve_pos (continuousOn_id.mul hk) hx hxa ha hA)
  have heq : (fun y => ∫ z in y..A y, (A y - z) * k z) =ᶠ[𝓝 x]
      (fun y => A y * (∫ z in y..A y, k z) - ∫ z in y..A y, z * k z) := by
    filter_upwards [curve_feasible_eventually hx hxa ha hA.continuousAt] with y hy
    exact left_moment_eq hk hy.1 hy.2.1 hy.2.2
  convert hd.congr_of_eventuallyEq heq using 1
  dsimp
  ring

private theorem right_moment_hasDerivAt_curve {k A : ℝ → ℝ} {s x A₁ : ℝ}
    (hk : ContinuousOn k (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => ∫ z in y..A y, (z - y) * k z)
      ((A x - x) * k (A x) * A₁ - ∫ z in x..A x, k z) x := by
  have hd := (integral_curve_pos (continuousOn_id.mul hk) hx hxa ha hA).sub
    ((hasDerivAt_id x).mul (integral_curve_pos hk hx hxa ha hA))
  have heq : (fun y => ∫ z in y..A y, (z - y) * k z) =ᶠ[𝓝 x]
      (fun y => (∫ z in y..A y, z * k z) - y * ∫ z in y..A y, k z) := by
    filter_upwards [curve_feasible_eventually hx hxa ha hA.continuousAt] with y hy
    exact right_moment_eq hk hy.1 hy.2.1 hy.2.2
  convert hd.congr_of_eventuallyEq heq using 1
  dsimp
  ring

/-- Pure lower-score second partial, in nonnegative-kernel form. -/
def admittedLossXX (k₁ : ℝ → ℝ) (x a : ℝ) : ℝ :=
  a / (a - x) ^ 3 * ∫ z in x..a, (a - z) ^ 2 * k₁ z

/-- Pure upper-score second partial, in nonnegative-kernel form. -/
def admittedLossAA (k₁ : ℝ → ℝ) (x a : ℝ) : ℝ :=
  x / (a - x) ^ 3 * ∫ z in x..a, (z - x) ^ 2 * k₁ z

/-- Mixed second partial, in nonnegative-kernel form. -/
def admittedLossXA (k k₁ : ℝ → ℝ) (x a : ℝ) : ℝ :=
  k x / 2 + 1 / (2 * (a - x) ^ 3) *
    ∫ z in x..a, (a - z) * ((a - x) ^ 2 + (a + x) * (z - x)) * k₁ z

private theorem admittedLossXX_eq {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    admittedLossXX k₁ x a = a / (a - x) ^ 3 *
      (-(a - x) ^ 2 * k x + 2 * ∫ z in x..a, (a - z) * k z) := by
  rw [admittedLossXX, admittedLoss_square_identity hk hk₁ hx hxa ha a]
  simp

private theorem admittedLossAA_eq {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    admittedLossAA k₁ x a = x / (a - x) ^ 3 *
      ((a - x) ^ 2 * k a - 2 * ∫ z in x..a, (z - x) * k z) := by
  have he := admittedLoss_square_identity hk hk₁ hx hxa ha x
  have heq : (∫ z in x..a, (z - x) ^ 2 * k₁ z) =
      (∫ z in x..a, (x - z) ^ 2 * k₁ z) := by
    apply intervalIntegral.integral_congr
    intro z _
    ring
  have hn : (∫ z in x..a, (x - z) * k z) =
      -(∫ z in x..a, (z - x) * k z) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  rw [admittedLossAA, heq, he, hn]
  ring

private theorem admittedLossXA_eq {k k₁ : ℝ → ℝ} {s : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) {x a : ℝ}
    (hx : 0 < x) (hxa : x < a) (ha : a < s) :
    admittedLossXA k k₁ x a =
      (a * (a - x) * (∫ z in x..a, k z) -
        (a + x) * ∫ z in x..a, (a - z) * k z) / (a - x) ^ 3 := by
  rw [admittedLossXA, admittedLoss_mixed_identity hk hk₁ hx hxa ha]
  field_simp [sub_ne_zero.mpr hxa.ne']
  ring

/-- The lower-score first partial along a moving upper score. -/
theorem admittedLossLeft_hasDerivAt_curve {k k₁ A : ℝ → ℝ} {s x A₁ : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => admittedLossLeft k y (A y))
      (admittedLossXX k₁ x (A x) + A₁ * admittedLossXA k k₁ x (A x)) x := by
  have hc := continuousOn_of_derivative_pos hk
  have hd := (hA.div ((hA.sub (hasDerivAt_id x)).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hxa.ne'))).mul
    (left_moment_hasDerivAt_curve hc hx hxa ha hA)
  convert hd using 1
  dsimp
  rw [admittedLossXX_eq hk hk₁ hx hxa ha, admittedLossXA_eq hk hk₁ hx hxa ha]
  field_simp [sub_ne_zero.mpr hxa.ne']
  ring

/-- The upper-score first partial along a moving upper score. -/
theorem admittedLossRight_hasDerivAt_curve {k k₁ A : ℝ → ℝ} {s x A₁ : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => admittedLossRight k y (A y))
      (admittedLossXA k k₁ x (A x) + A₁ * admittedLossAA k₁ x (A x)) x := by
  have hc := continuousOn_of_derivative_pos hk
  have hd := ((hasDerivAt_id x).div ((hA.sub (hasDerivAt_id x)).pow 2)
    (pow_ne_zero 2 (sub_ne_zero.mpr hxa.ne'))).mul
    (right_moment_hasDerivAt_curve hc hx hxa ha hA)
  convert hd using 1
  dsimp
  rw [admittedLossAA_eq hk hk₁ hx hxa ha, admittedLossXA_eq hk hk₁ hx hxa ha,
    left_moment_eq hc hx hxa ha, right_moment_eq hc hx hxa ha]
  field_simp [sub_ne_zero.mpr hxa.ne']
  ring

/-- Differentiating the actual admitted loss when both endpoints move. -/
theorem admittedLoss_hasDerivAt_curve {L L₁ A : ℝ → ℝ} {s x A₁ : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ContinuousOn L₁ (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A A₁ x) :
    HasDerivAt (fun y => admittedLoss L y (A y))
      (admittedLossLeft (lossSlope L₁) x (A x) +
        A₁ * admittedLossRight (lossSlope L₁) x (A x)) x := by
  have hj := continuousOn_lossIntegrand (continuousOn_of_derivative_pos hL)
  have hd := (((hasDerivAt_id x).mul hA).div (hA.sub (hasDerivAt_id x))
    (sub_ne_zero.mpr hxa.ne')).mul (integral_curve_pos hj hx hxa ha hA)
  have hn : (∫ z in x..A x, (z - x) * lossSlope L₁ z) =
      -(∫ z in x..A x, (x - z) * lossSlope L₁ z) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro z _
    ring
  convert hd using 1
  dsimp [admittedLossLeft, admittedLossRight]
  rw [hn, admittedLoss_weighted_identity hL hL₁ hx hxa ha (A x),
    admittedLoss_weighted_identity hL hL₁ hx hxa ha x]
  field_simp [sub_ne_zero.mpr hxa.ne', hx.ne', (hx.trans hxa).ne']
  ring

/-- Derivative of marginal loss per produced score. -/
def lossSlopeDeriv (L₁ L₂ : ℝ → ℝ) (z : ℝ) : ℝ :=
  (z * L₂ z - L₁ z) / z ^ 2

/-- First derivative of admitted loss along the upper-score path. -/
def admittedLossCurveSlope (k A A₁ : ℝ → ℝ) (x : ℝ) : ℝ :=
  admittedLossLeft k x (A x) + A₁ x * admittedLossRight k x (A x)

/-- Second derivative of admitted loss along the upper-score path. -/
def admittedLossCurveCurvature (k k₁ A A₁ A₂ : ℝ → ℝ) (x : ℝ) : ℝ :=
  admittedLossXX k₁ x (A x) + 2 * A₁ x * admittedLossXA k k₁ x (A x) +
    (A₁ x) ^ 2 * admittedLossAA k₁ x (A x) +
      A₂ x * admittedLossRight k x (A x)

/-- Direct differentiation of the first-derivative integral, with no aggregate
derivative supplied as an assumption. -/
theorem admittedLossCurveSlope_hasDerivAt {k k₁ A A₁ A₂ : ℝ → ℝ} {s x : ℝ}
    (hk : ∀ z ∈ Ioo 0 s, HasDerivAt k (k₁ z) z)
    (hk₁ : ContinuousOn k₁ (Ioo 0 s)) (hx : 0 < x) (hxa : x < A x)
    (ha : A x < s) (hA : HasDerivAt A (A₁ x) x)
    (hA₁ : HasDerivAt A₁ (A₂ x) x) :
    HasDerivAt (admittedLossCurveSlope k A A₁)
      (admittedLossCurveCurvature k k₁ A A₁ A₂ x) x := by
  have hd := (admittedLossLeft_hasDerivAt_curve hk hk₁ hx hxa ha hA).add
    (hA₁.mul (admittedLossRight_hasDerivAt_curve hk hk₁ hx hxa ha hA))
  convert hd using 1
  dsimp [admittedLossCurveCurvature]
  ring

/-- Every term in the curve curvature is nonnegative for an increasing convex
upper-score path and increasing marginal loss per score. -/
theorem admittedLossCurveCurvature_nonneg {k k₁ A A₁ A₂ : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (hxa : x < A x)
    (hk : ∀ z ∈ Icc x (A x), 0 ≤ k z)
    (hk₁ : ∀ z ∈ Icc x (A x), 0 ≤ k₁ z)
    (hA₁ : 0 ≤ A₁ x) (hA₂ : 0 ≤ A₂ x) :
    0 ≤ admittedLossCurveCurvature k k₁ A A₁ A₂ x := by
  obtain ⟨_, hR, hXX, hAA, hXA⟩ := admittedLoss_kernel_nonneg hx hxa hk hk₁
  exact add_nonneg
    (add_nonneg (add_nonneg hXX (mul_nonneg (mul_nonneg (by norm_num) hA₁) hXA))
      (mul_nonneg (sq_nonneg _) hAA)) (mul_nonneg hA₂ hR)

/-- Primitive loss regularity and `z L'' ≥ L' ≥ 0` imply nonnegative actual
admitted-loss curvature along every increasing convex twice-differentiable
upper-score path. The primitive functions need only be regular below `s`. -/
theorem admittedLoss_curve_derivatives_and_nonneg
    {L L₁ L₂ A A₁ A₂ : ℝ → ℝ} {s x : ℝ}
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ∀ z ∈ Ioo 0 s, HasDerivAt L₁ (L₂ z) z)
    (hL₂ : ContinuousOn L₂ (Ioo 0 s))
    (hLpos : ∀ z ∈ Ioo 0 s, 0 ≤ L₁ z)
    (hLcurv : ∀ z ∈ Ioo 0 s, L₁ z ≤ z * L₂ z)
    (hx : 0 < x) (hxa : x < A x) (ha : A x < s)
    (hA : HasDerivAt A (A₁ x) x) (hA₁ : HasDerivAt A₁ (A₂ x) x)
    (hApos : 0 ≤ A₁ x) (hAconv : 0 ≤ A₂ x) :
    HasDerivAt (fun y => admittedLoss L y (A y))
      (admittedLossCurveSlope (lossSlope L₁) A A₁ x) x ∧
    HasDerivAt (admittedLossCurveSlope (lossSlope L₁) A A₁)
      (admittedLossCurveCurvature (lossSlope L₁) (lossSlopeDeriv L₁ L₂)
        A A₁ A₂ x) x ∧
    0 ≤ admittedLossCurveCurvature (lossSlope L₁) (lossSlopeDeriv L₁ L₂)
      A A₁ A₂ x := by
  have hc := continuousOn_of_derivative_pos hL₁
  have hk : ∀ z ∈ Ioo 0 s, HasDerivAt (lossSlope L₁) (lossSlopeDeriv L₁ L₂ z) z :=
    fun z hz => hasDerivAt_lossSlope hz.1 (hL₁ z hz)
  have hk₁ : ContinuousOn (lossSlopeDeriv L₁ L₂) (Ioo 0 s) :=
    ((continuousOn_id.mul hL₂).sub hc).div (continuousOn_id.pow 2)
      fun _ hz => pow_ne_zero 2 hz.1.ne'
  refine ⟨admittedLoss_hasDerivAt_curve hL hc hx hxa ha hA,
    admittedLossCurveSlope_hasDerivAt hk hk₁ hx hxa ha hA hA₁, ?_⟩
  apply admittedLossCurveCurvature_nonneg hx hxa _ _ hApos hAconv
  · intro z hz
    have hz' : z ∈ Ioo 0 s := ⟨hx.trans_le hz.1, hz.2.trans_lt ha⟩
    exact div_nonneg (hLpos z hz') hz'.1.le
  · intro z hz
    have hz' : z ∈ Ioo 0 s := ⟨hx.trans_le hz.1, hz.2.trans_lt ha⟩
    exact div_nonneg (sub_nonneg.mpr (hLcurv z hz')) (sq_nonneg _)

/-- The actual admitted-population average loss is convex along an arbitrary
increasing convex twice-differentiable score path. This conclusion is derived
from primitive loss derivatives and the interval integral defining the average. -/
theorem admittedLoss_convexOn_curve
    {L L₁ L₂ A A₁ A₂ : ℝ → ℝ} {s : ℝ} {D : Set ℝ}
    (hD : Convex ℝ D)
    (hL : ∀ z ∈ Ioo 0 s, HasDerivAt L (L₁ z) z)
    (hL₁ : ∀ z ∈ Ioo 0 s, HasDerivAt L₁ (L₂ z) z)
    (hL₂ : ContinuousOn L₂ (Ioo 0 s))
    (hLpos : ∀ z ∈ Ioo 0 s, 0 ≤ L₁ z)
    (hLcurv : ∀ z ∈ Ioo 0 s, L₁ z ≤ z * L₂ z)
    (hfeas : ∀ x ∈ D, 0 < x ∧ x < A x ∧ A x < s)
    (hA : ∀ x ∈ D, HasDerivAt A (A₁ x) x)
    (hA₁ : ∀ x ∈ D, HasDerivAt A₁ (A₂ x) x)
    (hApos : ∀ x ∈ D, 0 ≤ A₁ x) (hAconv : ∀ x ∈ D, 0 ≤ A₂ x) :
    ConvexOn ℝ D (fun x => admittedLoss L x (A x)) := by
  have hall (x : ℝ) (hx : x ∈ D) := admittedLoss_curve_derivatives_and_nonneg
    hL hL₁ hL₂ hLpos hLcurv (hfeas x hx).1 (hfeas x hx).2.1
    (hfeas x hx).2.2 (hA x hx) (hA₁ x hx) (hApos x hx) (hAconv x hx)
  exact convexOn_of_hasDerivWithinAt2_nonneg hD
    (fun x hx => (hall x hx).1.continuousAt.continuousWithinAt)
    (fun x hx => (hall x (interior_subset hx)).1.hasDerivWithinAt)
    (fun x hx => (hall x (interior_subset hx)).2.1.hasDerivWithinAt)
    (fun x hx => (hall x (interior_subset hx)).2.2)

end
end LBG22StrategicRanking
