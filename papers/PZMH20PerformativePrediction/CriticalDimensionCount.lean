import AppliedModelingLib.Foundations.Probability.EuclideanDyadicShellConcentration

/-!
# Explicit critical-dimensional sample count

The reusable dimension-two compact-head certificate contains the exact term
`depth N / sqrt N`.  The general all-dimensional selector bounds this term by
`N⁻¹˙²⁵`, which is convenient but loses the critical logarithmic rate.
Here we retain the exact logarithmic depth and give it the explicit count
`(C / r * log (C / r))²`.  The small-radius hypothesis is stated openly; it
is exactly the regime in which `C / r ≥ exp 2` and `log x / sqrt x` is
decreasing.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib

/-- The dimension-two effective depth is at most `log N / log 4` once the
count is large enough for the dyadic construction.  This is the exact
logarithmic estimate used before the conservative quarter-power bound in the
general all-dimensional selector. -/
theorem dyadicEffectiveCountDepth_two_le_log_count
    (count : ℕ) (hcount : 64 ≤ count) :
    (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) ≤
      Real.log (count : ℝ) / Real.log 4 := by
  have hlogFour_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hcount_real : (64 : ℝ) ≤ count := by exact_mod_cast hcount
  have hcount_pos : 0 < (count : ℝ) := lt_of_lt_of_le (by norm_num) hcount_real
  have hratio_one : 1 ≤ (count : ℝ) / 64 := by
    apply (one_le_div (by norm_num : (0 : ℝ) < 64)).mpr
    simpa using hcount_real
  have hratio_pos : 0 < (count : ℝ) / 64 := lt_of_lt_of_le zero_lt_one hratio_one
  have hlog_nonneg : 0 ≤ Real.logb 4 ((count : ℝ) / 64) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg hratio_one) hlogFour_pos.le
  have hratio_le : (count : ℝ) / 64 ≤ count := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 64)).mpr
    nlinarith
  have hfloor : (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) ≤
      Real.logb 4 ((count : ℝ) / 64) := by
    change (Nat.floor (Real.logb 4 (((count : ℝ) / 16) / 4)) : ℝ) ≤ _
    convert Nat.floor_le hlog_nonneg using 1 <;> ring
  calc
    (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) ≤
        Real.logb 4 ((count : ℝ) / 64) := hfloor
    _ ≤ Real.logb 4 (count : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hratio_pos hratio_le
    _ = Real.log (count : ℝ) / Real.log 4 := by rw [Real.logb]

/-- One coefficient simultaneously pays for the central critical-depth term
and for the same term multiplied by the radial-tail factor. -/
noncomputable def criticalDimensionDepthCoefficient (tailConstant : ℝ) : ℝ :=
  (96 / Real.log 4) *
    max 1 (Probability.selectedShellGeometricTailMultiplier tailConstant)

/-- The real `r⁻² log²(C/r)` threshold used by the critical selector. -/
noncomputable def criticalDimensionLogSquaredThreshold
    (tailConstant radius : ℝ) : ℝ :=
  let ratio := criticalDimensionDepthCoefficient tailConstant / radius
  (ratio * Real.log ratio) ^ 2

/-- A positive concrete critical-dimensional count.  The fixed `64` gate is
the exact base-count premise of the dyadic depth estimate. -/
noncomputable def criticalDimensionLogSquaredCount
    (tailConstant radius : ℝ) : ℕ :=
  Math.positiveNatCeil
    (max 64 (criticalDimensionLogSquaredThreshold tailConstant radius))

theorem criticalDimensionDepthCoefficient_pos (tailConstant : ℝ) :
    0 < criticalDimensionDepthCoefficient tailConstant := by
  unfold criticalDimensionDepthCoefficient
  have hlogFour_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hmax_pos : 0 < max 1
      (Probability.selectedShellGeometricTailMultiplier tailConstant) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  positivity

theorem criticalDimensionLogSquaredCount_pos (tailConstant radius : ℝ) :
    0 < criticalDimensionLogSquaredCount tailConstant radius := by
  exact lt_of_lt_of_le zero_lt_one
    (Math.one_le_positiveNatCeil
      (max 64 (criticalDimensionLogSquaredThreshold tailConstant radius)))

/-- In the honest small-radius regime, the concrete natural count is within
one of its displayed `r⁻² log²(C/r)` real threshold. -/
theorem criticalDimensionLogSquaredCount_bounds
    (tailConstant : ℝ) {radius : ℝ} (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant) :
    criticalDimensionLogSquaredThreshold tailConstant radius ≤
        criticalDimensionLogSquaredCount tailConstant radius ∧
      (criticalDimensionLogSquaredCount tailConstant radius : ℝ) <
        criticalDimensionLogSquaredThreshold tailConstant radius + 1 := by
  let coefficient := criticalDimensionDepthCoefficient tailConstant
  let ratio := coefficient / radius
  let threshold := (ratio * Real.log ratio) ^ 2
  have hcoefficient_pos : 0 < coefficient := by
    dsimp [coefficient]
    exact criticalDimensionDepthCoefficient_pos tailConstant
  have hratio_exp : Real.exp 2 ≤ ratio := by
    dsimp [ratio]
    exact (le_div_iff₀ hradius).mpr (by simpa [mul_comm] using hsmall)
  have hratio_pos : 0 < ratio := div_pos hcoefficient_pos hradius
  have hlog_ratio : 2 ≤ Real.log ratio := by
    have hlog := Real.log_le_log (Real.exp_pos 2) hratio_exp
    simpa using hlog
  have hexp_one : 2 ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1 <;> norm_num
  have hexp_two : 4 ≤ Real.exp 2 := by
    calc
      (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hexp_one 2
      _ = Real.exp 2 := by
        rw [← Real.exp_nat_mul]
        norm_num
  have hproduct : 8 ≤ ratio * Real.log ratio := by
    calc
      (8 : ℝ) = 4 * 2 := by norm_num
      _ ≤ ratio * Real.log ratio :=
        mul_le_mul (hexp_two.trans hratio_exp) hlog_ratio (by norm_num) hratio_pos.le
  have hthreshold64 : (64 : ℝ) ≤ threshold := by
    dsimp [threshold]
    nlinarith [sq_nonneg (ratio * Real.log ratio - 8)]
  have hthreshold_nonneg : 0 ≤ threshold := sq_nonneg _
  have hlower : threshold ≤
      criticalDimensionLogSquaredCount tailConstant radius := by
    calc
      threshold ≤ max 64 threshold := le_max_right _ _
      _ ≤ Math.positiveNatCeil (max 64 threshold) :=
        Math.le_positiveNatCeil _
      _ = criticalDimensionLogSquaredCount tailConstant radius := by
        simp only [criticalDimensionLogSquaredCount,
          criticalDimensionLogSquaredThreshold, coefficient, ratio, threshold]
  constructor
  · simpa only [criticalDimensionLogSquaredThreshold, coefficient, ratio, threshold] using hlower
  · have hmax64 : max (64 : ℝ) threshold = threshold := max_eq_right hthreshold64
    have hmaxOne : max (1 : ℝ) threshold = threshold :=
      max_eq_right (by linarith)
    unfold criticalDimensionLogSquaredCount Math.positiveNatCeil
    rw [show criticalDimensionLogSquaredThreshold tailConstant radius = threshold by
      simp only [criticalDimensionLogSquaredThreshold, coefficient, ratio, threshold]]
    rw [hmax64, hmaxOne]
    exact Nat.ceil_lt_add_one hthreshold_nonneg

/-- The explicit critical count makes `log N / sqrt N` at most `4r/C`.
This is the analytic inversion that the conservative all-dimensional selector
replaces by a quarter-power estimate. -/
theorem log_count_div_sqrt_criticalDimensionLogSquaredCount_le
    (tailConstant : ℝ) {radius : ℝ} (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant) :
    Real.log (criticalDimensionLogSquaredCount tailConstant radius : ℝ) /
        Real.sqrt (criticalDimensionLogSquaredCount tailConstant radius : ℝ) ≤
      4 * radius / criticalDimensionDepthCoefficient tailConstant := by
  let coefficient := criticalDimensionDepthCoefficient tailConstant
  let ratio := coefficient / radius
  let logarithm := Real.log ratio
  let threshold := (ratio * logarithm) ^ 2
  let count := criticalDimensionLogSquaredCount tailConstant radius
  have hcoefficient_pos : 0 < coefficient := by
    dsimp [coefficient]
    exact criticalDimensionDepthCoefficient_pos tailConstant
  have hratio_exp : Real.exp 2 ≤ ratio := by
    dsimp [ratio]
    exact (le_div_iff₀ hradius).mpr (by simpa [mul_comm] using hsmall)
  have hratio_pos : 0 < ratio := div_pos hcoefficient_pos hradius
  have hlogarithm : 2 ≤ logarithm := by
    dsimp [logarithm]
    have hlog := Real.log_le_log (Real.exp_pos 2) hratio_exp
    simpa using hlog
  have hlogarithm_pos : 0 < logarithm := lt_of_lt_of_le (by norm_num) hlogarithm
  have hproduct_pos : 0 < ratio * logarithm := mul_pos hratio_pos hlogarithm_pos
  have hthreshold_exp : Real.exp 2 ≤ threshold := by
    have hexp_nonneg : 0 ≤ Real.exp 2 := (Real.exp_pos 2).le
    have hexp_one : 1 ≤ Real.exp 2 := by
      simpa using (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2))
    have hproduct_exp : Real.exp 2 ≤ ratio * logarithm := by
      calc
        Real.exp 2 ≤ Real.exp 2 * 2 := by nlinarith [Real.exp_pos 2]
        _ ≤ ratio * logarithm :=
          mul_le_mul hratio_exp hlogarithm (by norm_num) hratio_pos.le
    dsimp [threshold]
    nlinarith [sq_nonneg (ratio * logarithm - 1)]
  have hthreshold_le_count : threshold ≤ (count : ℝ) := by
    dsimp [threshold, logarithm, ratio, coefficient, count]
    exact (criticalDimensionLogSquaredCount_bounds tailConstant hradius hsmall).1
  have hcount_exp : Real.exp 2 ≤ (count : ℝ) :=
    hthreshold_exp.trans hthreshold_le_count
  have hantitone :
      Real.log (count : ℝ) / Real.sqrt (count : ℝ) ≤
        Real.log threshold / Real.sqrt threshold :=
    Real.log_div_sqrt_antitoneOn hthreshold_exp hcount_exp hthreshold_le_count
  have hlog_logarithm_le : Real.log logarithm ≤ logarithm :=
    Real.log_le_self hlogarithm_pos.le
  have hlog_threshold_le : Real.log threshold ≤ 4 * logarithm := by
    have hlog_product : Real.log (ratio * logarithm) =
        Real.log ratio + Real.log logarithm :=
      Real.log_mul hratio_pos.ne' hlogarithm_pos.ne'
    dsimp [threshold]
    rw [Real.log_pow, hlog_product]
    dsimp [logarithm]
    linarith
  have hsqrt_threshold : Real.sqrt threshold = ratio * logarithm := by
    dsimp [threshold]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hproduct_pos]
  have hthreshold_rate : Real.log threshold / Real.sqrt threshold ≤ 4 / ratio := by
    rw [hsqrt_threshold]
    calc
      Real.log threshold / (ratio * logarithm) ≤
          (4 * logarithm) / (ratio * logarithm) :=
        div_le_div_of_nonneg_right hlog_threshold_le hproduct_pos.le
      _ = 4 / ratio := by field_simp [hratio_pos.ne', hlogarithm_pos.ne']
  calc
    Real.log (criticalDimensionLogSquaredCount tailConstant radius : ℝ) /
        Real.sqrt (criticalDimensionLogSquaredCount tailConstant radius : ℝ) =
        Real.log (count : ℝ) / Real.sqrt (count : ℝ) := by rfl
    _ ≤ Real.log threshold / Real.sqrt threshold := hantitone
    _ ≤ 4 / ratio := hthreshold_rate
    _ = 4 * radius / criticalDimensionDepthCoefficient tailConstant := by
      dsimp [ratio, coefficient]
      field_simp [hradius.ne', (criticalDimensionDepthCoefficient_pos tailConstant).ne']
      <;> ring

/-- The critical selector discharges both exact logarithmic-depth components:
the central one and the one multiplied by the radial-tail factor. -/
theorem criticalDimensionLogSquaredCount_depth_gates
    (tailConstant : ℝ) {radius : ℝ} (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant) :
    let count := criticalDimensionLogSquaredCount tailConstant radius
    4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤ radius / 6 ∧
      (4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ)) *
          Probability.selectedShellGeometricTailMultiplier tailConstant ≤ radius / 6 := by
  dsimp only
  let count := criticalDimensionLogSquaredCount tailConstant radius
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailConstant
  let multiplier := max 1 tailMultiplier
  have hcount_pos : 0 < count := criticalDimensionLogSquaredCount_pos tailConstant radius
  have hcount64 : 64 ≤ count := by
    have hreal : (64 : ℝ) ≤ count := by
      calc
        (64 : ℝ) ≤ max 64 (criticalDimensionLogSquaredThreshold tailConstant radius) :=
          le_max_left _ _
        _ ≤ count := Math.le_positiveNatCeil _
    exact_mod_cast hreal
  have hsqrt_pos : 0 < Real.sqrt (count : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hcount_pos)
  have hdepth_le_log := dyadicEffectiveCountDepth_two_le_log_count count hcount64
  have hdepth_div :
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
        (1 / Real.log 4) *
          (Real.log (count : ℝ) / Real.sqrt (count : ℝ)) := by
    calc
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
          (Real.log (count : ℝ) / Real.log 4) /
            Real.sqrt (count : ℝ) :=
        div_le_div_of_nonneg_right hdepth_le_log hsqrt_pos.le
      _ = (1 / Real.log 4) *
          (Real.log (count : ℝ) / Real.sqrt (count : ℝ)) := by ring
  have hlog_rate :=
    log_count_div_sqrt_criticalDimensionLogSquaredCount_le tailConstant hradius hsmall
  have hlogFour_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hdepth_rate :
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
        4 * radius /
          (criticalDimensionDepthCoefficient tailConstant * Real.log 4) := by
    calc
      (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤
          (1 / Real.log 4) *
            (Real.log (count : ℝ) / Real.sqrt (count : ℝ)) := hdepth_div
      _ ≤ (1 / Real.log 4) *
          (4 * radius / criticalDimensionDepthCoefficient tailConstant) :=
        mul_le_mul_of_nonneg_left hlog_rate (one_div_nonneg.mpr hlogFour_pos.le)
      _ = 4 * radius /
          (criticalDimensionDepthCoefficient tailConstant * Real.log 4) := by ring
  have hmultiplier_one : 1 ≤ multiplier := le_max_left _ _
  have hmultiplier_pos : 0 < multiplier := lt_of_lt_of_le zero_lt_one hmultiplier_one
  have htail_nonneg : 0 ≤ tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have htail_le : tailMultiplier ≤ multiplier := le_max_right _ _
  have hraw :
      4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤ radius / (6 * multiplier) := by
    calc
      4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) =
          4 * ((Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
            Real.sqrt (count : ℝ)) := by ring
      _ ≤ 4 * (4 * radius /
          (criticalDimensionDepthCoefficient tailConstant * Real.log 4)) :=
        mul_le_mul_of_nonneg_left hdepth_rate (by norm_num)
      _ = radius / (6 * multiplier) := by
        dsimp [criticalDimensionDepthCoefficient, multiplier, tailMultiplier]
        field_simp [hlogFour_pos.ne', hmultiplier_pos.ne']
        <;> ring
  constructor
  · calc
      4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ) ≤ radius / (6 * multiplier) := hraw
      _ ≤ radius / 6 := by
        exact div_le_div_of_nonneg_left hradius.le (by norm_num)
          (by nlinarith [hmultiplier_one])
  · calc
      (4 * (Math.dyadicEffectiveCountDepth 2 ((count : ℝ) / 16) : ℝ) /
          Real.sqrt (count : ℝ)) * tailMultiplier ≤
          (radius / (6 * multiplier)) * tailMultiplier :=
        mul_le_mul_of_nonneg_right hraw htail_nonneg
      _ ≤ (radius / (6 * multiplier)) * multiplier := by
        exact mul_le_mul_of_nonneg_left htail_le (by positivity)
      _ = radius / 6 := by field_simp [hmultiplier_pos.ne']

/-- Composition with the existing exact dimension-two head certificate.  The
four non-depth requirements remain visible as the same quadratic/linear gates
used by the general selector; only the two logarithmic gates are discharged
by the new concrete count. -/
theorem selectedShellGeometricHeadSchedule_dimensionTwo_le_of_criticalCount
    (cutoff : ℕ) (confidence tailConstant : ℝ) {radius : ℝ}
    (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailConstant)
    (hcentralRootGate :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 ≤
        (criticalDimensionLogSquaredCount tailConstant radius : ℝ) * radius ^ 2)
    (hcentralCountGate :
      6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence ≤
        (criticalDimensionLogSquaredCount tailConstant radius : ℝ) * radius)
    (hsuccessorRootGate :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff confidence
            tailConstant ^ 2 ≤
        (criticalDimensionLogSquaredCount tailConstant radius : ℝ) * radius ^ 2)
    (hsuccessorSqrtGate :
      6 ^ 2 *
          Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff confidence
            tailConstant ^ 2 ≤
        (criticalDimensionLogSquaredCount tailConstant radius : ℝ) * radius ^ 2) :
    Probability.selectedShellGeometricHeadSchedule_dimensionTwo cutoff
        (criticalDimensionLogSquaredCount tailConstant radius) confidence tailConstant ≤
      ENNReal.ofReal radius := by
  let count := criticalDimensionLogSquaredCount tailConstant radius
  have hcount_pos : 0 < count := criticalDimensionLogSquaredCount_pos tailConstant radius
  obtain ⟨hcentralDepth, hsuccessorDepth⟩ :=
    criticalDimensionLogSquaredCount_depth_gates tailConstant hradius hsmall
  apply Probability.selectedShellGeometricHeadSchedule_dimensionTwo_le_of_sixth_component_bounds
    cutoff count confidence tailConstant radius hradius.le
  · exact AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount_pos
      (Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient_nonneg confidence)
      hradius.le (by norm_num) hcentralRootGate
  · exact hcentralDepth
  · exact AppliedModelingLib.Math.div_nat_le_div_of_mul_le count hcount_pos (by norm_num)
      hcentralCountGate
  · exact AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount_pos
      (Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient_nonneg cutoff
        confidence tailConstant) hradius.le (by norm_num) hsuccessorRootGate
  · exact hsuccessorDepth
  · exact AppliedModelingLib.Math.div_sqrt_nat_le_div_of_sq_mul_le count hcount_pos
      (Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient_nonneg cutoff
        confidence tailConstant) hradius.le (by norm_num) hsuccessorSqrtGate

end PZMH20PerformativePrediction
