import PZMH20PerformativePrediction.CriticalDimensionSampleCount

/-!
# Sharp dimension-two actual-count rates

This file bounds the actual natural count selected by the sharp critical
schedule.  The radius factor is `r⁻² (1 + log (C/r))²`; the round factor is
the honest shifted logarithm from `SampleCountRates`.  The existing
all-dimensional selector remains the separate conservative `r⁻⁴` route in
dimension two.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib

/-- The positive radius logarithm used by the critical-dimensional rate. -/
noncomputable def criticalDimensionShiftedRadiusLog
    (tailBound radius : ℝ) : ℝ :=
  1 + Real.log (criticalDimensionDepthCoefficient tailBound / radius)

theorem criticalDimensionShiftedRadiusLog_three_le
    (tailBound : ℝ) {radius : ℝ} (hradius : 0 < radius)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound) :
    3 ≤ criticalDimensionShiftedRadiusLog tailBound radius := by
  have hratio : Real.exp 2 ≤ criticalDimensionDepthCoefficient tailBound / radius := by
    exact (le_div_iff₀ hradius).mpr (by simpa [mul_comm] using hsmall)
  have hlog := Real.log_le_log (Real.exp_pos 2) hratio
  rw [Real.log_exp] at hlog
  unfold criticalDimensionShiftedRadiusLog
  simpa using (show (3 : ℝ) ≤ 1 +
      Real.log (criticalDimensionDepthCoefficient tailBound / radius) by linarith)

theorem one_le_criticalDimensionDepthCoefficient (tailBound : ℝ) :
    1 ≤ criticalDimensionDepthCoefficient tailBound := by
  have hlogFour_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogFour_le_three : Real.log 4 ≤ 3 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4) using 1 <;>
      norm_num
  have hquotient : 1 ≤ 96 / Real.log 4 := by
    apply (le_div_iff₀ hlogFour_pos).mpr
    linarith
  have hmultiplier : 1 ≤ max 1
      (Probability.selectedShellGeometricTailMultiplier tailBound) := le_max_left _ _
  unfold criticalDimensionDepthCoefficient
  nlinarith [mul_nonneg (sub_nonneg.mpr hquotient) (sub_nonneg.mpr hmultiplier)]

/-- The concrete source cutoff is only logarithmic in the inverse radius.
After multiplication by `log 2`, it is controlled by the same shifted radius
logarithm used in the sharp count. -/
theorem criticalDimensionHeadCutoff_add_one_mul_log_two_le
    {eta radius tailBound : ℝ} (heta : 0 < eta)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
        Real.log 2 ≤
      (2 * Real.log 2 + 1) * criticalDimensionShiftedRadiusLog tailBound radius := by
  let delta : ℝ := 1 / (2 * (1 + eta))
  let threshold : ℝ := Real.rpow radius (-delta)
  let logarithm : ℝ := Real.log
    (criticalDimensionDepthCoefficient tailBound / radius)
  have hlogTwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdelta_pos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdelta_le_one : delta ≤ 1 := by
    dsimp [delta]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * (1 + eta))).mpr
    linarith
  have hthreshold_one : 1 ≤ threshold := by
    dsimp [threshold]
    calc
      1 = Real.rpow radius 0 := by
        rw [Real.rpow_eq_pow, Real.rpow_zero]
      _ ≤ Real.rpow radius (-delta) :=
        Real.rpow_le_rpow_of_exponent_ge hradius hradius_le_one (by linarith)
  have hlogb_nonneg : 0 ≤ Real.logb 2 threshold := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg hthreshold_one) hlogTwo_pos.le
  have hceil_lt :
      (Probability.pOneFournierGuillinHeadCutoff eta radius : ℝ) <
        Real.logb 2 threshold + 1 := by
    unfold Probability.pOneFournierGuillinHeadCutoff
    change (Nat.ceil (Real.logb 2 threshold) : ℝ) < Real.logb 2 threshold + 1
    exact Nat.ceil_lt_add_one hlogb_nonneg
  have hnegLog_nonneg : 0 ≤ -Real.log radius := by
    exact neg_nonneg.mpr (Real.log_nonpos hradius.le hradius_le_one)
  have hlogb_eq : Real.logb 2 threshold =
      delta * (-Real.log radius) / Real.log 2 := by
    unfold Real.logb
    dsimp [threshold]
    rw [Real.log_rpow hradius]
    ring
  have hcoefficient_one := one_le_criticalDimensionDepthCoefficient tailBound
  have hcoefficient_pos := lt_of_lt_of_le zero_lt_one hcoefficient_one
  have hlogarithm_nonneg : 0 ≤ logarithm := by
    dsimp [logarithm]
    apply Real.log_nonneg
    apply (one_le_div hradius).mpr
    exact hradius_le_one.trans hcoefficient_one
  have hnegLog_le : -Real.log radius ≤ logarithm := by
    dsimp [logarithm]
    rw [Real.log_div hcoefficient_pos.ne' hradius.ne']
    have hlogCoefficient : 0 ≤ Real.log (criticalDimensionDepthCoefficient tailBound) :=
      Real.log_nonneg hcoefficient_one
    linarith
  have hcutoff_log :
      ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
          Real.log 2 < delta * (-Real.log radius) + 2 * Real.log 2 := by
    rw [hlogb_eq] at hceil_lt
    have hscaled := mul_lt_mul_of_pos_right hceil_lt hlogTwo_pos
    calc
      ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
          Real.log 2 =
          (Probability.pOneFournierGuillinHeadCutoff eta radius : ℝ) * Real.log 2 +
            Real.log 2 := by push_cast; ring
      _ < (delta * (-Real.log radius) / Real.log 2 + 1) * Real.log 2 +
            Real.log 2 := by
        simpa [add_comm] using add_lt_add_right hscaled (Real.log 2)
      _ = delta * (-Real.log radius) + 2 * Real.log 2 := by
        field_simp [hlogTwo_pos.ne']
        <;> ring
  have hdeltaLog_le : delta * (-Real.log radius) ≤ logarithm := by
    calc
      delta * (-Real.log radius) ≤ 1 * (-Real.log radius) :=
        mul_le_mul_of_nonneg_right hdelta_le_one hnegLog_nonneg
      _ ≤ logarithm := by simpa using hnegLog_le
  have hshifted : criticalDimensionShiftedRadiusLog tailBound radius = 1 + logarithm := by
    rfl
  have hfactor_nonneg : 0 ≤ 2 * Real.log 2 + 1 := by positivity
  rw [hshifted]
  calc
    ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
        Real.log 2 ≤ delta * (-Real.log radius) + 2 * Real.log 2 := hcutoff_log.le
    _ ≤ logarithm + 2 * Real.log 2 := by linarith
    _ ≤ (2 * Real.log 2 + 1) * (1 + logarithm) := by
      nlinarith

/-- The sharp critical count specialized to the source's inverse-square round
allocation and the natural dimension-two cutoff. -/
noncomputable def criticalDimensionRateCountSchedule
    (eta alpha gamma tailBound radius p : ℝ) : ℕ → ℕ := fun round =>
  criticalDimensionAllShellEffectiveCount
    (Probability.pOneFournierGuillinHeadCutoff eta radius)
    eta alpha gamma tailBound
    (radius / Real.rpow 2 (-(1 + eta))) radius
    (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
    radius (theorem310FailureBudget p round / 2)

/-- The sharp critical schedule has a nonempty batch at every round. -/
theorem criticalDimensionRateCountSchedule_pos
    (eta alpha gamma tailBound radius p : ℝ) (round : ℕ) :
    0 < criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round := by
  unfold criticalDimensionRateCountSchedule
  exact lt_of_lt_of_le zero_lt_one
    (one_le_criticalDimensionAllShellEffectiveCount
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound (radius / Real.rpow 2 (-(1 + eta))) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2))

/-- A parameter-only coefficient for the sharp critical head, all-shell mass,
and source square-rate gates. -/
noncomputable def criticalDimensionSampleRateConstant
    (eta alpha gamma tailBound : ℝ) : ℝ :=
  let roundCoefficient := theorem310RoundLogCoefficient
  let radiusCoefficient := criticalDimensionDepthCoefficient tailBound
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := roundCoefficient + Real.log 2
  let successorLogCoefficient := roundCoefficient + (2 * Real.log 2 + 1)
  1 +
    (radiusCoefficient ^ 2 + 1) +
    6 ^ 2 * (2 * (32 * Real.sqrt 2) ^ 2 + 16 * centralLogCoefficient) +
    6 * (2 * Real.sqrt 2 * (64 + 8 * centralLogCoefficient)) +
    6 ^ 2 *
      (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
        tailMultiplier ^ 2 +
    6 ^ 2 * (512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2 +
    roundCoefficient / (2 * (shellCoefficient / decay) ^ 2) +
    roundCoefficient / (shellCoefficient ^ 2 / (18 * tailBound)) +
    roundCoefficient / (shellCoefficient * decay * Real.log 9 / 4) +
    roundCoefficient / (shellCoefficient * gamma / 4) +
    1 / (shellCoefficient ^ 2 / (18 * tailBound)) +
    1 / (shellCoefficient * decay * Real.log 9 / 8) +
    1 / ((shellCoefficient * gamma / 4) *
      (Real.rpow 2 (alpha - 1 - eta) - 1))

theorem criticalDimensionSampleRateConstant_pos
    {eta alpha gamma tailBound : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound) :
    0 < criticalDimensionSampleRateConstant eta alpha gamma tailBound := by
  have hround : 0 < theorem310RoundLogCoefficient := theorem310RoundLogCoefficient_pos
  have hradius : 0 < criticalDimensionDepthCoefficient tailBound :=
    criticalDimensionDepthCoefficient_pos tailBound
  have hdecay : 0 < Real.rpow 2 (-(1 + eta)) := Real.rpow_pos_of_pos (by norm_num) _
  have hshell : 0 < Probability.pOneFournierGuillinShellCoefficient eta :=
    Probability.pOneFournierGuillinShellCoefficient_pos heta
  have htail : 0 < Probability.selectedShellGeometricTailMultiplier tailBound := by
    unfold Probability.selectedShellGeometricTailMultiplier
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
  unfold criticalDimensionSampleRateConstant
  dsimp only
  have hcentral : 0 < theorem310RoundLogCoefficient + Real.log 2 := by positivity
  have hsuccessor : 0 < theorem310RoundLogCoefficient + (2 * Real.log 2 + 1) := by
    positivity
  positivity

theorem one_le_criticalDimensionSampleRateConstant
    {eta alpha gamma tailBound : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound) :
    1 ≤ criticalDimensionSampleRateConstant eta alpha gamma tailBound := by
  have hround : 0 < theorem310RoundLogCoefficient := theorem310RoundLogCoefficient_pos
  have hradius : 0 < criticalDimensionDepthCoefficient tailBound :=
    criticalDimensionDepthCoefficient_pos tailBound
  have hdecay : 0 < Real.rpow 2 (-(1 + eta)) := Real.rpow_pos_of_pos (by norm_num) _
  have hshell : 0 < Probability.pOneFournierGuillinShellCoefficient eta :=
    Probability.pOneFournierGuillinShellCoefficient_pos heta
  have htail : 0 < Probability.selectedShellGeometricTailMultiplier tailBound := by
    unfold Probability.selectedShellGeometricTailMultiplier
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
  unfold criticalDimensionSampleRateConstant
  dsimp only
  have hcentral : 0 < theorem310RoundLogCoefficient + Real.log 2 := by positivity
  have hsuccessor : 0 < theorem310RoundLogCoefficient + (2 * Real.log 2 + 1) := by
    positivity
  have hnonneg : 0 ≤
      (criticalDimensionDepthCoefficient tailBound ^ 2 + 1) +
      6 ^ 2 * (2 * (32 * Real.sqrt 2) ^ 2 +
        16 * (theorem310RoundLogCoefficient + Real.log 2)) +
      6 * (2 * Real.sqrt 2 *
        (64 + 8 * (theorem310RoundLogCoefficient + Real.log 2))) +
      6 ^ 2 *
        (2 * (32 * Real.sqrt 2) ^ 2 +
          16 * (theorem310RoundLogCoefficient + (2 * Real.log 2 + 1))) *
          Probability.selectedShellGeometricTailMultiplier tailBound ^ 2 +
      6 ^ 2 *
        (512 + 64 * (theorem310RoundLogCoefficient + (2 * Real.log 2 + 1))) *
          Probability.selectedShellGeometricTailMultiplier tailBound ^ 2 +
      theorem310RoundLogCoefficient /
        (2 * (Probability.pOneFournierGuillinShellCoefficient eta /
          Real.rpow 2 (-(1 + eta))) ^ 2) +
      theorem310RoundLogCoefficient /
        (Probability.pOneFournierGuillinShellCoefficient eta ^ 2 / (18 * tailBound)) +
      theorem310RoundLogCoefficient /
        (Probability.pOneFournierGuillinShellCoefficient eta *
          Real.rpow 2 (-(1 + eta)) * Real.log 9 / 4) +
      theorem310RoundLogCoefficient /
        (Probability.pOneFournierGuillinShellCoefficient eta * gamma / 4) +
      1 / (Probability.pOneFournierGuillinShellCoefficient eta ^ 2 / (18 * tailBound)) +
      1 / (Probability.pOneFournierGuillinShellCoefficient eta *
        Real.rpow 2 (-(1 + eta)) * Real.log 9 / 8) +
      1 / ((Probability.pOneFournierGuillinShellCoefficient eta * gamma / 4) *
        (Real.rpow 2 (alpha - 1 - eta) - 1)) := by
    positivity
  linarith

set_option maxHeartbeats 1000000 in
/-- The complete real max requirement of the sharp critical schedule has the
source rate `r⁻² log²(C/r)` times the honest shifted round logarithm. -/
theorem criticalDimensionAllShellEffectiveCountRequirement_le_sampleRate
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    criticalDimensionAllShellEffectiveCountRequirement
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound
      (radius / Real.rpow 2 (-(1 + eta))) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2) ≤
    criticalDimensionSampleRateConstant eta alpha gamma tailBound *
      (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
        theorem310ShiftedRoundLog p round := by
  let cutoff := Probability.pOneFournierGuillinHeadCutoff eta radius
  let confidence := Math.expConfidenceForHalfBudget (theorem310FailureBudget p round)
  let tolerance := theorem310FailureBudget p round / 2
  let roundCoefficient := theorem310RoundLogCoefficient
  let radiusCoefficient := criticalDimensionDepthCoefficient tailBound
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let roundLog := theorem310ShiftedRoundLog p round
  let radiusLog := criticalDimensionShiftedRadiusLog tailBound radius
  let inverseSquare := 1 / radius ^ 2
  let centralLogCoefficient := roundCoefficient + Real.log 2
  let successorLogCoefficient := roundCoefficient + (2 * Real.log 2 + 1)
  let coefficientZero := radiusCoefficient ^ 2 + 1
  let coefficientOne :=
    6 ^ 2 * (2 * (32 * Real.sqrt 2) ^ 2 + 16 * centralLogCoefficient)
  let coefficientTwo :=
    6 * (2 * Real.sqrt 2 * (64 + 8 * centralLogCoefficient))
  let coefficientThree :=
    6 ^ 2 * (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
      tailMultiplier ^ 2
  let coefficientFour :=
    6 ^ 2 * (512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2
  let coefficientFive := roundCoefficient / (2 * (shellCoefficient / decay) ^ 2)
  let coefficientSix := roundCoefficient / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientSeven := roundCoefficient / (shellCoefficient * decay * Real.log 9 / 4)
  let coefficientEight := roundCoefficient / (shellCoefficient * gamma / 4)
  let coefficientNine := 1 / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientTen := 1 / (shellCoefficient * decay * Real.log 9 / 8)
  let coefficientEleven := 1 / ((shellCoefficient * gamma / 4) *
    (Real.rpow 2 (alpha - 1 - eta) - 1))
  let constant := criticalDimensionSampleRateConstant eta alpha gamma tailBound
  have hroundCoefficient : 0 < roundCoefficient := by
    dsimp [roundCoefficient]
    exact theorem310RoundLogCoefficient_pos
  have hradiusCoefficient : 0 < radiusCoefficient := by
    dsimp [radiusCoefficient]
    exact criticalDimensionDepthCoefficient_pos tailBound
  have hdecay : 0 < decay := by
    dsimp [decay]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hshellCoefficient : 0 < shellCoefficient := by
    dsimp [shellCoefficient]
    exact Probability.pOneFournierGuillinShellCoefficient_pos heta
  have htailMultiplier : 0 < tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have hroundLog : 1 ≤ roundLog := by
    dsimp [roundLog]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hradiusLog : 3 ≤ radiusLog := by
    dsimp [radiusLog]
    exact criticalDimensionShiftedRadiusLog_three_le tailBound hradius hsmall
  have hinverseSquare : 1 ≤ inverseSquare := by
    dsimp [inverseSquare]
    simpa using one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (power := 0) (dimension := 2) (by norm_num)
  have hroundLog_nonneg : 0 ≤ roundLog := zero_le_one.trans hroundLog
  have hradiusLog_nonneg : 0 ≤ radiusLog := by linarith
  have hinverseSquare_nonneg : 0 ≤ inverseSquare := zero_le_one.trans hinverseSquare
  have hradiusLogSq_one : 1 ≤ radiusLog ^ 2 := by nlinarith
  have hspatialScale_one : 1 ≤ inverseSquare * radiusLog ^ 2 :=
    one_le_mul_of_one_le_of_one_le hinverseSquare hradiusLogSq_one
  have hscale_one : 1 ≤ inverseSquare * radiusLog ^ 2 * roundLog :=
    one_le_mul_of_one_le_of_one_le
      hspatialScale_one hroundLog
  obtain ⟨hconfidence, hlogEight, hlogSixteen, hlogFour, hlogFourTail⟩ :=
    theorem310_concrete_round_logs_le hp hp_le_one round
  have hconfidence_nonneg : 0 ≤ confidence := by
    dsimp [confidence]
    exact Math.expConfidenceForHalfBudget_nonneg _
  have hroundBound : confidence ≤ roundCoefficient * roundLog := by
    simpa [confidence, roundCoefficient, roundLog] using hconfidence
  have hcutoffBound : ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (2 * Real.log 2 + 1) * radiusLog := by
    dsimp [cutoff, radiusLog]
    exact criticalDimensionHeadCutoff_add_one_mul_log_two_le heta hradius hradius_le_one
  have hcentralArgument : confidence + Real.log 2 ≤ centralLogCoefficient * roundLog := by
    dsimp [centralLogCoefficient]
    have hfixed : Real.log 2 ≤ Real.log 2 * roundLog := by
      nlinarith [hlogTwo.le]
    linarith
  have hround_le_product : roundLog ≤ roundLog * radiusLog := by
    calc
      roundLog = roundLog * 1 := by ring
      _ ≤ roundLog * radiusLog :=
        mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ radiusLog) hroundLog_nonneg
  have hradius_le_product : radiusLog ≤ roundLog * radiusLog := by
    calc
      radiusLog = 1 * radiusLog := by ring
      _ ≤ roundLog * radiusLog :=
        mul_le_mul_of_nonneg_right hroundLog hradiusLog_nonneg
  have hsuccessorArgument :
      confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
        successorLogCoefficient * roundLog * radiusLog := by
    dsimp [successorLogCoefficient]
    calc
      confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
          roundCoefficient * roundLog + (2 * Real.log 2 + 1) * radiusLog :=
        add_le_add hroundBound hcutoffBound
      _ ≤ (roundCoefficient + (2 * Real.log 2 + 1)) *
          (roundLog * radiusLog) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hround_le_product hroundCoefficient.le)
          (mul_le_mul_of_nonneg_left hradius_le_product (by positivity))
          |>.trans_eq (by ring)
      _ = (roundCoefficient + (2 * Real.log 2 + 1)) * roundLog * radiusLog := by ring
  have hcentralArgument_nonneg : 0 ≤ confidence + Real.log 2 := by positivity
  have hsuccessorArgument_nonneg :
      0 ≤ confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hcoefficientZero_nonneg : 0 ≤ coefficientZero := by
    dsimp [coefficientZero]
    positivity
  have hcoefficientOne_nonneg : 0 ≤ coefficientOne := by
    dsimp [coefficientOne, centralLogCoefficient]
    positivity
  have hcoefficientTwo_nonneg : 0 ≤ coefficientTwo := by
    dsimp [coefficientTwo, centralLogCoefficient]
    positivity
  have hcoefficientThree_nonneg : 0 ≤ coefficientThree := by
    dsimp [coefficientThree, successorLogCoefficient]
    positivity
  have hcoefficientFour_nonneg : 0 ≤ coefficientFour := by
    dsimp [coefficientFour, successorLogCoefficient]
    positivity
  have hcoefficientFive_nonneg : 0 ≤ coefficientFive := by
    dsimp [coefficientFive]
    positivity
  have hcoefficientSix_nonneg : 0 ≤ coefficientSix := by
    dsimp [coefficientSix]
    positivity
  have hcoefficientSeven_nonneg : 0 ≤ coefficientSeven := by
    dsimp [coefficientSeven]
    positivity
  have hcoefficientEight_nonneg : 0 ≤ coefficientEight := by
    dsimp [coefficientEight]
    positivity
  have hcoefficientNine_nonneg : 0 ≤ coefficientNine := by
    dsimp [coefficientNine]
    positivity
  have hcoefficientTen_nonneg : 0 ≤ coefficientTen := by
    dsimp [coefficientTen]
    positivity
  have hcoefficientEleven_nonneg : 0 ≤ coefficientEleven := by
    dsimp [coefficientEleven]
    have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
    positivity
  have hconstant_eq : constant = 1 + coefficientZero + coefficientOne + coefficientTwo +
      coefficientThree + coefficientFour + coefficientFive + coefficientSix + coefficientSeven +
      coefficientEight + coefficientNine + coefficientTen + coefficientEleven := by
    rfl
  have hcoefficient_le : ∀ coefficient : ℝ,
      (coefficient = coefficientZero ∨ coefficient = coefficientOne ∨
        coefficient = coefficientTwo ∨ coefficient = coefficientThree ∨
        coefficient = coefficientFour ∨ coefficient = coefficientFive ∨
        coefficient = coefficientSix ∨ coefficient = coefficientSeven ∨
        coefficient = coefficientEight ∨ coefficient = coefficientNine ∨
        coefficient = coefficientTen ∨ coefficient = coefficientEleven) →
      coefficient ≤ constant := by
    intro coefficient hcoefficient
    rw [hconstant_eq]
    rcases hcoefficient with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      linarith
  have hrate : ∀ {coefficient : ℝ}, 0 ≤ coefficient → coefficient ≤ constant →
      coefficient * inverseSquare * radiusLog ^ 2 * roundLog ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    intro coefficient hnonneg hle
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hle hinverseSquare_nonneg)
        (sq_nonneg radiusLog)) hroundLog_nonneg
  have hroundRate : ∀ {coefficient : ℝ}, 0 ≤ coefficient → coefficient ≤ constant →
      coefficient * inverseSquare * roundLog ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    intro coefficient hnonneg hle
    calc
      coefficient * inverseSquare * roundLog =
          coefficient * inverseSquare * 1 * roundLog := by ring
      _ ≤ coefficient * inverseSquare * radiusLog ^ 2 * roundLog := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hradiusLogSq_one
            (mul_nonneg hnonneg hinverseSquare_nonneg)) hroundLog_nonneg
      _ ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog := hrate hnonneg hle
  have hplainRate : ∀ {coefficient : ℝ}, 0 ≤ coefficient → coefficient ≤ constant →
      coefficient * inverseSquare ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    intro coefficient hnonneg hle
    calc
      coefficient * inverseSquare = coefficient * inverseSquare * 1 := by ring
      _ ≤ coefficient * inverseSquare * roundLog :=
        mul_le_mul_of_nonneg_left hroundLog
          (mul_nonneg hnonneg hinverseSquare_nonneg)
      _ ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog :=
        hroundRate hnonneg hle
  have hcriticalCount :
      (criticalDimensionLogSquaredCount tailBound radius : ℝ) ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    have hbounds := criticalDimensionLogSquaredCount_bounds tailBound hradius hsmall
    have hlogRatio_nonneg : 0 ≤ Real.log (radiusCoefficient / radius) := by
      have hratio : Real.exp 2 ≤ radiusCoefficient / radius := by
        dsimp [radiusCoefficient]
        exact (le_div_iff₀ hradius).mpr (by simpa [mul_comm] using hsmall)
      exact Real.log_nonneg (le_trans
        (by simpa using (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 2))) hratio)
    have hlogRatio_le : Real.log (radiusCoefficient / radius) ≤ radiusLog := by
      dsimp [radiusLog, criticalDimensionShiftedRadiusLog, radiusCoefficient]
      linarith
    have hthreshold : criticalDimensionLogSquaredThreshold tailBound radius ≤
        radiusCoefficient ^ 2 * inverseSquare * radiusLog ^ 2 := by
      unfold criticalDimensionLogSquaredThreshold
      dsimp [radiusCoefficient, inverseSquare]
      have hsquare := pow_le_pow_left₀ hlogRatio_nonneg hlogRatio_le 2
      calc
        ((criticalDimensionDepthCoefficient tailBound / radius) *
            Real.log (criticalDimensionDepthCoefficient tailBound / radius)) ^ 2 =
            criticalDimensionDepthCoefficient tailBound ^ 2 * (1 / radius ^ 2) *
              Real.log (criticalDimensionDepthCoefficient tailBound / radius) ^ 2 := by
          field_simp [hradius.ne']
          <;> ring
        _ ≤ criticalDimensionDepthCoefficient tailBound ^ 2 * (1 / radius ^ 2) *
              radiusLog ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare (by positivity)
    calc
      (criticalDimensionLogSquaredCount tailBound radius : ℝ) ≤
          criticalDimensionLogSquaredThreshold tailBound radius + 1 := hbounds.2.le
      _ ≤ coefficientZero * inverseSquare * radiusLog ^ 2 * roundLog := by
        dsimp [coefficientZero]
        calc
          criticalDimensionLogSquaredThreshold tailBound radius + 1 ≤
              radiusCoefficient ^ 2 * inverseSquare * radiusLog ^ 2 +
                inverseSquare * radiusLog ^ 2 :=
            add_le_add hthreshold hspatialScale_one
          _ ≤ (radiusCoefficient ^ 2 + 1) * inverseSquare * radiusLog ^ 2 *
                roundLog := by
            calc
              radiusCoefficient ^ 2 * inverseSquare * radiusLog ^ 2 +
                  inverseSquare * radiusLog ^ 2 =
                  (radiusCoefficient ^ 2 * inverseSquare * radiusLog ^ 2 +
                    inverseSquare * radiusLog ^ 2) * 1 := by ring
              _ ≤ (radiusCoefficient ^ 2 * inverseSquare * radiusLog ^ 2 +
                    inverseSquare * radiusLog ^ 2) * roundLog :=
                mul_le_mul_of_nonneg_left hroundLog (by positivity)
              _ = (radiusCoefficient ^ 2 + 1) * inverseSquare * radiusLog ^ 2 *
                    roundLog := by ring
      _ ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog :=
        hrate hcoefficientZero_nonneg (hcoefficient_le _ (Or.inl rfl))
  have hcentralRootSquare :
      Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 ≤
        (2 * (32 * Real.sqrt 2) ^ 2 + 16 * centralLogCoefficient) * roundLog := by
    unfold Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient
    have hsquare := sq_nonneg
      (32 * Real.sqrt 2 - 2 * Real.sqrt 2 * Real.sqrt (confidence + Real.log 2))
    have hsqrt := Real.sq_sqrt hcentralArgument_nonneg
    have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [hsqrt, htwo]
  have hcentralCount :
      Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence ≤
        (2 * Real.sqrt 2 * (64 + 8 * centralLogCoefficient)) * roundLog := by
    unfold Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient
    have hfirst : 64 + 8 * (confidence + Real.log 2) ≤
        (64 + 8 * centralLogCoefficient) * roundLog := by
      calc
        64 + 8 * (confidence + Real.log 2) ≤
            64 + 8 * (centralLogCoefficient * roundLog) := by linarith
        _ ≤ (64 + 8 * centralLogCoefficient) * roundLog := by
          nlinarith [hroundLog]
    calc
      2 * Real.sqrt 2 *
          (16 * ((2 ^ 2 : ℕ) : ℝ) + 8 * (confidence + Real.log 2)) =
          2 * Real.sqrt 2 * (64 + 8 * (confidence + Real.log 2)) := by norm_num
      _ ≤ 2 * Real.sqrt 2 * ((64 + 8 * centralLogCoefficient) * roundLog) :=
        mul_le_mul_of_nonneg_left hfirst
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
      _ = (2 * Real.sqrt 2 * (64 + 8 * centralLogCoefficient)) * roundLog := by
        ring
  have hsuccessorRootSquare :
      Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff confidence
          tailBound ^ 2 ≤
        (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
          tailMultiplier ^ 2 * roundLog * radiusLog := by
    have hbaseSquare :
        (32 * Real.sqrt 2 + 2 * Real.sqrt 2 *
          Real.sqrt (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ^ 2 ≤
          (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
            roundLog * radiusLog := by
      have hsquare := sq_nonneg
        (32 * Real.sqrt 2 - 2 * Real.sqrt 2 *
          Real.sqrt (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2))
      have hsqrt := Real.sq_sqrt hsuccessorArgument_nonneg
      have htwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith [hsqrt, htwo]
    have hmul :
        ((32 * Real.sqrt 2 + 2 * Real.sqrt 2 *
          Real.sqrt (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
            tailMultiplier) ^ 2 ≤
          (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
            tailMultiplier ^ 2 * roundLog * radiusLog := by
      rw [mul_pow]
      calc
        (32 * Real.sqrt 2 + 2 * Real.sqrt 2 *
            Real.sqrt (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ^ 2 *
            tailMultiplier ^ 2 ≤
            ((2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
              roundLog * radiusLog) * tailMultiplier ^ 2 :=
          mul_le_mul_of_nonneg_right hbaseSquare (sq_nonneg tailMultiplier)
        _ = (2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
            tailMultiplier ^ 2 * roundLog * radiusLog := by ring
    unfold Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient
    simpa only [tailMultiplier, Nat.cast_add, Nat.cast_one] using hmul
  have hsuccessorSqrtSquare :
      Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff confidence
          tailBound ^ 2 ≤
        (512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2 *
          roundLog * radiusLog := by
    have hinside : 0 ≤ 16 * ((2 ^ 2 : ℕ) : ℝ) +
        8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) := by positivity
    have hinsideBound : 16 * ((2 ^ 2 : ℕ) : ℝ) +
        8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) ≤
        (64 + 8 * successorLogCoefficient) * roundLog * radiusLog := by
      have hroundRadius_one : 1 ≤ roundLog * radiusLog :=
        one_le_mul_of_one_le_of_one_le hroundLog (by linarith)
      have hsuccessorArgument' :
          confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
            successorLogCoefficient * roundLog * radiusLog := by
        simpa only [Nat.cast_add, Nat.cast_one] using hsuccessorArgument
      have hconstant : 64 ≤ 64 * (roundLog * radiusLog) := by
        calc
          (64 : ℝ) = 64 * 1 := by ring
          _ ≤ 64 * (roundLog * radiusLog) :=
            mul_le_mul_of_nonneg_left hroundRadius_one (by norm_num)
      have hargumentEight :
          8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) ≤
            8 * (successorLogCoefficient * roundLog * radiusLog) :=
        mul_le_mul_of_nonneg_left hsuccessorArgument' (by norm_num)
      calc
        16 * ((2 ^ 2 : ℕ) : ℝ) +
            8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) =
            64 + 8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) := by
          norm_num
        _ ≤ 64 + 8 * (successorLogCoefficient * roundLog * radiusLog) :=
          by simpa only [add_comm] using (add_le_add_left hargumentEight 64)
        _ ≤ (64 + 8 * successorLogCoefficient) * roundLog * radiusLog := by
          calc
            64 + 8 * (successorLogCoefficient * roundLog * radiusLog) ≤
                64 * (roundLog * radiusLog) +
                  8 * (successorLogCoefficient * roundLog * radiusLog) :=
              by
                simpa only [add_comm] using
                  (add_le_add_right hconstant
                    (8 * (successorLogCoefficient * roundLog * radiusLog)))
            _ = (64 + 8 * successorLogCoefficient) * roundLog * radiusLog := by ring
    have hsqrtInside := Real.sq_sqrt hinside
    have hsqrtTwo := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hcore :
        (2 * Real.sqrt 2) ^ 2 *
          (16 * ((2 ^ 2 : ℕ) : ℝ) +
            8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ≤
          (512 + 64 * successorLogCoefficient) * roundLog * radiusLog := by
      have hfactor : (2 * Real.sqrt 2) ^ 2 = 8 := by
        calc
          (2 * Real.sqrt 2) ^ 2 = 4 * (Real.sqrt 2) ^ 2 := by ring
          _ = 8 := by rw [hsqrtTwo]; norm_num
      calc
        (2 * Real.sqrt 2) ^ 2 *
            (16 * ((2 ^ 2 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) =
            8 * (16 * ((2 ^ 2 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) := by
          rw [hfactor]
        _ ≤ 8 * ((64 + 8 * successorLogCoefficient) * roundLog * radiusLog) :=
          mul_le_mul_of_nonneg_left hinsideBound (by norm_num)
        _ = (512 + 64 * successorLogCoefficient) * roundLog * radiusLog := by ring
    have hmul :
        (2 * Real.sqrt 2 * Real.sqrt
            (16 * ((2 ^ 2 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
            tailMultiplier) ^ 2 ≤
          (512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2 *
            roundLog * radiusLog := by
      calc
        (2 * Real.sqrt 2 * Real.sqrt
            (16 * ((2 ^ 2 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
            tailMultiplier) ^ 2 =
            ((2 * Real.sqrt 2) ^ 2 *
              (16 * ((2 ^ 2 : ℕ) : ℝ) +
                8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2))) *
              tailMultiplier ^ 2 := by
          simp only [mul_pow]
          rw [hsqrtInside]
        _ ≤ ((512 + 64 * successorLogCoefficient) * roundLog * radiusLog) *
            tailMultiplier ^ 2 :=
          mul_le_mul_of_nonneg_right hcore (sq_nonneg tailMultiplier)
        _ = (512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2 *
            roundLog * radiusLog := by ring
    unfold Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient
    simpa only [tailMultiplier, Nat.cast_add, Nat.cast_one] using hmul
  have hheadOne :
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 /
          radius ^ 2 ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 /
          radius ^ 2 ≤ coefficientOne * inverseSquare * roundLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient confidence ^ 2 /
              radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionTwoCentralRootCoefficient
                confidence ^ 2 * inverseSquare := by dsimp [inverseSquare]; ring
          _ ≤ 6 ^ 2 *
              ((2 * (32 * Real.sqrt 2) ^ 2 + 16 * centralLogCoefficient) * roundLog) *
                inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcentralRootSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientOne * inverseSquare * roundLog := by
            dsimp [coefficientOne]
            ring
      _ ≤ _ := hroundRate hcoefficientOne_nonneg
        (hcoefficient_le _ (Or.inr (Or.inl rfl)))
  have hheadTwo :
      6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence /
          radius ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    have hinverseRadius : 1 / radius ≤ inverseSquare := by
      dsimp [inverseSquare]
      have hsquare_le : radius ^ 2 ≤ radius := by
        calc
          radius ^ 2 = radius * radius := by ring
          _ ≤ radius * 1 := mul_le_mul_of_nonneg_left hradius_le_one hradius.le
          _ = radius := by ring
      exact one_div_le_one_div_of_le (sq_pos_of_pos hradius) hsquare_le
    calc
      6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence /
          radius ≤ coefficientTwo * (1 / radius) * roundLog := by
        calc
          6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient confidence /
              radius = 6 * Probability.selectedShellGeometricDimensionTwoCentralCountCoefficient
                confidence * (1 / radius) := by ring
          _ ≤ 6 * ((2 * Real.sqrt 2 * (64 + 8 * centralLogCoefficient)) * roundLog) *
                (1 / radius) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcentralCount (by norm_num)) (by positivity)
          _ = coefficientTwo * (1 / radius) * roundLog := by
            dsimp [coefficientTwo]
            ring
      _ ≤ coefficientTwo * inverseSquare * roundLog := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinverseRadius hcoefficientTwo_nonneg) hroundLog_nonneg
      _ ≤ _ := hroundRate hcoefficientTwo_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inl rfl))))
  have hradiusLog_le_sq : radiusLog ≤ radiusLog ^ 2 := by
    have hone_le_radiusLog : 1 ≤ radiusLog := by linarith [hradiusLog]
    calc
      radiusLog = radiusLog * 1 := by ring
      _ ≤ radiusLog * radiusLog :=
        mul_le_mul_of_nonneg_left hone_le_radiusLog (by linarith [hradiusLog])
      _ = radiusLog ^ 2 := by ring
  have hheadThree :
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
          coefficientThree * inverseSquare * roundLog * radiusLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient cutoff
              confidence tailBound ^ 2 / radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorRootCoefficient
                cutoff confidence tailBound ^ 2 * inverseSquare := by
            dsimp [inverseSquare]
            ring
          _ ≤ 6 ^ 2 *
              ((2 * (32 * Real.sqrt 2) ^ 2 + 16 * successorLogCoefficient) *
                tailMultiplier ^ 2 * roundLog * radiusLog) * inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsuccessorRootSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientThree * inverseSquare * roundLog * radiusLog := by
            dsimp [coefficientThree]
            ring
      _ ≤ coefficientThree * inverseSquare * roundLog * radiusLog ^ 2 :=
        mul_le_mul_of_nonneg_left hradiusLog_le_sq (by positivity)
      _ = coefficientThree * inverseSquare * radiusLog ^ 2 * roundLog := by ring
      _ ≤ _ := hrate hcoefficientThree_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hheadFour :
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
          coefficientFour * inverseSquare * roundLog * radiusLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient cutoff
              confidence tailBound ^ 2 / radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionTwoSuccessorSqrtCoefficient
                cutoff confidence tailBound ^ 2 * inverseSquare := by
            dsimp [inverseSquare]
            ring
          _ ≤ 6 ^ 2 * ((512 + 64 * successorLogCoefficient) * tailMultiplier ^ 2 *
                roundLog * radiusLog) * inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsuccessorSqrtSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientFour * inverseSquare * roundLog * radiusLog := by
            dsimp [coefficientFour]
            ring
      _ ≤ coefficientFour * inverseSquare * roundLog * radiusLog ^ 2 :=
        mul_le_mul_of_nonneg_left hradiusLog_le_sq (by positivity)
      _ = coefficientFour * inverseSquare * radiusLog ^ 2 * roundLog := by ring
      _ ≤ _ := hrate hcoefficientFour_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hheadRequirement :
      criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailBound radius ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    unfold criticalDimensionSharpHeadEffectiveCountRequirement
    exact max_le hcriticalCount
      (max_le hheadOne (max_le hheadTwo (max_le hheadThree hheadFour)))
  have hlogEightScale : Real.log (8 / tolerance) / radius ^ 2 ≤
      roundCoefficient * inverseSquare * roundLog := by
    dsimp [inverseSquare, roundCoefficient, roundLog, tolerance]
    calc
      Real.log (8 / (theorem310FailureBudget p round / 2)) / radius ^ 2 ≤
          theorem310RoundLogCoefficient * theorem310ShiftedRoundLog p round /
            radius ^ 2 :=
        div_le_div_of_nonneg_right hlogEight (sq_nonneg radius)
      _ = theorem310RoundLogCoefficient * (1 / radius ^ 2) *
          theorem310ShiftedRoundLog p round := by ring
  have hlogSixteenScale : Real.log (16 / tolerance) / radius ^ 2 ≤
      roundCoefficient * inverseSquare * roundLog := by
    dsimp [inverseSquare, roundCoefficient, roundLog, tolerance]
    calc
      Real.log (16 / (theorem310FailureBudget p round / 2)) / radius ^ 2 ≤
          theorem310RoundLogCoefficient * theorem310ShiftedRoundLog p round /
            radius ^ 2 :=
        div_le_div_of_nonneg_right hlogSixteen (sq_nonneg radius)
      _ = theorem310RoundLogCoefficient * (1 / radius ^ 2) *
          theorem310ShiftedRoundLog p round := by ring
  have hlogFourScale : Real.log (4 / tolerance) / radius ^ 2 ≤
      roundCoefficient * inverseSquare * roundLog := by
    dsimp [inverseSquare, roundCoefficient, roundLog, tolerance]
    calc
      Real.log (4 / (theorem310FailureBudget p round / 2)) / radius ^ 2 ≤
          theorem310RoundLogCoefficient * theorem310ShiftedRoundLog p round /
            radius ^ 2 :=
        div_le_div_of_nonneg_right hlogFour (sq_nonneg radius)
      _ = theorem310RoundLogCoefficient * (1 / radius ^ 2) *
          theorem310ShiftedRoundLog p round := by ring
  have hlogFourTailScale :
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2 ≤
        roundCoefficient * inverseSquare * roundLog := by
    dsimp [inverseSquare, roundCoefficient, roundLog, tolerance]
    calc
      Real.log (4 / ((theorem310FailureBudget p round / 2) *
          (1 - Real.exp (-1)))) / radius ^ 2 ≤
          theorem310RoundLogCoefficient * theorem310ShiftedRoundLog p round /
            radius ^ 2 :=
        div_le_div_of_nonneg_right hlogFourTail (sq_nonneg radius)
      _ = theorem310RoundLogCoefficient * (1 / radius ^ 2) *
          theorem310ShiftedRoundLog p round := by ring
  have hmassOne : Real.log (8 / tolerance) /
      (2 * (shellCoefficient * (radius / decay)) ^ 2) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      Real.log (8 / tolerance) / (2 * (shellCoefficient * (radius / decay)) ^ 2) =
          (1 / (2 * (shellCoefficient / decay) ^ 2)) *
            (Real.log (8 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hdecay.ne', hshellCoefficient.ne']
        <;> ring
      _ ≤ coefficientFive * inverseSquare * roundLog := by
        calc
          (1 / (2 * (shellCoefficient / decay) ^ 2)) *
              (Real.log (8 / tolerance) / radius ^ 2) ≤
              (1 / (2 * (shellCoefficient / decay) ^ 2)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogEightScale
              (show 0 ≤ 1 / (2 * (shellCoefficient / decay) ^ 2) by positivity)
          _ = coefficientFive * inverseSquare * roundLog := by
            dsimp [coefficientFive]
            ring
      _ ≤ _ := hroundRate hcoefficientFive_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hmassTwo : Real.log (16 / tolerance) /
      (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      Real.log (16 / tolerance) /
          (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
          (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
            (Real.log (16 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
        <;> ring
      _ ≤ coefficientSix * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
              (Real.log (16 / tolerance) / radius ^ 2) ≤
              (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogSixteenScale
              (show 0 ≤ 1 / (shellCoefficient ^ 2 / (18 * tailBound)) by positivity)
          _ = coefficientSix * inverseSquare * roundLog := by
            dsimp [coefficientSix]
            ring
      _ ≤ _ := hroundRate hcoefficientSix_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl rfl))))))))
  have hmassThree : Real.log (4 / tolerance) /
      (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      Real.log (4 / tolerance) /
          (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) =
          (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
            (Real.log (4 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
        <;> ring
      _ ≤ coefficientSeven * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
              (Real.log (4 / tolerance) / radius ^ 2) ≤
              (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogFourScale
              (show 0 ≤ 1 / (shellCoefficient * decay * Real.log 9 / 4) by positivity)
          _ = coefficientSeven * inverseSquare * roundLog := by
            dsimp [coefficientSeven]
            ring
      _ ≤ _ := hroundRate hcoefficientSeven_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl rfl)))))))))
  have hmassFour : Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
      (shellCoefficient * radius ^ 2 * gamma / 4) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
          (shellCoefficient * radius ^ 2 * gamma / 4) =
          (1 / (shellCoefficient * gamma / 4)) *
            (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne']
        <;> ring
      _ ≤ coefficientEight * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient * gamma / 4)) *
              (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2) ≤
              (1 / (shellCoefficient * gamma / 4)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogFourTailScale
              (show 0 ≤ 1 / (shellCoefficient * gamma / 4) by positivity)
          _ = coefficientEight * inverseSquare * roundLog := by
            dsimp [coefficientEight]
            ring
      _ ≤ _ := hroundRate hcoefficientEight_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
  have hmassRequirement :
      Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta
        (radius / decay) radius gamma tailBound tolerance ≤
        constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    unfold Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement
      Probability.pOneFournierGuillinShellWeight
    simp only [Nat.cast_zero, mul_zero, neg_zero]
    have hrpowZero : Real.rpow (2 : ℝ) 0 = 1 := by
      rw [Real.rpow_eq_pow, Real.rpow_zero]
    rw [hrpowZero, mul_one]
    exact max_le hmassOne (max_le hmassTwo (max_le hmassThree hmassFour))
  have hsquareOne : 1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
          coefficientNine * inverseSquare := by
        dsimp [coefficientNine, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientNine_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))))
  have hsquareTwo : 1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    calc
      1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) =
          coefficientTen * inverseSquare := by
        dsimp [coefficientTen, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientTen_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))))
  have hsquareThree : 1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
      (Real.rpow 2 (alpha - 1 - eta) - 1)) ≤
      constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
    calc
      1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
          (Real.rpow 2 (alpha - 1 - eta) - 1)) =
          coefficientEleven * inverseSquare := by
        dsimp [coefficientEleven, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne', hbaseSub.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientEleven_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))))))
  have hsquareRequirement :
      Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement eta alpha gamma
        tailBound radius ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog := by
    unfold Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
    exact max_le hsquareOne (max_le hsquareTwo hsquareThree)
  change max
    (criticalDimensionSharpHeadEffectiveCountRequirement cutoff confidence tailBound radius)
    (max
      (Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta
        (radius / decay) radius gamma tailBound tolerance)
      (Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement eta alpha gamma
        tailBound radius)) ≤ constant * inverseSquare * radiusLog ^ 2 * roundLog
  exact max_le hheadRequirement (max_le hmassRequirement hsquareRequirement)

/-- The actual positive natural count of the sharp critical schedule has the
same rate up to the unavoidable ceiling factor two. -/
theorem criticalDimensionRateCountSchedule_le
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round : ℝ) ≤
      2 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          theorem310ShiftedRoundLog p round := by
  let requirement :=
    criticalDimensionAllShellEffectiveCountRequirement
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound
      (radius / Real.rpow 2 (-(1 + eta))) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2)
  let envelope :=
    criticalDimensionSampleRateConstant eta alpha gamma tailBound *
      (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
        theorem310ShiftedRoundLog p round
  have hrequirement : requirement ≤ envelope := by
    dsimp [requirement, envelope]
    exact criticalDimensionAllShellEffectiveCountRequirement_le_sampleRate
      heta halphaGap hgamma htailBound hradius hradius_le_one hsmall hp hp_le_one round
  have hinverse_one : 1 ≤ 1 / radius ^ 2 := by
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le 2))
  have hradiusLog_three :=
    criticalDimensionShiftedRadiusLog_three_le tailBound hradius hsmall
  have hradiusLogSq_one :
      1 ≤ criticalDimensionShiftedRadiusLog tailBound radius ^ 2 := by
    nlinarith
  have hshifted_one := theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hconstant_one := one_le_criticalDimensionSampleRateConstant
    heta halphaGap hgamma htailBound
  have henvelope_one : 1 ≤ envelope := by
    dsimp [envelope]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hconstant_one hinverse_one)
        hradiusLogSq_one) hshifted_one
  have hmax : max 1 requirement ≤ envelope := max_le henvelope_one hrequirement
  have hceil : (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := by
    unfold Math.positiveNatCeil
    exact Nat.ceil_lt_add_one (zero_le_one.trans (le_max_left _ _))
  have hcount_lt : (Math.positiveNatCeil requirement : ℝ) < 2 * envelope := by
    calc
      (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := hceil
      _ ≤ envelope + 1 := add_le_add hmax le_rfl
      _ ≤ 2 * envelope := by linarith
  unfold criticalDimensionRateCountSchedule criticalDimensionAllShellEffectiveCount
  simpa only [requirement, envelope, mul_assoc] using hcount_lt.le

/-- Literal round-log form on the honest endpoint range where the source log
is at least one. -/
theorem criticalDimensionRateCountSchedule_le_literal_log
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hsmall : Real.exp 2 * radius ≤ criticalDimensionDepthCoefficient tailBound)
    (hp : 0 < p) (hp_le_exp_neg_one : p ≤ Real.exp (-1)) (round : ℕ) :
    (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round : ℝ) ≤
      4 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by
  have hp_le_one : p ≤ 1 :=
    hp_le_exp_neg_one.trans (Real.exp_lt_one_iff.mpr (by norm_num)).le
  have hbase := criticalDimensionRateCountSchedule_le heta halphaGap hgamma htailBound
    hradius hradius_le_one hsmall hp hp_le_one round
  have htime : (1 : ℝ) ≤ ((round + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega : round + 1 ≠ 0)
  have hratio_exp : Real.exp 1 ≤ ((round + 1 : ℕ) : ℝ) / p := by
    apply (le_div_iff₀ hp).mpr
    have hpexp : p * Real.exp 1 ≤ 1 := by
      calc
        p * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 :=
          mul_le_mul_of_nonneg_right hp_le_exp_neg_one (Real.exp_pos 1).le
        _ = 1 := by rw [← Real.exp_add]; norm_num
    simpa [mul_comm] using hpexp.trans htime
  have hlog_one : 1 ≤ Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hratio_exp
    simpa using hlog
  have hshifted : theorem310ShiftedRoundLog p round ≤
      2 * Real.log (((round + 1 : ℕ) : ℝ) / p) := by
    unfold theorem310ShiftedRoundLog
    linarith
  calc
    (criticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round : ℝ) ≤
      2 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          theorem310ShiftedRoundLog p round := hbase
    _ ≤ 2 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          (2 * Real.log (((round + 1 : ℕ) : ℝ) / p)) := by
      exact mul_le_mul_of_nonneg_left hshifted
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by positivity)
              (criticalDimensionSampleRateConstant_pos
                heta halphaGap hgamma htailBound).le)
            (by positivity)) (sq_nonneg _))
    _ = 4 * criticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * criticalDimensionShiftedRadiusLog tailBound radius ^ 2 *
          Real.log (((round + 1 : ℕ) : ℝ) / p) := by ring

end PZMH20PerformativePrediction
