import PZMH20PerformativePrediction.SampleCountRates

/-!
# Dimension-one actual sample-count rate

The all-dimensional concrete selector already uses the exact dimension-one
compact-head requirement when the ambient dimension is one.  This file bounds
that existing positive natural count.  The inverse-square dependence is the
correct one-dimensional power for the checked selector; its shellwise
confidence allocation contributes one honest logarithm in the inverse radius.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib

/-- The radius logarithm appearing in the exact dimension-one shell selector. -/
noncomputable def subcriticalDimensionShiftedRadiusLog (radius : ℝ) : ℝ :=
  1 - Real.log radius

theorem one_le_subcriticalDimensionShiftedRadiusLog
    {radius : ℝ} (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    1 ≤ subcriticalDimensionShiftedRadiusLog radius := by
  unfold subcriticalDimensionShiftedRadiusLog
  have hlog : Real.log radius ≤ 0 := Real.log_nonpos hradius.le hradius_le_one
  linarith

/-- The source cutoff contributes at most one inverse-radius logarithm. -/
theorem subcriticalDimensionHeadCutoff_add_one_mul_log_two_le
    {eta radius : ℝ} (heta : 0 < eta)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
        Real.log 2 ≤
      (2 * Real.log 2 + 1) * subcriticalDimensionShiftedRadiusLog radius := by
  let delta : ℝ := 1 / (2 * (1 + eta))
  let threshold : ℝ := Real.rpow radius (-delta)
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
      1 = Real.rpow radius 0 := by rw [Real.rpow_eq_pow, Real.rpow_zero]
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
  have hdeltaLog_le : delta * (-Real.log radius) ≤ -Real.log radius := by
    calc
      delta * (-Real.log radius) ≤ 1 * (-Real.log radius) :=
        mul_le_mul_of_nonneg_right hdelta_le_one hnegLog_nonneg
      _ = -Real.log radius := by ring
  unfold subcriticalDimensionShiftedRadiusLog
  calc
    ((Probability.pOneFournierGuillinHeadCutoff eta radius + 1 : ℕ) : ℝ) *
        Real.log 2 ≤ delta * (-Real.log radius) + 2 * Real.log 2 := hcutoff_log.le
    _ ≤ -Real.log radius + 2 * Real.log 2 := by linarith
    _ ≤ (2 * Real.log 2 + 1) * (1 - Real.log radius) := by
      nlinarith [hnegLog_nonneg, hlogTwo_pos.le]

/-- The exponential cutoff term in the dimension-one head is at most a
constant times the inverse radius. -/
theorem two_pow_subcriticalDimensionHeadCutoff_le_two_div_radius
    {eta radius : ℝ} (heta : 0 < eta)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1) :
    (2 : ℝ) ^ Probability.pOneFournierGuillinHeadCutoff eta radius ≤
      2 / radius := by
  let delta : ℝ := 1 / (2 * (1 + eta))
  let threshold : ℝ := Real.rpow radius (-delta)
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
      1 = Real.rpow radius 0 := by rw [Real.rpow_eq_pow, Real.rpow_zero]
      _ ≤ Real.rpow radius (-delta) :=
        Real.rpow_le_rpow_of_exponent_ge hradius hradius_le_one (by linarith)
  have hcutoff_eq : Probability.pOneFournierGuillinHeadCutoff eta radius =
      Nat.ceil (Real.logb 2 threshold) := by
    simp only [Probability.pOneFournierGuillinHeadCutoff]
    dsimp [threshold, delta]
  have hceil := AppliedModelingLib.Math.pow_natCeil_logb_lt_mul
    (base := (2 : ℝ)) (threshold := threshold) (by norm_num) hthreshold_one
  have hthreshold_le : threshold ≤ 1 / radius := by
    dsimp [threshold]
    calc
      Real.rpow radius (-delta) ≤ Real.rpow radius (-1) :=
        Real.rpow_le_rpow_of_exponent_ge hradius hradius_le_one (by linarith)
      _ = 1 / radius := by
        simpa only [one_div] using Real.rpow_neg_one radius
  calc
    (2 : ℝ) ^ Probability.pOneFournierGuillinHeadCutoff eta radius =
        (2 : ℝ) ^ Nat.ceil (Real.logb 2 threshold) := by rw [hcutoff_eq]
    _ ≤ 2 * threshold := hceil.le
    _ ≤ 2 * (1 / radius) := mul_le_mul_of_nonneg_left hthreshold_le (by norm_num)
    _ = 2 / radius := by ring

/-- Parameter-only coefficient for the six exact dimension-one compact-head
gates. -/
noncomputable def subcriticalDimensionHeadRateConstant (tailBound : ℝ) : ℝ :=
  let roundCoefficient := theorem310RoundLogCoefficient
  let baseCoefficient := 2 * (1 / (1 - 1 / Real.sqrt 2))
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := roundCoefficient + Real.log 2
  let successorLogCoefficient := roundCoefficient + (2 * Real.log 2 + 1)
  max 1 <| max (6 * 128) <| max
    (6 ^ 2 * (2 * baseCoefficient ^ 2 + 8 * centralLogCoefficient)) <| max
    (6 * (2 * (32 + 8 * centralLogCoefficient))) <| max
    (6 * (128 * 8)) <| max
    (6 ^ 2 * (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
      tailMultiplier ^ 2)
    (6 ^ 2 * (4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2)

theorem one_le_subcriticalDimensionHeadRateConstant (tailBound : ℝ) :
    1 ≤ subcriticalDimensionHeadRateConstant tailBound := by
  unfold subcriticalDimensionHeadRateConstant
  dsimp only
  exact le_max_left _ _

/-- The exact six-gate dimension-one head requirement has inverse-square
radius dependence and one shell-cutoff logarithm. -/
theorem selectedShellGeometricDimensionOneEffectiveCountRequirement_le_subcriticalRate
    {eta tailBound radius p : ℝ} (heta : 0 < eta)
    (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    Probability.selectedShellGeometricDimensionOneEffectiveCountRequirement
      (Probability.pOneFournierGuillinHeadCutoff eta radius)
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      tailBound radius ≤
    subcriticalDimensionHeadRateConstant tailBound * (1 / radius ^ 2) *
      subcriticalDimensionShiftedRadiusLog radius * theorem310ShiftedRoundLog p round := by
  let cutoff := Probability.pOneFournierGuillinHeadCutoff eta radius
  let confidence := Math.expConfidenceForHalfBudget (theorem310FailureBudget p round)
  let roundLog := theorem310ShiftedRoundLog p round
  let radiusLog := subcriticalDimensionShiftedRadiusLog radius
  let inverseSquare := 1 / radius ^ 2
  let roundCoefficient := theorem310RoundLogCoefficient
  let baseCoefficient := 2 * (1 / (1 - 1 / Real.sqrt 2))
  let tailMultiplier := Probability.selectedShellGeometricTailMultiplier tailBound
  let centralLogCoefficient := roundCoefficient + Real.log 2
  let successorLogCoefficient := roundCoefficient + (2 * Real.log 2 + 1)
  let coefficientZero : ℝ := 6 * 128
  let coefficientOne :=
    6 ^ 2 * (2 * baseCoefficient ^ 2 + 8 * centralLogCoefficient)
  let coefficientTwo := 6 * (2 * (32 + 8 * centralLogCoefficient))
  let coefficientThree : ℝ := 6 * (128 * 8)
  let coefficientFour :=
    6 ^ 2 * (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
      tailMultiplier ^ 2
  let coefficientFive :=
    6 ^ 2 * (4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2
  let constant := subcriticalDimensionHeadRateConstant tailBound
  have hroundCoefficient : 0 < roundCoefficient := theorem310RoundLogCoefficient_pos
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htailMultiplier : 0 < tailMultiplier := by
    dsimp [tailMultiplier, Probability.selectedShellGeometricTailMultiplier]
    positivity
  have hbaseCoefficient : 0 < baseCoefficient := by
    dsimp [baseCoefficient]
    have hsqrtTwo : 1 < Real.sqrt 2 := Real.one_lt_sqrt_two
    have hinvSqrtTwo : 1 / Real.sqrt 2 < 1 := by
      rw [div_lt_one (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
      exact hsqrtTwo
    exact mul_pos (by norm_num) (one_div_pos.mpr (sub_pos.mpr hinvSqrtTwo))
  have hroundLog : 1 ≤ roundLog := by
    dsimp [roundLog]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hradiusLog : 1 ≤ radiusLog := by
    dsimp [radiusLog]
    exact one_le_subcriticalDimensionShiftedRadiusLog hradius hradius_le_one
  have hinverseSquare : 1 ≤ inverseSquare := by
    dsimp [inverseSquare]
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le 2))
  have hroundLog_nonneg : 0 ≤ roundLog := zero_le_one.trans hroundLog
  have hradiusLog_nonneg : 0 ≤ radiusLog := zero_le_one.trans hradiusLog
  have hinverseSquare_nonneg : 0 ≤ inverseSquare := zero_le_one.trans hinverseSquare
  obtain ⟨hconfidence, -, -, -, -⟩ := theorem310_concrete_round_logs_le hp hp_le_one round
  have hconfidence_nonneg : 0 ≤ confidence := by
    dsimp [confidence]
    unfold Math.expConfidenceForHalfBudget
    exact le_max_left _ _
  have hcentralArgument : confidence + Real.log 2 ≤
      centralLogCoefficient * roundLog := by
    dsimp [centralLogCoefficient]
    calc
      confidence + Real.log 2 ≤ roundCoefficient * roundLog + Real.log 2 := by
        dsimp [confidence, roundCoefficient, roundLog] at hconfidence ⊢
        linarith
      _ ≤ (roundCoefficient + Real.log 2) * roundLog := by
        nlinarith [hroundLog]
  have hcutoffLog : ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
      (2 * Real.log 2 + 1) * radiusLog := by
    dsimp [cutoff, radiusLog]
    exact subcriticalDimensionHeadCutoff_add_one_mul_log_two_le
      heta hradius hradius_le_one
  have hround_le_product : roundLog ≤ roundLog * radiusLog := by
    calc
      roundLog = roundLog * 1 := by ring
      _ ≤ roundLog * radiusLog :=
        mul_le_mul_of_nonneg_left hradiusLog hroundLog_nonneg
  have hradius_le_product : radiusLog ≤ roundLog * radiusLog := by
    calc
      radiusLog = 1 * radiusLog := by ring
      _ ≤ roundLog * radiusLog :=
        mul_le_mul_of_nonneg_right hroundLog hradiusLog_nonneg
  have hsuccessorArgument : confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
      successorLogCoefficient * roundLog * radiusLog := by
    dsimp [successorLogCoefficient]
    calc
      confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
          roundCoefficient * roundLog + (2 * Real.log 2 + 1) * radiusLog := by
        dsimp [confidence, roundCoefficient, roundLog] at hconfidence ⊢
        linarith
      _ ≤ roundCoefficient * (roundLog * radiusLog) +
          (2 * Real.log 2 + 1) * (roundLog * radiusLog) := by
        gcongr
      _ = (roundCoefficient + (2 * Real.log 2 + 1)) * roundLog * radiusLog := by ring
  have hcentralArgument_nonneg : 0 ≤ confidence + Real.log 2 := by positivity
  have hsuccessorArgument_nonneg :
      0 ≤ confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hcoefficientZero_nonneg : 0 ≤ coefficientZero := by positivity
  have hcoefficientOne_nonneg : 0 ≤ coefficientOne := by
    dsimp [coefficientOne, centralLogCoefficient]
    positivity
  have hcoefficientTwo_nonneg : 0 ≤ coefficientTwo := by
    dsimp [coefficientTwo, centralLogCoefficient]
    positivity
  have hcoefficientThree_nonneg : 0 ≤ coefficientThree := by positivity
  have hcoefficientFour_nonneg : 0 ≤ coefficientFour := by
    dsimp [coefficientFour, successorLogCoefficient]
    positivity
  have hcoefficientFive_nonneg : 0 ≤ coefficientFive := by
    dsimp [coefficientFive, successorLogCoefficient]
    positivity
  have hcoefficient_le : ∀ coefficient : ℝ,
      coefficient = coefficientZero ∨ coefficient = coefficientOne ∨
      coefficient = coefficientTwo ∨ coefficient = coefficientThree ∨
      coefficient = coefficientFour ∨ coefficient = coefficientFive →
      coefficient ≤ constant := by
    intro coefficient hcoefficient
    dsimp [constant, subcriticalDimensionHeadRateConstant]
    rcases hcoefficient with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((((le_max_right _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
  have hfullRate {coefficient : ℝ} (hcoefficient_nonneg : 0 ≤ coefficient)
      (hcoefficient : coefficient ≤ constant) :
      coefficient * inverseSquare * radiusLog * roundLog ≤
        constant * inverseSquare * radiusLog * roundLog := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoefficient hinverseSquare_nonneg)
        hradiusLog_nonneg) hroundLog_nonneg
  have hroundRate {coefficient : ℝ} (hcoefficient_nonneg : 0 ≤ coefficient)
      (hcoefficient : coefficient ≤ constant) :
      coefficient * inverseSquare * roundLog ≤
        constant * inverseSquare * radiusLog * roundLog := by
    calc
      coefficient * inverseSquare * roundLog ≤
          coefficient * inverseSquare * radiusLog * roundLog := by
        exact mul_le_mul_of_nonneg_right
          (by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hradiusLog
                (mul_nonneg hcoefficient_nonneg hinverseSquare_nonneg)))
          hroundLog_nonneg
      _ ≤ _ := hfullRate hcoefficient_nonneg hcoefficient
  have hplainRate {coefficient : ℝ} (hcoefficient_nonneg : 0 ≤ coefficient)
      (hcoefficient : coefficient ≤ constant) :
      coefficient * inverseSquare ≤
        constant * inverseSquare * radiusLog * roundLog := by
    calc
      coefficient * inverseSquare ≤ coefficient * inverseSquare * roundLog := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hroundLog
            (mul_nonneg hcoefficient_nonneg hinverseSquare_nonneg))
      _ ≤ _ := hroundRate hcoefficient_nonneg hcoefficient
  have hcentralRootSquare :
      Probability.selectedShellGeometricDimensionOneCentralRootCoefficient confidence ^ 2 ≤
        (2 * baseCoefficient ^ 2 + 8 * centralLogCoefficient) * roundLog := by
    unfold Probability.selectedShellGeometricDimensionOneCentralRootCoefficient
    have hsquare := sq_nonneg
      (baseCoefficient - 2 * Real.sqrt (confidence + Real.log 2))
    have hsqrt := Real.sq_sqrt hcentralArgument_nonneg
    dsimp [baseCoefficient]
    nlinarith
  have hcentralCount :
      Probability.selectedShellGeometricDimensionOneCentralCountCoefficient confidence ≤
        (2 * (32 + 8 * centralLogCoefficient)) * roundLog := by
    unfold Probability.selectedShellGeometricDimensionOneCentralCountCoefficient
    have hfirst : 32 + 8 * (confidence + Real.log 2) ≤
        (32 + 8 * centralLogCoefficient) * roundLog := by
      calc
        32 + 8 * (confidence + Real.log 2) ≤
            32 + 8 * (centralLogCoefficient * roundLog) := by linarith
        _ ≤ (32 + 8 * centralLogCoefficient) * roundLog := by
          nlinarith [hroundLog]
    norm_num
    linarith
  have hsuccessorCount :
      Probability.selectedShellGeometricDimensionOneSuccessorCountCoefficient cutoff ≤
        128 * 8 / radius := by
    have hpower : (2 : ℝ) ^ cutoff ≤ 2 / radius := by
      dsimp [cutoff]
      exact two_pow_subcriticalDimensionHeadCutoff_le_two_div_radius
        heta hradius hradius_le_one
    have hinverseRadius_nonneg : 0 ≤ radius⁻¹ := by positivity
    unfold Probability.selectedShellGeometricDimensionOneSuccessorCountCoefficient
    rw [div_eq_mul_inv] at hpower ⊢
    calc
      128 * (2 * ((2 : ℝ) ^ cutoff - 1)) ≤
          128 * (2 * (2 : ℝ) ^ cutoff) := by nlinarith
      _ ≤ 128 * (2 * (2 * radius⁻¹)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hpower (by norm_num)) (by norm_num)
      _ = (128 * 2 * 2) * radius⁻¹ := by ring
      _ ≤ (128 * 8) * radius⁻¹ :=
        mul_le_mul_of_nonneg_right (by norm_num) hinverseRadius_nonneg
      _ = 128 * 8 * radius⁻¹ := by ring
  have hsuccessorRootSquare :
      Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient cutoff confidence
          tailBound ^ 2 ≤
        (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
          tailMultiplier ^ 2 * roundLog * radiusLog := by
    have hbaseSquare :
        (baseCoefficient + 2 * Real.sqrt
          (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ^ 2 ≤
          (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
            roundLog * radiusLog := by
      have hsquare := sq_nonneg
        (baseCoefficient - 2 * Real.sqrt
          (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2))
      have hsqrt := Real.sq_sqrt hsuccessorArgument_nonneg
      nlinarith
    have hmul :
        ((baseCoefficient + 2 * Real.sqrt
          (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
          tailMultiplier) ^ 2 ≤
        (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
          tailMultiplier ^ 2 * roundLog * radiusLog := by
      rw [mul_pow]
      calc
        (baseCoefficient + 2 * Real.sqrt
            (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ^ 2 *
            tailMultiplier ^ 2 ≤
            ((2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
              roundLog * radiusLog) * tailMultiplier ^ 2 :=
          mul_le_mul_of_nonneg_right hbaseSquare (sq_nonneg tailMultiplier)
        _ = (2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
            tailMultiplier ^ 2 * roundLog * radiusLog := by ring
    unfold Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient
    simpa only [baseCoefficient, tailMultiplier, Nat.cast_add, Nat.cast_one] using hmul
  have hsuccessorSqrtSquare :
      Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient cutoff confidence
          tailBound ^ 2 ≤
        (4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2 *
          roundLog * radiusLog := by
    have hinside : 0 ≤ 16 * ((2 ^ 1 : ℕ) : ℝ) +
        8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) := by positivity
    have hinsideBound : 16 * ((2 ^ 1 : ℕ) : ℝ) +
        8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) ≤
        (32 + 8 * successorLogCoefficient) * roundLog * radiusLog := by
      have hroundRadius_one : 1 ≤ roundLog * radiusLog :=
        one_le_mul_of_one_le_of_one_le hroundLog hradiusLog
      have hsuccessorArgument' :
          confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2 ≤
            successorLogCoefficient * roundLog * radiusLog := by
        simpa only [Nat.cast_add, Nat.cast_one] using hsuccessorArgument
      calc
        16 * ((2 ^ 1 : ℕ) : ℝ) +
            8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) =
            32 + 8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2) := by
          norm_num
        _ ≤ 32 + 8 * (successorLogCoefficient * roundLog * radiusLog) := by
          gcongr
        _ ≤ (32 + 8 * successorLogCoefficient) * roundLog * radiusLog := by
          have hconstant : 32 ≤ 32 * (roundLog * radiusLog) := by
            calc
              (32 : ℝ) = 32 * 1 := by ring
              _ ≤ 32 * (roundLog * radiusLog) :=
                mul_le_mul_of_nonneg_left hroundRadius_one (by norm_num)
          calc
            32 + 8 * (successorLogCoefficient * roundLog * radiusLog) ≤
                32 * (roundLog * radiusLog) +
                  8 * (successorLogCoefficient * roundLog * radiusLog) := by
              simpa only [add_comm] using
                (add_le_add_right hconstant
                  (8 * (successorLogCoefficient * roundLog * radiusLog)))
            _ = (32 + 8 * successorLogCoefficient) * roundLog * radiusLog := by ring
    have hsqrtInside := Real.sq_sqrt hinside
    have hcore :
        4 * (16 * ((2 ^ 1 : ℕ) : ℝ) +
          8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) ≤
        4 * ((32 + 8 * successorLogCoefficient) * roundLog * radiusLog) :=
      mul_le_mul_of_nonneg_left hinsideBound (by norm_num)
    have hmul :
        (2 * Real.sqrt
          (16 * ((2 ^ 1 : ℕ) : ℝ) +
            8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
          tailMultiplier) ^ 2 ≤
        (4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2 *
          roundLog * radiusLog := by
      calc
        (2 * Real.sqrt
            (16 * ((2 ^ 1 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2)) *
            tailMultiplier) ^ 2 =
            (4 * (16 * ((2 ^ 1 : ℕ) : ℝ) +
              8 * (confidence + ((cutoff + 1 : ℕ) : ℝ) * Real.log 2))) *
              tailMultiplier ^ 2 := by
          simp only [mul_pow]
          rw [hsqrtInside]
          ring
        _ ≤ (4 * ((32 + 8 * successorLogCoefficient) * roundLog * radiusLog)) *
            tailMultiplier ^ 2 :=
          mul_le_mul_of_nonneg_right hcore (sq_nonneg tailMultiplier)
        _ = (4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2 *
            roundLog * radiusLog := by ring
    unfold Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient
    simpa only [tailMultiplier, Nat.cast_add, Nat.cast_one] using hmul
  have hgateZero : 6 * 128 / radius ≤
      constant * inverseSquare * radiusLog * roundLog := by
    have hinverseRadius : 1 / radius ≤ inverseSquare := by
      dsimp [inverseSquare]
      have hsquare_le : radius ^ 2 ≤ radius := by
        calc
          radius ^ 2 = radius * radius := by ring
          _ ≤ radius * 1 := mul_le_mul_of_nonneg_left hradius_le_one hradius.le
          _ = radius := by ring
      exact one_div_le_one_div_of_le (sq_pos_of_pos hradius) hsquare_le
    calc
      6 * 128 / radius = coefficientZero * (1 / radius) := by
        dsimp [coefficientZero]
        ring
      _ ≤ coefficientZero * inverseSquare :=
        mul_le_mul_of_nonneg_left hinverseRadius hcoefficientZero_nonneg
      _ ≤ _ := hplainRate hcoefficientZero_nonneg
        (hcoefficient_le _ (Or.inl rfl))
  have hgateOne :
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneCentralRootCoefficient
          confidence ^ 2 / radius ^ 2 ≤
        constant * inverseSquare * radiusLog * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneCentralRootCoefficient
          confidence ^ 2 / radius ^ 2 ≤ coefficientOne * inverseSquare * roundLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionOneCentralRootCoefficient
              confidence ^ 2 / radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionOneCentralRootCoefficient
                confidence ^ 2 * inverseSquare := by dsimp [inverseSquare]; ring
          _ ≤ 6 ^ 2 *
              ((2 * baseCoefficient ^ 2 + 8 * centralLogCoefficient) * roundLog) *
                inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcentralRootSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientOne * inverseSquare * roundLog := by
            dsimp [coefficientOne]
            ring
      _ ≤ _ := hroundRate hcoefficientOne_nonneg
        (hcoefficient_le _ (Or.inr (Or.inl rfl)))
  have hgateTwo :
      6 * Probability.selectedShellGeometricDimensionOneCentralCountCoefficient confidence /
          radius ≤ constant * inverseSquare * radiusLog * roundLog := by
    have hinverseRadius : 1 / radius ≤ inverseSquare := by
      dsimp [inverseSquare]
      have hsquare_le : radius ^ 2 ≤ radius := by
        calc
          radius ^ 2 = radius * radius := by ring
          _ ≤ radius * 1 := mul_le_mul_of_nonneg_left hradius_le_one hradius.le
          _ = radius := by ring
      exact one_div_le_one_div_of_le (sq_pos_of_pos hradius) hsquare_le
    calc
      6 * Probability.selectedShellGeometricDimensionOneCentralCountCoefficient confidence /
          radius ≤ coefficientTwo * (1 / radius) * roundLog := by
        calc
          6 * Probability.selectedShellGeometricDimensionOneCentralCountCoefficient confidence /
              radius = 6 * Probability.selectedShellGeometricDimensionOneCentralCountCoefficient
                confidence * (1 / radius) := by ring
          _ ≤ 6 * ((2 * (32 + 8 * centralLogCoefficient)) * roundLog) *
                (1 / radius) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcentralCount (by norm_num)) (by positivity)
          _ = coefficientTwo * (1 / radius) * roundLog := by
            dsimp [coefficientTwo]
            ring
      _ ≤ coefficientTwo * inverseSquare * roundLog :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hinverseRadius hcoefficientTwo_nonneg)
          hroundLog_nonneg
      _ ≤ _ := hroundRate hcoefficientTwo_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inl rfl))))
  have hgateThree :
      6 * Probability.selectedShellGeometricDimensionOneSuccessorCountCoefficient cutoff /
          radius ≤ constant * inverseSquare * radiusLog * roundLog := by
    calc
      6 * Probability.selectedShellGeometricDimensionOneSuccessorCountCoefficient cutoff /
          radius ≤ coefficientThree * inverseSquare := by
        calc
          6 * Probability.selectedShellGeometricDimensionOneSuccessorCountCoefficient cutoff /
              radius ≤ 6 * (128 * 8 / radius) / radius :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsuccessorCount (by norm_num)) hradius.le
          _ = coefficientThree * inverseSquare := by
            dsimp [coefficientThree, inverseSquare]
            ring
      _ ≤ _ := hplainRate hcoefficientThree_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hgateFour :
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
        constant * inverseSquare * radiusLog * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
          coefficientFour * inverseSquare * radiusLog * roundLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient cutoff
              confidence tailBound ^ 2 / radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorRootCoefficient
                cutoff confidence tailBound ^ 2 * inverseSquare := by
            dsimp [inverseSquare]
            ring
          _ ≤ 6 ^ 2 *
              ((2 * baseCoefficient ^ 2 + 8 * successorLogCoefficient) *
                tailMultiplier ^ 2 * roundLog * radiusLog) * inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsuccessorRootSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientFour * inverseSquare * radiusLog * roundLog := by
            dsimp [coefficientFour]
            ring
      _ ≤ _ := hfullRate hcoefficientFour_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hgateFive :
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
        constant * inverseSquare * radiusLog * roundLog := by
    calc
      6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient cutoff
          confidence tailBound ^ 2 / radius ^ 2 ≤
          coefficientFive * inverseSquare * radiusLog * roundLog := by
        calc
          6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient cutoff
              confidence tailBound ^ 2 / radius ^ 2 =
              6 ^ 2 * Probability.selectedShellGeometricDimensionOneSuccessorSqrtCoefficient
                cutoff confidence tailBound ^ 2 * inverseSquare := by
            dsimp [inverseSquare]
            ring
          _ ≤ 6 ^ 2 *
              ((4 * (32 + 8 * successorLogCoefficient)) * tailMultiplier ^ 2 *
                roundLog * radiusLog) * inverseSquare :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsuccessorSqrtSquare (by norm_num))
              hinverseSquare_nonneg
          _ = coefficientFive * inverseSquare * radiusLog * roundLog := by
            dsimp [coefficientFive]
            ring
      _ ≤ _ := hfullRate hcoefficientFive_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  unfold Probability.selectedShellGeometricDimensionOneEffectiveCountRequirement
  exact max_le hgateZero
    (max_le hgateOne (max_le hgateTwo (max_le hgateThree (max_le hgateFour hgateFive))))

/-- Parameter-only coefficient for the mass and source square-rate gates shared
by every positive dimension. -/
noncomputable def theorem310CommonAllShellRateConstant
    (eta alpha gamma tailBound : ℝ) : ℝ :=
  let roundCoefficient := theorem310RoundLogCoefficient
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  max 1 <| max
    (roundCoefficient / (2 * (shellCoefficient / decay) ^ 2)) <| max
    (roundCoefficient / (shellCoefficient ^ 2 / (18 * tailBound))) <| max
    (roundCoefficient / (shellCoefficient * decay * Real.log 9 / 4)) <| max
    (roundCoefficient / (shellCoefficient * gamma / 4)) <| max
    (1 / (shellCoefficient ^ 2 / (18 * tailBound))) <| max
    (1 / (shellCoefficient * decay * Real.log 9 / 8))
    (1 / ((shellCoefficient * gamma / 4) *
      (Real.rpow 2 (alpha - 1 - eta) - 1)))

theorem one_le_theorem310CommonAllShellRateConstant
    (eta alpha gamma tailBound : ℝ) :
    1 ≤ theorem310CommonAllShellRateConstant eta alpha gamma tailBound := by
  unfold theorem310CommonAllShellRateConstant
  dsimp only
  exact le_max_left _ _

/-- The common mass and source requirements have the inverse-square round
rate independently of the ambient dimension. -/
theorem theorem310CommonAllShellEffectiveCountRequirement_le_rate
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    max
      (Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta
        (radius / Real.rpow 2 (-(1 + eta))) radius gamma tailBound
        (theorem310FailureBudget p round / 2))
      (Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
        eta alpha gamma tailBound radius) ≤
    theorem310CommonAllShellRateConstant eta alpha gamma tailBound *
      (1 / radius ^ 2) * theorem310ShiftedRoundLog p round := by
  let tolerance := theorem310FailureBudget p round / 2
  let roundCoefficient := theorem310RoundLogCoefficient
  let decay := Real.rpow 2 (-(1 + eta))
  let shellCoefficient := Probability.pOneFournierGuillinShellCoefficient eta
  let roundLog := theorem310ShiftedRoundLog p round
  let inverseSquare := 1 / radius ^ 2
  let coefficientZero := roundCoefficient / (2 * (shellCoefficient / decay) ^ 2)
  let coefficientOne := roundCoefficient / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientTwo := roundCoefficient / (shellCoefficient * decay * Real.log 9 / 4)
  let coefficientThree := roundCoefficient / (shellCoefficient * gamma / 4)
  let coefficientFour := 1 / (shellCoefficient ^ 2 / (18 * tailBound))
  let coefficientFive := 1 / (shellCoefficient * decay * Real.log 9 / 8)
  let coefficientSix := 1 / ((shellCoefficient * gamma / 4) *
    (Real.rpow 2 (alpha - 1 - eta) - 1))
  let constant := theorem310CommonAllShellRateConstant eta alpha gamma tailBound
  have hroundCoefficient : 0 < roundCoefficient := theorem310RoundLogCoefficient_pos
  have hdecay : 0 < decay := by
    dsimp [decay]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hshellCoefficient : 0 < shellCoefficient := by
    dsimp [shellCoefficient]
    exact Probability.pOneFournierGuillinShellCoefficient_pos heta
  have hlogNine : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hbase : 1 < Real.rpow 2 (alpha - 1 - eta) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have hroundLog : 1 ≤ roundLog := by
    dsimp [roundLog]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hroundLog_nonneg : 0 ≤ roundLog := zero_le_one.trans hroundLog
  have hinverseSquare_nonneg : 0 ≤ inverseSquare := by
    dsimp [inverseSquare]
    positivity
  obtain ⟨-, hlogEight, hlogSixteen, hlogFour, hlogFourTail⟩ :=
    theorem310_concrete_round_logs_le hp hp_le_one round
  have hcoefficientZero_nonneg : 0 ≤ coefficientZero := by
    dsimp [coefficientZero]
    positivity
  have hcoefficientOne_nonneg : 0 ≤ coefficientOne := by
    dsimp [coefficientOne]
    positivity
  have hcoefficientTwo_nonneg : 0 ≤ coefficientTwo := by
    dsimp [coefficientTwo]
    positivity
  have hcoefficientThree_nonneg : 0 ≤ coefficientThree := by
    dsimp [coefficientThree]
    positivity
  have hcoefficientFour_nonneg : 0 ≤ coefficientFour := by
    dsimp [coefficientFour]
    positivity
  have hcoefficientFive_nonneg : 0 ≤ coefficientFive := by
    dsimp [coefficientFive]
    positivity
  have hcoefficientSix_nonneg : 0 ≤ coefficientSix := by
    dsimp [coefficientSix]
    have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
    positivity
  have hcoefficient_le : ∀ coefficient : ℝ,
      coefficient = coefficientZero ∨ coefficient = coefficientOne ∨
      coefficient = coefficientTwo ∨ coefficient = coefficientThree ∨
      coefficient = coefficientFour ∨ coefficient = coefficientFive ∨
      coefficient = coefficientSix → coefficient ≤ constant := by
    intro coefficient hcoefficient
    dsimp [constant, theorem310CommonAllShellRateConstant]
    rcases hcoefficient with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact (((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((((((le_max_left _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((((((le_max_right _ _).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans
        (le_max_right _ _)).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hroundRate {coefficient : ℝ} (hcoefficient_nonneg : 0 ≤ coefficient)
      (hcoefficient : coefficient ≤ constant) :
      coefficient * inverseSquare * roundLog ≤
        constant * inverseSquare * roundLog := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoefficient hinverseSquare_nonneg) hroundLog_nonneg
  have hplainRate {coefficient : ℝ} (hcoefficient_nonneg : 0 ≤ coefficient)
      (hcoefficient : coefficient ≤ constant) :
      coefficient * inverseSquare ≤ constant * inverseSquare * roundLog := by
    calc
      coefficient * inverseSquare ≤ coefficient * inverseSquare * roundLog := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hroundLog
            (mul_nonneg hcoefficient_nonneg hinverseSquare_nonneg))
      _ ≤ _ := hroundRate hcoefficient_nonneg hcoefficient
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
  have hmassZero : Real.log (8 / tolerance) /
      (2 * (shellCoefficient * (radius / decay)) ^ 2) ≤
      constant * inverseSquare * roundLog := by
    calc
      Real.log (8 / tolerance) / (2 * (shellCoefficient * (radius / decay)) ^ 2) =
          (1 / (2 * (shellCoefficient / decay) ^ 2)) *
            (Real.log (8 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hdecay.ne', hshellCoefficient.ne']
        <;> ring
      _ ≤ coefficientZero * inverseSquare * roundLog := by
        calc
          (1 / (2 * (shellCoefficient / decay) ^ 2)) *
              (Real.log (8 / tolerance) / radius ^ 2) ≤
              (1 / (2 * (shellCoefficient / decay) ^ 2)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogEightScale
              (show 0 ≤ 1 / (2 * (shellCoefficient / decay) ^ 2) by positivity)
          _ = coefficientZero * inverseSquare * roundLog := by
            dsimp [coefficientZero]
            ring
      _ ≤ _ := hroundRate hcoefficientZero_nonneg
        (hcoefficient_le _ (Or.inl rfl))
  have hmassOne : Real.log (16 / tolerance) /
      (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
      constant * inverseSquare * roundLog := by
    calc
      Real.log (16 / tolerance) /
          (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
          (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
            (Real.log (16 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
        <;> ring
      _ ≤ coefficientOne * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
              (Real.log (16 / tolerance) / radius ^ 2) ≤
              (1 / (shellCoefficient ^ 2 / (18 * tailBound))) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogSixteenScale
              (show 0 ≤ 1 / (shellCoefficient ^ 2 / (18 * tailBound)) by positivity)
          _ = coefficientOne * inverseSquare * roundLog := by
            dsimp [coefficientOne]
            ring
      _ ≤ _ := hroundRate hcoefficientOne_nonneg
        (hcoefficient_le _ (Or.inr (Or.inl rfl)))
  have hmassTwo : Real.log (4 / tolerance) /
      (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) ≤
      constant * inverseSquare * roundLog := by
    calc
      Real.log (4 / tolerance) /
          (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 4) =
          (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
            (Real.log (4 / tolerance) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
        <;> ring
      _ ≤ coefficientTwo * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
              (Real.log (4 / tolerance) / radius ^ 2) ≤
              (1 / (shellCoefficient * decay * Real.log 9 / 4)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogFourScale
              (show 0 ≤ 1 / (shellCoefficient * decay * Real.log 9 / 4) by positivity)
          _ = coefficientTwo * inverseSquare * roundLog := by
            dsimp [coefficientTwo]
            ring
      _ ≤ _ := hroundRate hcoefficientTwo_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inl rfl))))
  have hmassThree : Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
      (shellCoefficient * radius ^ 2 * gamma / 4) ≤
      constant * inverseSquare * roundLog := by
    calc
      Real.log (4 / (tolerance * (1 - Real.exp (-1)))) /
          (shellCoefficient * radius ^ 2 * gamma / 4) =
          (1 / (shellCoefficient * gamma / 4)) *
            (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2) := by
        field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne']
        <;> ring
      _ ≤ coefficientThree * inverseSquare * roundLog := by
        calc
          (1 / (shellCoefficient * gamma / 4)) *
              (Real.log (4 / (tolerance * (1 - Real.exp (-1)))) / radius ^ 2) ≤
              (1 / (shellCoefficient * gamma / 4)) *
                (roundCoefficient * inverseSquare * roundLog) :=
            mul_le_mul_of_nonneg_left hlogFourTailScale
              (show 0 ≤ 1 / (shellCoefficient * gamma / 4) by positivity)
          _ = coefficientThree * inverseSquare * roundLog := by
            dsimp [coefficientThree]
            ring
      _ ≤ _ := hroundRate hcoefficientThree_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hmassRequirement :
      Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta
        (radius / decay) radius gamma tailBound tolerance ≤
        constant * inverseSquare * roundLog := by
    unfold Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement
      Probability.pOneFournierGuillinShellWeight
    simp only [Nat.cast_zero, mul_zero, neg_zero]
    have hrpowZero : Real.rpow (2 : ℝ) 0 = 1 := by
      rw [Real.rpow_eq_pow, Real.rpow_zero]
    rw [hrpowZero, mul_one]
    exact max_le hmassZero (max_le hmassOne (max_le hmassTwo hmassThree))
  have hsquareZero : 1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) ≤
      constant * inverseSquare * roundLog := by
    calc
      1 / (shellCoefficient ^ 2 * radius ^ 2 / (18 * tailBound)) =
          coefficientFour * inverseSquare := by
        dsimp [coefficientFour, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', htailBound.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientFour_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hsquareOne : 1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) ≤
      constant * inverseSquare * roundLog := by
    calc
      1 / (shellCoefficient * decay * radius ^ 2 * Real.log 9 / 8) =
          coefficientFive * inverseSquare := by
        dsimp [coefficientFive, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', hdecay.ne', hlogNine.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientFive_nonneg
        (hcoefficient_le _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  have hsquareTwo : 1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
      (Real.rpow 2 (alpha - 1 - eta) - 1)) ≤
      constant * inverseSquare * roundLog := by
    have hbaseSub : 0 < Real.rpow 2 (alpha - 1 - eta) - 1 := sub_pos.mpr hbase
    calc
      1 / ((shellCoefficient * radius ^ 2 * gamma / 4) *
          (Real.rpow 2 (alpha - 1 - eta) - 1)) =
          coefficientSix * inverseSquare := by
        dsimp [coefficientSix, inverseSquare]
        field_simp [hradius.ne', hshellCoefficient.ne', hgamma.ne', hbaseSub.ne']
        <;> ring
      _ ≤ _ := hplainRate hcoefficientSix_nonneg
        (hcoefficient_le _
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  have hsquareRequirement :
      Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
        eta alpha gamma tailBound radius ≤ constant * inverseSquare * roundLog := by
    unfold Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
    exact max_le hsquareZero (max_le hsquareOne hsquareTwo)
  dsimp [tolerance, decay, constant, inverseSquare, roundLog] at hmassRequirement hsquareRequirement
  dsimp [tolerance, decay, constant, inverseSquare, roundLog]
  exact max_le hmassRequirement hsquareRequirement

/-- Parameter-only coefficient for the complete dimension-one selector. -/
noncomputable def subcriticalDimensionSampleRateConstant
    (eta alpha gamma tailBound : ℝ) : ℝ :=
  max (subcriticalDimensionHeadRateConstant tailBound)
    (theorem310CommonAllShellRateConstant eta alpha gamma tailBound)

theorem one_le_subcriticalDimensionSampleRateConstant
    (eta alpha gamma tailBound : ℝ) :
    1 ≤ subcriticalDimensionSampleRateConstant eta alpha gamma tailBound := by
  unfold subcriticalDimensionSampleRateConstant
  exact (one_le_subcriticalDimensionHeadRateConstant tailBound).trans (le_max_left _ _)

/-- The exact all-dimensional requirement specialized to dimension one has
the corrected inverse-square radius power, one inverse-radius logarithm, and
the shifted round logarithm. -/
theorem pOneFournierGuillinAllDimensionalAllShellEffectiveCountRequirement_dimensionOne_le_rate
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    Probability.pOneFournierGuillinAllDimensionalAllShellEffectiveCountRequirement
      1 (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound
      (radius / Real.rpow 2 (-(1 + eta))) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2) ≤
    subcriticalDimensionSampleRateConstant eta alpha gamma tailBound *
      (1 / radius ^ 2) * subcriticalDimensionShiftedRadiusLog radius *
        theorem310ShiftedRoundLog p round := by
  let headConstant := subcriticalDimensionHeadRateConstant tailBound
  let commonConstant := theorem310CommonAllShellRateConstant eta alpha gamma tailBound
  let constant := subcriticalDimensionSampleRateConstant eta alpha gamma tailBound
  let inverseSquare := 1 / radius ^ 2
  let radiusLog := subcriticalDimensionShiftedRadiusLog radius
  let roundLog := theorem310ShiftedRoundLog p round
  have hradiusLog : 1 ≤ radiusLog := by
    dsimp [radiusLog]
    exact one_le_subcriticalDimensionShiftedRadiusLog hradius hradius_le_one
  have hroundLog : 1 ≤ roundLog := by
    dsimp [roundLog]
    exact theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hinverseSquare_nonneg : 0 ≤ inverseSquare := by
    dsimp [inverseSquare]
    positivity
  have hhead :
      Probability.selectedShellGeometricDimensionOneEffectiveCountRequirement
        (Probability.pOneFournierGuillinHeadCutoff eta radius)
        (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
        tailBound radius ≤ headConstant * inverseSquare * radiusLog * roundLog := by
    dsimp [headConstant, inverseSquare, radiusLog, roundLog]
    exact selectedShellGeometricDimensionOneEffectiveCountRequirement_le_subcriticalRate
      heta htailBound hradius hradius_le_one hp hp_le_one round
  have hcommon :
      max
        (Probability.pOneFournierGuillinUniformAllShellMassEffectiveCountRequirement eta
          (radius / Real.rpow 2 (-(1 + eta))) radius gamma tailBound
          (theorem310FailureBudget p round / 2))
        (Probability.pOneFournierGuillinUniformSquareRateEffectiveCountRequirement
          eta alpha gamma tailBound radius) ≤
        commonConstant * inverseSquare * roundLog := by
    dsimp [commonConstant, inverseSquare, roundLog]
    exact theorem310CommonAllShellEffectiveCountRequirement_le_rate
      heta halphaGap hgamma htailBound hradius hp hp_le_one round
  have hheadConstant : headConstant ≤ constant := by
    dsimp [headConstant, constant, subcriticalDimensionSampleRateConstant]
    exact le_max_left _ _
  have hcommonConstant : commonConstant ≤ constant := by
    dsimp [commonConstant, constant, subcriticalDimensionSampleRateConstant]
    exact le_max_right _ _
  have hheadRate : headConstant * inverseSquare * radiusLog * roundLog ≤
      constant * inverseSquare * radiusLog * roundLog := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hheadConstant hinverseSquare_nonneg)
        (zero_le_one.trans hradiusLog)) (zero_le_one.trans hroundLog)
  have hcommonRate : commonConstant * inverseSquare * roundLog ≤
      constant * inverseSquare * radiusLog * roundLog := by
    calc
      commonConstant * inverseSquare * roundLog ≤
          commonConstant * inverseSquare * radiusLog * roundLog := by
        exact mul_le_mul_of_nonneg_right
          (by
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hradiusLog
                (mul_nonneg
                  (zero_le_one.trans
                    (one_le_theorem310CommonAllShellRateConstant eta alpha gamma tailBound))
                  hinverseSquare_nonneg)))
          (zero_le_one.trans hroundLog)
      _ ≤ constant * inverseSquare * radiusLog * roundLog := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcommonConstant hinverseSquare_nonneg)
            (zero_le_one.trans hradiusLog)) (zero_le_one.trans hroundLog)
  unfold Probability.pOneFournierGuillinAllDimensionalAllShellEffectiveCountRequirement
    Probability.selectedShellGeometricHeadEffectiveCountRequirement_byDimension
  simp only [ite_true]
  exact max_le (hhead.trans hheadRate) (hcommon.trans hcommonRate)

/-- The actual positive natural count selected by the existing all-dimensional
schedule at dimension one. -/
noncomputable def subcriticalDimensionRateCountSchedule
    (eta alpha gamma tailBound radius p : ℝ) : ℕ → ℕ := fun round =>
  Probability.pOneFournierGuillinAllDimensionalAllShellEffectiveCount
    1 (Probability.pOneFournierGuillinHeadCutoff eta radius)
    eta alpha gamma tailBound
    (radius / Real.rpow 2 (-(1 + eta))) radius
    (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
    radius (theorem310FailureBudget p round / 2)

/-- The actual dimension-one count has corrected inverse-square radius power,
one inverse-radius logarithm, and the shifted round logarithm. -/
theorem subcriticalDimensionRateCountSchedule_le
    {eta alpha gamma tailBound radius p : ℝ}
    (heta : 0 < eta) (halphaGap : 1 + eta < alpha)
    (hgamma : 0 < gamma) (htailBound : 0 < tailBound)
    (hradius : 0 < radius) (hradius_le_one : radius ≤ 1)
    (hp : 0 < p) (hp_le_one : p ≤ 1) (round : ℕ) :
    (subcriticalDimensionRateCountSchedule eta alpha gamma tailBound radius p round : ℝ) ≤
      2 * subcriticalDimensionSampleRateConstant eta alpha gamma tailBound *
        (1 / radius ^ 2) * subcriticalDimensionShiftedRadiusLog radius *
          theorem310ShiftedRoundLog p round := by
  let requirement :=
    Probability.pOneFournierGuillinAllDimensionalAllShellEffectiveCountRequirement
      1 (Probability.pOneFournierGuillinHeadCutoff eta radius)
      eta alpha gamma tailBound
      (radius / Real.rpow 2 (-(1 + eta))) radius
      (Math.expConfidenceForHalfBudget (theorem310FailureBudget p round))
      radius (theorem310FailureBudget p round / 2)
  let envelope :=
    subcriticalDimensionSampleRateConstant eta alpha gamma tailBound *
      (1 / radius ^ 2) * subcriticalDimensionShiftedRadiusLog radius *
        theorem310ShiftedRoundLog p round
  have hrequirement : requirement ≤ envelope := by
    dsimp [requirement, envelope]
    exact pOneFournierGuillinAllDimensionalAllShellEffectiveCountRequirement_dimensionOne_le_rate
      heta halphaGap hgamma htailBound hradius hradius_le_one hp hp_le_one round
  have hinverse_one : 1 ≤ 1 / radius ^ 2 := by
    simpa using (one_div_pow_le_one_div_pow_dimension hradius hradius_le_one
      (Nat.zero_le 2))
  have hradiusLog_one :=
    one_le_subcriticalDimensionShiftedRadiusLog hradius hradius_le_one
  have hroundLog_one := theorem310ShiftedRoundLog_one_le hp hp_le_one round
  have hconstant_one := one_le_subcriticalDimensionSampleRateConstant
    eta alpha gamma tailBound
  have henvelope_one : 1 ≤ envelope := by
    dsimp [envelope]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hconstant_one hinverse_one)
        hradiusLog_one) hroundLog_one
  have hmax : max 1 requirement ≤ envelope := max_le henvelope_one hrequirement
  have hceil : (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := by
    unfold Math.positiveNatCeil
    exact Nat.ceil_lt_add_one (zero_le_one.trans (le_max_left _ _))
  have hcount_lt : (Math.positiveNatCeil requirement : ℝ) < 2 * envelope := by
    calc
      (Math.positiveNatCeil requirement : ℝ) < max 1 requirement + 1 := hceil
      _ ≤ envelope + 1 := add_le_add hmax le_rfl
      _ ≤ 2 * envelope := by linarith
  unfold subcriticalDimensionRateCountSchedule
    Probability.pOneFournierGuillinAllDimensionalAllShellEffectiveCount
  simpa only [requirement, envelope, mul_assoc] using hcount_lt.le

end PZMH20PerformativePrediction
