import AppliedModelingLib.Foundations.Math.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import FalahatgarEtAl2017MaxingRanking.CanonicalStrongTransitivityRanking

/-!
# Strong-Transitivity-Ranking resource asymptotics

Appendix B.2 samples one fixed batch for each unordered distinct pair.  The
exact natural comparison count remains visible in
`strongTransitivityComparisonCount`; this file derives its finite
ceiling-corrected source envelope and its fixed-accuracy, fixed-confidence
quadratic-logarithmic rate.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib Asymptotics

/-- The real-valued source envelope for Algorithm 7's exact unordered-pair
comparison count, retaining the ceiling correction in every Algorithm-6
batch. -/
noncomputable def strongTransitivityComparisonEnvelope
    (armCount : ℕ) (epsilon delta : ℝ) : ℝ :=
  ((armCount.choose 2 : ℕ) : ℝ) *
    (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) ^ 2 / delta) + 1)

/-- The literal Algorithm-7 comparison count is bounded by the source
ceiling-corrected real envelope. -/
theorem strongTransitivityComparisonCount_real_le_sourceEnvelope
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
      strongTransitivityComparisonEnvelope armCount epsilon delta := by
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  have harmCountSqPos : 0 < (armCount : ℝ) ^ 2 := sq_pos_of_pos harmCountReal
  have heta : 0 < delta / (armCount : ℝ) ^ 2 := div_pos hdelta harmCountSqPos
  have hetaLeOne : delta / (armCount : ℝ) ^ 2 ≤ 1 := by
    have harmCountGeOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr harmCount
    have harmCountSqGeOne : 1 ≤ (armCount : ℝ) ^ 2 := by
      nlinarith [sq_nonneg ((armCount : ℝ) - 1)]
    have hle : delta / (armCount : ℝ) ^ 2 ≤ delta := by
      apply (div_le_iff₀ harmCountSqPos).mpr
      nlinarith
    exact hle.trans hdeltaLeOne
  have hbudget := fixedSampleBudget_lt_realTarget_add_one 0 epsilon
    (delta / (armCount : ℝ) ^ 2) heta hetaLeOne
  have hbudgetLe :
      (strongTransitivitySampleBudget armCount epsilon delta : ℝ) ≤
        2 / epsilon ^ 2 * Real.log (2 / (delta / (armCount : ℝ) ^ 2)) + 1 := by
    simpa [strongTransitivitySampleBudget] using le_of_lt hbudget
  have hlog : Real.log (2 / (delta / (armCount : ℝ) ^ 2)) =
      Real.log (2 * (armCount : ℝ) ^ 2 / delta) := by
    congr 1
    field_simp [ne_of_gt hdelta, ne_of_gt harmCountSqPos]
  rw [strongTransitivityComparisonCount_eq]
  simp only [Fintype.card_fin]
  rw [Nat.cast_mul]
  rw [hlog] at hbudgetLe
  unfold strongTransitivityComparisonEnvelope
  exact mul_le_mul_of_nonneg_left hbudgetLe (Nat.cast_nonneg _)

/-- The exact Algorithm-7 count has a uniform source-rate form.  The shifted
logarithm is deliberate: it retains the finite ceiling term at the valid
endpoint `delta = 1` instead of silently treating a zero logarithm as a
positive resource bound. -/
theorem strongTransitivityComparisonCount_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
      5 * (armCount : ℝ) ^ 2 *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 := by
  let logFactor : ℝ := Real.log ((armCount : ℝ) / delta)
  let envelope : ℝ := 1 + logFactor
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  have hratioPos : 0 < (armCount : ℝ) / delta := div_pos harmCountReal hdelta
  have hratioGeOne : 1 ≤ (armCount : ℝ) / delta := by
    apply (le_div_iff₀ hdelta).mpr
    have harmCountGeOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr harmCount
    nlinarith
  have hlogFactorNonnegative : 0 ≤ logFactor := by
    dsimp [logFactor]
    exact Real.log_nonneg hratioGeOne
  have hlogTwoLeOne : Real.log (2 : ℝ) ≤ 1 := by
    apply (Real.exp_le_exp).mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    simpa [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hlogArmLe : Real.log (armCount : ℝ) ≤ logFactor := by
    dsimp [logFactor]
    apply Real.log_le_log harmCountReal
    apply (le_div_iff₀ hdelta).mpr
    nlinarith [hdeltaLeOne]
  have hlogBudgetLe : Real.log (2 * (armCount : ℝ) ^ 2 / delta) ≤
      2 * envelope := by
    have hlogSplit : Real.log (2 * (armCount : ℝ) ^ 2 / delta) =
        Real.log 2 + logFactor + Real.log (armCount : ℝ) := by
      dsimp [logFactor]
      rw [show 2 * (armCount : ℝ) ^ 2 / delta =
          2 * ((armCount : ℝ) / delta) * (armCount : ℝ) by
        field_simp [ne_of_gt hdelta]]
      rw [Real.log_mul (mul_ne_zero (by norm_num) (ne_of_gt hratioPos))
        (ne_of_gt harmCountReal)]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hratioPos)]
    rw [hlogSplit]
    dsimp [envelope]
    nlinarith
  have hepsilonSqPos : 0 < epsilon ^ 2 := sq_pos_of_pos hepsilon
  have hepsilonSqLeOne : epsilon ^ 2 ≤ 1 := by
    simpa using (sq_le_sq₀ hepsilon.le (by norm_num)).mpr hepsilonLeOne
  have hinvEpsilonSqGeOne : 1 ≤ 1 / epsilon ^ 2 := by
    apply (le_div_iff₀ hepsilonSqPos).mpr
    simpa using hepsilonSqLeOne
  have henvelopeOverEpsilonSqGeOne : 1 ≤ envelope / epsilon ^ 2 := by
    calc
      1 ≤ 1 / epsilon ^ 2 := hinvEpsilonSqGeOne
      _ ≤ envelope / epsilon ^ 2 := by
        exact div_le_div_of_nonneg_right (by dsimp [envelope]; linarith) hepsilonSqPos.le
  have hlogOverEpsilonSq :
      Real.log (2 * (armCount : ℝ) ^ 2 / delta) / epsilon ^ 2 ≤
        2 * envelope / epsilon ^ 2 := by
    exact div_le_div_of_nonneg_right hlogBudgetLe hepsilonSqPos.le
  have hbatchBound :
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) ^ 2 / delta) + 1 ≤
        5 * envelope / epsilon ^ 2 := by
    calc
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) ^ 2 / delta) + 1 =
          2 * (Real.log (2 * (armCount : ℝ) ^ 2 / delta) / epsilon ^ 2) + 1 := by
        field_simp [hepsilonSqPos.ne']
      _ ≤ 2 * (2 * envelope / epsilon ^ 2) + envelope / epsilon ^ 2 := by
        gcongr
      _ = 5 * envelope / epsilon ^ 2 := by ring
  have hchooseLe : ((armCount.choose 2 : ℕ) : ℝ) ≤ (armCount : ℝ) ^ 2 := by
    exact_mod_cast Nat.choose_le_pow armCount 2
  have hsource := strongTransitivityComparisonCount_real_le_sourceEnvelope
    armCount epsilon delta harmCount hdelta hdeltaLeOne
  unfold strongTransitivityComparisonEnvelope at hsource
  calc
    (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
        ((armCount.choose 2 : ℕ) : ℝ) *
          (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) ^ 2 / delta) + 1) := hsource
    _ ≤ ((armCount.choose 2 : ℕ) : ℝ) * (5 * envelope / epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left hbatchBound (Nat.cast_nonneg _)
    _ ≤ (armCount : ℝ) ^ 2 * (5 * envelope / epsilon ^ 2) :=
      mul_le_mul_of_nonneg_right hchooseLe (by positivity)
    _ = 5 * (armCount : ℝ) ^ 2 *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 := by
      dsimp [envelope, logFactor]
      ring

/-- At fixed positive accuracy and valid confidence, Algorithm 7's exact
unordered-pair comparison count has the source quadratic-logarithmic rate. -/
theorem strongTransitivityComparisonCount_isBigO_n_sq_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ =>
        (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ))
      (fun armCount : ℕ => (armCount : ℝ) ^ 2 * Real.log (armCount : ℝ)) := by
  let accuracyFactor : ℝ := 2 / epsilon ^ 2
  let confidenceLog : ℝ := Real.log (2 / delta)
  let rateConstant : ℝ := 2 * accuracyFactor + accuracyFactor * confidenceLog + 1
  have haccuracyFactorNonnegative : 0 ≤ accuracyFactor := by
    dsimp [accuracyFactor]
    positivity
  have hconfidenceLogNonnegative : 0 ≤ confidenceLog := by
    dsimp [confidenceLog]
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).mpr
    nlinarith
  have hrateConstantNonnegative : 0 ≤ rateConstant := by
    dsimp [rateConstant]
    positivity
  apply AppliedModelingLib.Math.isBigO_of_eventually_nonneg_le_const_mul
    hrateConstantNonnegative
  · filter_upwards with armCount
    exact_mod_cast Nat.zero_le (strongTransitivityComparisonCount
      (Arm := Fin armCount) epsilon delta)
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    exact mul_nonneg (sq_nonneg _) ((by norm_num : (0 : ℝ) ≤ 1).trans hlog)
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := hpopulationPositive.le
    have hchooseLe : ((armCount.choose 2 : ℕ) : ℝ) ≤ (armCount : ℝ) ^ 2 := by
      exact_mod_cast Nat.choose_le_pow armCount 2
    have hsource := strongTransitivityComparisonCount_real_le_sourceEnvelope
      armCount epsilon delta
      (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount) hdelta hdeltaLeOne
    have hlogRewrite : Real.log (2 * (armCount : ℝ) ^ 2 / delta) =
        2 * Real.log (armCount : ℝ) + confidenceLog := by
      dsimp [confidenceLog]
      have hratioPositive : 0 < 2 / delta := div_pos (by norm_num) hdelta
      rw [show 2 * (armCount : ℝ) ^ 2 / delta =
          (armCount : ℝ) * ((armCount : ℝ) * (2 / delta)) by
        field_simp [ne_of_gt hdelta]]
      rw [Real.log_mul (ne_of_gt hpopulationPositive)
        (mul_ne_zero (ne_of_gt hpopulationPositive) (ne_of_gt hratioPositive))]
      rw [Real.log_mul (ne_of_gt hpopulationPositive) (ne_of_gt hratioPositive)]
      ring
    have hconfidenceScaled : confidenceLog ≤ confidenceLog * Real.log (armCount : ℝ) := by
      calc
        confidenceLog = confidenceLog * 1 := by ring
        _ ≤ confidenceLog * Real.log (armCount : ℝ) :=
          mul_le_mul_of_nonneg_left hlog hconfidenceLogNonnegative
    have hfactorBound :
        accuracyFactor * (2 * Real.log (armCount : ℝ) + confidenceLog) + 1 ≤
          rateConstant * Real.log (armCount : ℝ) := by
      calc
        accuracyFactor * (2 * Real.log (armCount : ℝ) + confidenceLog) + 1 ≤
            accuracyFactor *
                (2 * Real.log (armCount : ℝ) +
                  confidenceLog * Real.log (armCount : ℝ)) +
              Real.log (armCount : ℝ) := by
          gcongr
        _ = rateConstant * Real.log (armCount : ℝ) := by
          dsimp [rateConstant]
          ring
    have hfactorNonnegative : 0 ≤
        accuracyFactor * (2 * Real.log (armCount : ℝ) + confidenceLog) + 1 := by
      positivity
    unfold strongTransitivityComparisonEnvelope at hsource
    rw [hlogRewrite] at hsource
    calc
      (strongTransitivityComparisonCount (Arm := Fin armCount) epsilon delta : ℝ) ≤
          ((armCount.choose 2 : ℕ) : ℝ) *
            (accuracyFactor * (2 * Real.log (armCount : ℝ) + confidenceLog) + 1) := by
        simpa [strongTransitivityComparisonEnvelope, accuracyFactor] using hsource
      _ ≤ (armCount : ℝ) ^ 2 *
            (accuracyFactor * (2 * Real.log (armCount : ℝ) + confidenceLog) + 1) :=
        mul_le_mul_of_nonneg_right hchooseLe hfactorNonnegative
      _ ≤ (armCount : ℝ) ^ 2 * (rateConstant * Real.log (armCount : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactorBound (sq_nonneg _)
      _ = rateConstant * ((armCount : ℝ) ^ 2 * Real.log (armCount : ℝ)) := by ring

end FalahatgarEtAl2017MaxingRanking
