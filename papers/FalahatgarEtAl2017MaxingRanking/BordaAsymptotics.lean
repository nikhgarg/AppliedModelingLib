import AppliedModelingLib.Foundations.Math.Asymptotics
import FalahatgarEtAl2017MaxingRanking.BordaProbability

/-!
# Borda-ranking source-budget asymptotics

Theorem 9 assigns one ceiling-corrected Borda batch to every arm.  This module
keeps that integral total explicit and proves its fixed-parameter source rate.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib Asymptotics

/-- The exact total number of source Borda observations for all arms. -/
noncomputable def bordaTotalSampleCount (armCount : ℕ) (epsilon delta : ℝ) : ℕ :=
  armCount * bordaSampleBudget armCount epsilon delta

/--
The integral total Borda budget is bounded by the source real display with all
ceiling corrections retained in `bordaSampleBudget`.
-/
theorem bordaTotalSampleCount_real_le_sourceEnvelope
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
      (armCount : ℝ) *
        (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1) := by
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  have heta : 0 < delta / (armCount : ℝ) := div_pos hdelta harmCountReal
  have hetaLeOne : delta / (armCount : ℝ) ≤ 1 := by
    apply (div_le_iff₀ harmCountReal).mpr
    have harmCountOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr harmCount
    nlinarith
  have hbudget := fixedSampleBudget_lt_realTarget_add_one 0 epsilon
    (delta / (armCount : ℝ)) heta hetaLeOne
  have hbudgetLe : (bordaSampleBudget armCount epsilon delta : ℝ) ≤
      2 / epsilon ^ 2 * Real.log (2 / (delta / (armCount : ℝ))) + 1 := by
    simpa [bordaSampleBudget] using le_of_lt hbudget
  have hlog : Real.log (2 / (delta / (armCount : ℝ))) =
      Real.log (2 * (armCount : ℝ) / delta) := by
    congr 1
    field_simp [ne_of_gt hdelta, ne_of_gt harmCountReal]
  unfold bordaTotalSampleCount
  rw [Nat.cast_mul]
  rw [hlog] at hbudgetLe
  exact mul_le_mul_of_nonneg_left hbudgetLe (Nat.cast_nonneg _)

/-- Theorem 9's all-arm source count has one explicit ceiling-aware
all-parameter rate form.  The shifted logarithm keeps the finite cost visible
at the valid endpoint `delta = 1`. -/
theorem bordaTotalSampleCount_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
      3 * (armCount : ℝ) *
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
  have hlogBudgetLe : Real.log (2 * (armCount : ℝ) / delta) ≤ envelope := by
    have hlogSplit : Real.log (2 * (armCount : ℝ) / delta) =
        Real.log 2 + logFactor := by
      dsimp [logFactor]
      rw [show 2 * (armCount : ℝ) / delta =
          2 * ((armCount : ℝ) / delta) by field_simp [ne_of_gt hdelta]]
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hratioPos)]
    rw [hlogSplit]
    dsimp [envelope]
    linarith
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
      Real.log (2 * (armCount : ℝ) / delta) / epsilon ^ 2 ≤
        envelope / epsilon ^ 2 := by
    exact div_le_div_of_nonneg_right hlogBudgetLe hepsilonSqPos.le
  have hbatchBound :
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1 ≤
        3 * envelope / epsilon ^ 2 := by
    calc
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1 =
          2 * (Real.log (2 * (armCount : ℝ) / delta) / epsilon ^ 2) + 1 := by
        field_simp [hepsilonSqPos.ne']
      _ ≤ 2 * (envelope / epsilon ^ 2) + envelope / epsilon ^ 2 := by
        gcongr
      _ = 3 * envelope / epsilon ^ 2 := by ring
  have hsource := bordaTotalSampleCount_real_le_sourceEnvelope armCount epsilon delta
    harmCount hdelta hdeltaLeOne
  calc
    (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
        (armCount : ℝ) *
          (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1) := hsource
    _ ≤ (armCount : ℝ) * (3 * envelope / epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left hbatchBound (Nat.cast_nonneg _)
    _ = 3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 := by
      dsimp [envelope, logFactor]
      ring

/--
At fixed positive accuracy and valid confidence, Theorem 9's integral Borda
sampling budget is `O(n log n)`.
-/
theorem bordaTotalSampleCount_isBigO_n_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ => (bordaTotalSampleCount armCount epsilon delta : ℝ))
      (fun armCount : ℕ => (armCount : ℝ) * Real.log (armCount : ℝ)) := by
  let accuracyFactor : ℝ := 2 / epsilon ^ 2
  let confidenceLog : ℝ := Real.log (2 / delta)
  let rateConstant : ℝ := accuracyFactor * (confidenceLog + 1) + 1
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
    exact_mod_cast Nat.zero_le (bordaTotalSampleCount armCount epsilon delta)
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    exact mul_nonneg hpopulationNonnegative
      ((by norm_num : (0 : ℝ) ≤ 1).trans hlog)
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := hpopulationPositive.le
    have hsource := bordaTotalSampleCount_real_le_sourceEnvelope armCount epsilon delta
      (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount) hdelta hdeltaLeOne
    have hlogRewrite : Real.log (2 * (armCount : ℝ) / delta) =
        Real.log (armCount : ℝ) + confidenceLog := by
      dsimp [confidenceLog]
      rw [show 2 * (armCount : ℝ) / delta = (armCount : ℝ) * (2 / delta) by
        field_simp [ne_of_gt hdelta]]
      rw [Real.log_mul (ne_of_gt hpopulationPositive) (by positivity)]
    have hconfidenceScaled : confidenceLog ≤ confidenceLog * Real.log (armCount : ℝ) := by
      calc
        confidenceLog = confidenceLog * 1 := by ring
        _ ≤ confidenceLog * Real.log (armCount : ℝ) :=
          mul_le_mul_of_nonneg_left hlog hconfidenceLogNonnegative
    have hfactorBound :
        accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1 ≤
          rateConstant * Real.log (armCount : ℝ) := by
      calc
        accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1 ≤
            accuracyFactor *
                (Real.log (armCount : ℝ) + confidenceLog * Real.log (armCount : ℝ)) +
              Real.log (armCount : ℝ) := by
          gcongr
        _ = rateConstant * Real.log (armCount : ℝ) := by
          dsimp [rateConstant]
          ring
    have hfactorNonnegative : 0 ≤
        accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1 := by
      positivity
    rw [hlogRewrite] at hsource
    calc
      (bordaTotalSampleCount armCount epsilon delta : ℝ) ≤
          (armCount : ℝ) *
            (accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1) := by
        simpa [accuracyFactor] using hsource
      _ ≤ (armCount : ℝ) * (rateConstant * Real.log (armCount : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactorBound hpopulationNonnegative
      _ = rateConstant * ((armCount : ℝ) * Real.log (armCount : ℝ)) := by ring

end FalahatgarEtAl2017MaxingRanking
