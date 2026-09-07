import AppliedModelingLib.Foundations.Math.Asymptotics
import FalahatgarEtAl2017MaxingRanking.AdaptiveSeqEliminateCost

/-!
# Seq-Eliminate source-budget asymptotics

The source's finite per-call ceiling cap is preserved here before it is
simplified into the printed `n log n` resource shape.
-/

namespace FalahatgarEtAl2017MaxingRanking

open AppliedModelingLib Asymptotics

/-- The exact real source envelope for a size-`armCount` Seq-Eliminate call. -/
noncomputable def seqEliminateSourceComparisonEnvelope
    (armCount : ℕ) (epsilon delta : ℝ) : ℝ :=
  ((armCount - 1 : ℕ) : ℝ) *
    (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1)

/--
The actual adaptive stopping-time total is bounded by the source envelope
when the challenger list has the `armCount - 1` calls of Seq-Eliminate.
-/
theorem adaptiveSeqEliminateStoppingTimes_real_le_sourceScheduleEnvelope
    {Arm Ω : Type*}
    (observation : Arm → Arm → ℕ → Ω → ℝ) (armCount : ℕ) (epsilon delta : ℝ)
    (outcome : Ω) (initial : Arm) (challengers : List Arm)
    (harmCount : 0 < armCount) (hlength : challengers.length = armCount - 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    ((adaptiveSeqEliminateStoppingTimes observation
      (fixedSampleBudget 0 epsilon (delta / (armCount : ℝ))) epsilon
      (delta / (armCount : ℝ)) outcome initial challengers).sum : ℝ) ≤
      seqEliminateSourceComparisonEnvelope armCount epsilon delta := by
  have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
  have heta : 0 < delta / (armCount : ℝ) := div_pos hdelta harmCountReal
  have hetaLeOne : delta / (armCount : ℝ) ≤ 1 := by
    apply (div_le_iff₀ harmCountReal).mpr
    have harmCountOne : 1 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr harmCount
    nlinarith
  have hsource := adaptiveSeqEliminateStoppingTimes_real_le_sourceBudget
    observation epsilon (delta / (armCount : ℝ)) outcome initial challengers heta hetaLeOne
  have hlog : Real.log (2 / (delta / (armCount : ℝ))) =
      Real.log (2 * (armCount : ℝ) / delta) := by
    congr 1
    field_simp [ne_of_gt hdelta, ne_of_gt harmCountReal]
  rw [hlength, hlog] at hsource
  exact hsource

/-- The exact Seq-Eliminate source envelope has one ceiling-aware
all-parameter rate form.  As elsewhere, the shifted logarithm preserves the
valid finite endpoint `delta = 1`. -/
theorem seqEliminateSourceComparisonEnvelope_real_le_sourceRateForm
    (armCount : ℕ) (epsilon delta : ℝ) (harmCount : 0 < armCount)
    (hepsilon : 0 < epsilon) (hepsilonLeOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    seqEliminateSourceComparisonEnvelope armCount epsilon delta ≤
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
  have hcallCountLe : ((armCount - 1 : ℕ) : ℝ) ≤ (armCount : ℝ) := by
    exact_mod_cast Nat.sub_le armCount 1
  have hbatchNonnegative : 0 ≤
      2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1 := by
    have hlogNonnegative : 0 ≤ Real.log (2 * (armCount : ℝ) / delta) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hdelta).mpr
      have harmCountGeOne : 1 ≤ (armCount : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr harmCount
      nlinarith
    positivity
  unfold seqEliminateSourceComparisonEnvelope
  calc
    ((armCount - 1 : ℕ) : ℝ) *
        (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1) ≤
        (armCount : ℝ) *
          (2 / epsilon ^ 2 * Real.log (2 * (armCount : ℝ) / delta) + 1) :=
      mul_le_mul_of_nonneg_right hcallCountLe hbatchNonnegative
    _ ≤ (armCount : ℝ) * (3 * envelope / epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left hbatchBound (Nat.cast_nonneg _)
    _ = 3 * (armCount : ℝ) *
        (1 + Real.log ((armCount : ℝ) / delta)) / epsilon ^ 2 := by
      dsimp [envelope, logFactor]
      ring

/--
At fixed positive accuracy and valid confidence, the source Seq-Eliminate
envelope is `O(n log n)`.  This is the source's `n log(n / delta)` display
with the confidence parameter held fixed, while retaining its exact ceiling
predecessor above.
-/
theorem seqEliminateSourceComparisonEnvelope_isBigO_n_mul_log
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hdeltaLeOne : delta ≤ 1) :
    IsBigO Filter.atTop
      (fun armCount : ℕ => seqEliminateSourceComparisonEnvelope armCount epsilon delta)
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
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hlogNonnegative : 0 ≤ Real.log (2 * (armCount : ℝ) / delta) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hdelta).mpr
      have hpopulationOne : 1 ≤ (armCount : ℝ) := by
        exact_mod_cast harmCount
      nlinarith
    unfold seqEliminateSourceComparisonEnvelope
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le (armCount - 1))
      (add_nonneg (mul_nonneg haccuracyFactorNonnegative hlogNonnegative) zero_le_one)
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
    have hcallCountLe : ((armCount - 1 : ℕ) : ℝ) ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.sub_le armCount 1
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
    unfold seqEliminateSourceComparisonEnvelope
    rw [hlogRewrite]
    calc
      ((armCount - 1 : ℕ) : ℝ) *
          (accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1) ≤
          (armCount : ℝ) *
            (accuracyFactor * (Real.log (armCount : ℝ) + confidenceLog) + 1) :=
        mul_le_mul_of_nonneg_right hcallCountLe hfactorNonnegative
      _ ≤ (armCount : ℝ) * (rateConstant * Real.log (armCount : ℝ)) :=
        mul_le_mul_of_nonneg_left hfactorBound hpopulationNonnegative
      _ = rateConstant * ((armCount : ℝ) * Real.log (armCount : ℝ)) := by ring

end FalahatgarEtAl2017MaxingRanking
