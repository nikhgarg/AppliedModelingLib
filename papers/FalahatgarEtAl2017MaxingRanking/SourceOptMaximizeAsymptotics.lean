import FalahatgarEtAl2017MaxingRanking.SourceCutoff
import FalahatgarEtAl2017MaxingRanking.PickAnchorSampling

/-!
# Elementary OPT-Maximize asymptotic bridges

These lemmas retain the rounded, capped integer parameters used by the finite
algorithm and establish only the limiting facts needed to simplify its exact
resource envelope.
-/

namespace FalahatgarEtAl2017MaxingRanking

/--
Eventually the rounded source cutoff dominates `√n`.  The cap is harmless
here: both the population size and the upward-rounded source expression have
that lower bound.
-/
theorem eventually_sqrt_nat_le_sourceOptMaximizeCutoff :
    ∀ᶠ armCount : ℕ in Filter.atTop,
      Real.sqrt (armCount : ℝ) ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
  filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 / 6 : ℝ)]
    with armCount harmCount hlog
  have harmCountNonnegative : 0 ≤ (armCount : ℝ) := by
    exact_mod_cast Nat.zero_le armCount
  have hsixLog : 1 ≤ 6 * Real.log (armCount : ℝ) := by
    nlinarith
  have hsourceArgument : (armCount : ℝ) ≤
      6 * (armCount : ℝ) * Real.log (armCount : ℝ) := by
    calc
      (armCount : ℝ) = (armCount : ℝ) * 1 := by ring
      _ ≤ (armCount : ℝ) * (6 * Real.log (armCount : ℝ)) :=
        mul_le_mul_of_nonneg_left hsixLog harmCountNonnegative
      _ = 6 * (armCount : ℝ) * Real.log (armCount : ℝ) := by ring
  have hpopulationRoot : Real.sqrt (armCount : ℝ) ≤ (armCount : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact harmCountNonnegative
    · have harmCountOne : 1 ≤ (armCount : ℝ) := by exact_mod_cast harmCount
      nlinarith
  have hrawRoot : Real.sqrt (armCount : ℝ) ≤
      ((⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
    calc
      Real.sqrt (armCount : ℝ) ≤
          Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) :=
        Real.sqrt_le_sqrt hsourceArgument
      _ ≤ (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) :=
        Nat.le_ceil _
      _ ≤ ((⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_succ _
  unfold sourceOptMaximizeCutoff
  rw [Nat.cast_min]
  exact le_min hpopulationRoot hrawRoot

/--
The logarithmic factor divided by the actual rounded source cutoff vanishes.
This is the rate bridge that controls the Pick-Anchor comparison term.
-/
theorem tendsto_log_div_sourceOptMaximizeCutoff_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        Real.log (armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ))
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds AppliedModelingLib.Math.tendsto_log_div_sqrt_nat_nhds_zero ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with armCount harmCount
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) harmCount)
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg hlogNonnegative hcutoffNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 2,
    eventually_sqrt_nat_le_sourceOptMaximizeCutoff] with armCount harmCount hcutoff
    have hlogPositive : 0 < Real.log (armCount : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) harmCount)
    have hrootPositive : 0 < Real.sqrt (armCount : ℝ) := by
      apply Real.sqrt_pos.2
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) harmCount)
    have hcutoffPositive : 0 < (sourceOptMaximizeCutoff armCount : ℝ) :=
      lt_of_lt_of_le hrootPositive hcutoff
    exact (div_le_div_iff_of_pos_left hlogPositive hcutoffPositive hrootPositive).2 hcutoff

/-- A cubic logarithm is still negligible compared with `√n`. -/
theorem tendsto_log_cubed_div_sqrt_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (Real.log (armCount : ℝ)) ^ 3 / Real.sqrt (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hreal :
      Filter.Tendsto
        (fun x : ℝ => (Real.log x) ^ 3 / Real.sqrt x)
        Filter.atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_rpow_atTop (3 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- A squared logarithm is negligible compared with the population size. -/
theorem tendsto_log_sq_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hreal :
      Filter.Tendsto
        (fun x : ℝ => (Real.log x) ^ 2 / x)
        Filter.atTop (nhds 0) := by
    simpa using
      (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  exact hreal.comp tendsto_natCast_atTop_atTop

/--
The rounded source cutoff times two source-log factors is sublinear.  This is
the common analytic estimate used by the Prune and final-loop resource terms.
-/
theorem tendsto_sourceOptMaximizeCutoff_mul_log_sq_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) * (Real.log (armCount : ℝ)) ^ 2 /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hcube :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (Real.log (armCount : ℝ)) ^ 3 / Real.sqrt (armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_log_cubed_div_sqrt_nat_nhds_zero
  have hsquare :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_log_sq_div_nat_nhds_zero
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          Real.sqrt 6 *
              ((Real.log (armCount : ℝ)) ^ 3 / Real.sqrt (armCount : ℝ)) +
            2 * ((Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hcube.const_mul (Real.sqrt 6) |>.add (hsquare.const_mul (2 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg (mul_nonneg hcutoffNonnegative (sq_nonneg _)) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := hpopulationPositive.le
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans hlog
    have hlogSq : Real.log (armCount : ℝ) ≤ (Real.log (armCount : ℝ)) ^ 2 := by
      nlinarith
    have hrootBound :
        Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) ≤
          Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ) := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hlogNonnegative)).mp
      rw [Real.sq_sqrt]
      · rw [show (Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ)) ^ 2 =
          6 * (armCount : ℝ) * (Real.log (armCount : ℝ)) ^ 2 by
            rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
              Real.sq_sqrt hpopulationNonnegative]]
        exact mul_le_mul_of_nonneg_left hlogSq (by positivity)
      · positivity
    have hcutoffBound : (sourceOptMaximizeCutoff armCount : ℝ) ≤
        Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ) + 2 :=
      by linarith [sourceOptMaximizeCutoff_real_lt_sqrt_add_two armCount, hrootBound]
    have hratioBound :
        (sourceOptMaximizeCutoff armCount : ℝ) * (Real.log (armCount : ℝ)) ^ 2 /
            (armCount : ℝ) ≤
          (Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ) + 2) *
              (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ) :=
      (div_le_div_iff_of_pos_right hpopulationPositive).2
        (mul_le_mul_of_nonneg_right hcutoffBound (sq_nonneg _))
    calc
      (sourceOptMaximizeCutoff armCount : ℝ) * (Real.log (armCount : ℝ)) ^ 2 /
          (armCount : ℝ) ≤
          (Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ) + 2) *
              (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ) := hratioBound
      _ = Real.sqrt 6 *
            ((Real.log (armCount : ℝ)) ^ 3 / Real.sqrt (armCount : ℝ)) +
          2 * ((Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ)) := by
        field_simp [ne_of_gt hpopulationPositive,
          ne_of_gt (Real.sqrt_pos.2 hpopulationPositive)]
        calc
          Real.sqrt (armCount : ℝ) *
              (Real.sqrt 6 * Real.sqrt (armCount : ℝ) * Real.log (armCount : ℝ) + 2) =
              Real.sqrt 6 * (Real.sqrt (armCount : ℝ)) ^ 2 * Real.log (armCount : ℝ) +
                Real.sqrt (armCount : ℝ) * 2 := by ring
          _ = Real.sqrt 6 * Real.log (armCount : ℝ) * (armCount : ℝ) +
                Real.sqrt (armCount : ℝ) * 2 := by
              rw [Real.sq_sqrt hpopulationNonnegative]
              ring

/-- One source-log factor times the rounded cutoff is also sublinear. -/
theorem tendsto_sourceOptMaximizeCutoff_mul_log_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) * Real.log (armCount : ℝ) /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hsource := tendsto_sourceOptMaximizeCutoff_mul_log_sq_div_nat_nhds_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    exact div_nonneg (mul_nonneg hcutoffNonnegative hlogNonnegative) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1,
    AppliedModelingLib.Math.tendsto_log_nat_atTop.eventually_ge_atTop (1 : ℝ)]
    with armCount harmCount hlog
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    have hlogSq : Real.log (armCount : ℝ) ≤ (Real.log (armCount : ℝ)) ^ 2 := by
      nlinarith
    exact (div_le_div_iff_of_pos_right hpopulationPositive).2
      (mul_le_mul_of_nonneg_left hlogSq hcutoffNonnegative)

/--
The source integer base-two horizon squared, weighted by the rounded cutoff,
is sublinear.  This supplies the multi-round Prune rate calculation.
-/
theorem tendsto_sourceOptMaximizeCutoff_mul_natLogTwo_sq_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount : ℕ) : ℝ) ^ 2 / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let logTwo : ℝ := Real.log 2
  have hlogTwoPositive : 0 < logTwo := by
    dsimp [logTwo]
    exact Real.log_pos (by norm_num)
  have hsource := tendsto_sourceOptMaximizeCutoff_mul_log_sq_div_nat_nhds_zero
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (logTwo ^ 2)⁻¹ *
            ((sourceOptMaximizeCutoff armCount : ℝ) *
              (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hsource.const_mul (logTwo ^ 2)⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg (mul_nonneg hcutoffNonnegative (sq_nonneg _)) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := hpopulationPositive.le
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    have hhorizonNonnegative : 0 ≤ ((Nat.log 2 armCount : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (Nat.log 2 armCount)
    have hhorizonLe : (Nat.log 2 armCount : ℝ) ≤
        Real.log (armCount : ℝ) / logTwo := by
      dsimp [logTwo]
      exact (le_div_iff₀ hlogTwoPositive).mpr (natLogTwo_real_mul_log_two_le_log armCount)
    have hlogRatioNonnegative : 0 ≤ Real.log (armCount : ℝ) / logTwo :=
      div_nonneg hlogNonnegative hlogTwoPositive.le
    have hhorizonSqLe : ((Nat.log 2 armCount : ℕ) : ℝ) ^ 2 ≤
        (Real.log (armCount : ℝ) / logTwo) ^ 2 :=
      (sq_le_sq₀ hhorizonNonnegative hlogRatioNonnegative).mpr hhorizonLe
    have hcutoffRatioNonnegative : 0 ≤
        (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) := by
      exact div_nonneg
        (by exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount))
        hpopulationNonnegative
    calc
      (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount : ℕ) : ℝ) ^ 2 / (armCount : ℝ) =
          ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) *
            ((Nat.log 2 armCount : ℕ) : ℝ) ^ 2 := by ring
      _ ≤ ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) *
            (Real.log (armCount : ℝ) / logTwo) ^ 2 :=
        mul_le_mul_of_nonneg_left hhorizonSqLe hcutoffRatioNonnegative
      _ = (logTwo ^ 2)⁻¹ *
            ((sourceOptMaximizeCutoff armCount : ℝ) *
              (Real.log (armCount : ℝ)) ^ 2 / (armCount : ℝ)) := by
        field_simp [ne_of_gt hpopulationPositive, ne_of_gt hlogTwoPositive]

/-- The rounded cutoff times the source base-two horizon is sublinear. -/
theorem tendsto_sourceOptMaximizeCutoff_mul_natLogTwo_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          (Nat.log 2 armCount : ℝ) / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let logTwo : ℝ := Real.log 2
  have hlogTwoPositive : 0 < logTwo := by
    dsimp [logTwo]
    exact Real.log_pos (by norm_num)
  have hsource := tendsto_sourceOptMaximizeCutoff_mul_log_div_nat_nhds_zero
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          logTwo⁻¹ *
            ((sourceOptMaximizeCutoff armCount : ℝ) * Real.log (armCount : ℝ) /
              (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hsource.const_mul logTwo⁻¹
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg (mul_nonneg hcutoffNonnegative (by exact_mod_cast Nat.zero_le (Nat.log 2 armCount)))
      hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := hpopulationPositive.le
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    have hhorizonLe : (Nat.log 2 armCount : ℝ) ≤
        Real.log (armCount : ℝ) / logTwo := by
      dsimp [logTwo]
      exact (le_div_iff₀ hlogTwoPositive).mpr (natLogTwo_real_mul_log_two_le_log armCount)
    have hcutoffRatioNonnegative : 0 ≤
        (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) := by
      exact div_nonneg
        (by exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount))
        hpopulationNonnegative
    calc
      (sourceOptMaximizeCutoff armCount : ℝ) * (Nat.log 2 armCount : ℝ) /
          (armCount : ℝ) =
          ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) *
            (Nat.log 2 armCount : ℝ) := by ring
      _ ≤ ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) *
            (Real.log (armCount : ℝ) / logTwo) :=
        mul_le_mul_of_nonneg_left hhorizonLe hcutoffRatioNonnegative
      _ = logTwo⁻¹ *
            ((sourceOptMaximizeCutoff armCount : ℝ) * Real.log (armCount : ℝ) /
              (armCount : ℝ)) := by
        field_simp [ne_of_gt hpopulationPositive, ne_of_gt hlogTwoPositive]

/-- The source's actual `log₂ n - 1` Prune horizon has the same linear-rate bound. -/
theorem tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount - 1 : ℕ) : ℝ) / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hsource := tendsto_sourceOptMaximizeCutoff_mul_natLogTwo_div_nat_nhds_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg
      (mul_nonneg hcutoffNonnegative
        (by exact_mod_cast Nat.zero_le (Nat.log 2 armCount - 1))) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    have hhorizonLe : ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ≤ (Nat.log 2 armCount : ℝ) := by
      exact_mod_cast Nat.sub_le (Nat.log 2 armCount) 1
    exact (div_le_div_iff_of_pos_right hpopulationPositive).2
      (mul_le_mul_of_nonneg_left hhorizonLe hcutoffNonnegative)

/-- The squared actual Prune horizon has the same linear-rate bound. -/
theorem tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_sq_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ^ 2 / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hsource := tendsto_sourceOptMaximizeCutoff_mul_natLogTwo_sq_div_nat_nhds_zero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsource ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    exact div_nonneg
      (mul_nonneg hcutoffNonnegative (sq_nonneg _)) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hcutoffNonnegative : 0 ≤ (sourceOptMaximizeCutoff armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount)
    have hsubNonnegative : 0 ≤ ((Nat.log 2 armCount - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (Nat.log 2 armCount - 1)
    have hlogNonnegative : 0 ≤ (Nat.log 2 armCount : ℝ) := by
      exact_mod_cast Nat.zero_le (Nat.log 2 armCount)
    have hhorizonLe : ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ≤ (Nat.log 2 armCount : ℝ) := by
      exact_mod_cast Nat.sub_le (Nat.log 2 armCount) 1
    have hhorizonSqLe : ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ^ 2 ≤
        (Nat.log 2 armCount : ℝ) ^ 2 :=
      (sq_le_sq₀ hsubNonnegative hlogNonnegative).mpr hhorizonLe
    exact (div_le_div_iff_of_pos_right hpopulationPositive).2
      (mul_le_mul_of_nonneg_left hhorizonSqLe hcutoffNonnegative)

/-- The cutoff-dependent core of the source Prune envelope is sublinear. -/
theorem tendsto_sourceOptMaximizePruneCore_div_nat_nhds_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          ((Nat.log 2 armCount - 1 : ℕ) : ℝ) *
          (Real.log (12 / delta) +
            (((Nat.log 2 armCount - 1 : ℕ) : ℝ) + 1) * Real.log 2) /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let confidenceLog : ℝ := Real.log (12 / delta)
  have hhorizon := tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_div_nat_nhds_zero
  have hhorizonSq := tendsto_sourceOptMaximizeCutoff_mul_sourceHorizon_sq_div_nat_nhds_zero
  have hsum :
      Filter.Tendsto
        (fun armCount : ℕ =>
          confidenceLog *
            ((sourceOptMaximizeCutoff armCount : ℝ) *
              ((Nat.log 2 armCount - 1 : ℕ) : ℝ) / (armCount : ℝ)) +
          Real.log 2 *
            ((sourceOptMaximizeCutoff armCount : ℝ) *
                ((Nat.log 2 armCount - 1 : ℕ) : ℝ) ^ 2 / (armCount : ℝ) +
              (sourceOptMaximizeCutoff armCount : ℝ) *
                ((Nat.log 2 armCount - 1 : ℕ) : ℝ) / (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hhorizon.const_mul confidenceLog |>.add
      ((hhorizonSq.add hhorizon).const_mul (Real.log 2))
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards with armCount
  dsimp [confidenceLog]
  ring

/-- The source final-check cutoff factor is sublinear. -/
theorem tendsto_sourceOptMaximizeFinalCutoffCore_div_nat_nhds_zero
    (delta : ℝ) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) *
          (Real.log (12 / delta) + Real.log (armCount : ℝ)) / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let confidenceLog : ℝ := Real.log (12 / delta)
  have hcutoff := tendsto_sourceOptMaximizeCutoff_div_nat_nhds_zero
  have hcutoffLog := tendsto_sourceOptMaximizeCutoff_mul_log_div_nat_nhds_zero
  have hsum :
      Filter.Tendsto
        (fun armCount : ℕ =>
          confidenceLog *
              ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) +
            (sourceOptMaximizeCutoff armCount : ℝ) *
              Real.log (armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa using hcutoff.const_mul confidenceLog |>.add hcutoffLog
  refine Filter.Tendsto.congr' ?_ hsum
  filter_upwards with armCount
  dsimp [confidenceLog]
  ring

/--
With the source cutoff, Pick-Anchor samples a vanishing fraction of the
population at every fixed valid confidence parameter.
-/
theorem tendsto_sourceOptMaximizePickAnchorSampleFraction_nhds_zero
    {anchorDelta : ℝ} (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let confidenceLog : ℝ := Real.log (2 / anchorDelta)
  have hreciprocal :
      Filter.Tendsto
        (fun armCount : ℕ =>
          1 / (sourceOptMaximizeCutoff armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_one_div_sourceOptMaximizeCutoff_nhds_zero
  have hpopulationReciprocal :
      Filter.Tendsto (fun armCount : ℕ => 1 / (armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          confidenceLog * (1 / (sourceOptMaximizeCutoff armCount : ℝ)) +
            1 / (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [confidenceLog] using hreciprocal.const_mul confidenceLog |>.add hpopulationReciprocal
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    have hsampleNonnegative :
        0 ≤ (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) := by
      exact_mod_cast Nat.zero_le
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta)
    have harmCountNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast harmCount.le
    exact div_nonneg hsampleNonnegative harmCountNonnegative
  · filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
    have hcutoff : 0 < sourceOptMaximizeCutoff armCount :=
      sourceOptMaximizeCutoff_pos armCount harmCount
    have hsample := pickAnchorSampleCount_real_lt_sourceFormula_add_one armCount
      (sourceOptMaximizeCutoff armCount) anchorDelta harmCount hcutoff hanchorDelta
      hanchorDeltaLeOne
    have hdivision :
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
            (armCount : ℝ) <
            ((armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ) * confidenceLog + 1) /
              (armCount : ℝ) :=
      (div_lt_div_iff_of_pos_right harmCountReal).2 hsample
    calc
      (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
          (armCount : ℝ) ≤
          ((armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ) * confidenceLog + 1) /
            (armCount : ℝ) := hdivision.le
      _ = confidenceLog * (1 / (sourceOptMaximizeCutoff armCount : ℝ)) +
            1 / (armCount : ℝ) := by
        field_simp [ne_of_gt harmCountReal,
          ne_of_gt (show 0 < (sourceOptMaximizeCutoff armCount : ℝ) by exact_mod_cast hcutoff)]

/--
The Pick-Anchor sample fraction remains negligible even after the logarithmic
per-comparison factor in its source resource cap is included.
-/
theorem tendsto_sourceOptMaximizePickAnchorSampleFraction_mul_log_nhds_zero
    {anchorDelta : ℝ} (hanchorDelta : 0 < anchorDelta)
    (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        ((pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
          (armCount : ℝ)) * Real.log (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let confidenceLog : ℝ := Real.log (2 / anchorDelta)
  have hcutoff :
      Filter.Tendsto
        (fun armCount : ℕ =>
          Real.log (armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_log_div_sourceOptMaximizeCutoff_nhds_zero
  have hpopulation :
      Filter.Tendsto
        (fun armCount : ℕ => Real.log (armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 0) :=
    AppliedModelingLib.Math.tendsto_log_nat_div_nat_nhds_zero
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          confidenceLog *
              (Real.log (armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ)) +
            Real.log (armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [confidenceLog] using hcutoff.const_mul confidenceLog |>.add hpopulation
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hsampleNonnegative :
        0 ≤ (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) := by
      exact_mod_cast Nat.zero_le
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta)
    have harmCountNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    exact mul_nonneg
      (div_nonneg hsampleNonnegative harmCountNonnegative) hlogNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have harmCountReal : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hcutoff : 0 < sourceOptMaximizeCutoff armCount :=
      sourceOptMaximizeCutoff_pos armCount (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount)
    have hlogNonnegative : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast harmCount
    have hsample := pickAnchorSampleCount_real_lt_sourceFormula_add_one armCount
      (sourceOptMaximizeCutoff armCount) anchorDelta
      (lt_of_lt_of_le (by norm_num : 0 < 1) harmCount) hcutoff hanchorDelta
      hanchorDeltaLeOne
    have hfraction :
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
            (armCount : ℝ) ≤
          confidenceLog * (1 / (sourceOptMaximizeCutoff armCount : ℝ)) +
            1 / (armCount : ℝ) := by
      have hdivision :
          (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
              (armCount : ℝ) <
            ((armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ) * confidenceLog + 1) /
                (armCount : ℝ) :=
        (div_lt_div_iff_of_pos_right harmCountReal).2 hsample
      calc
        (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
            (armCount : ℝ) ≤
            ((armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ) * confidenceLog + 1) /
              (armCount : ℝ) := hdivision.le
        _ = confidenceLog * (1 / (sourceOptMaximizeCutoff armCount : ℝ)) +
              1 / (armCount : ℝ) := by
          field_simp [ne_of_gt harmCountReal,
            ne_of_gt (show 0 < (sourceOptMaximizeCutoff armCount : ℝ) by exact_mod_cast hcutoff)]
    calc
      ((pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
          (armCount : ℝ)) * Real.log (armCount : ℝ) ≤
          (confidenceLog * (1 / (sourceOptMaximizeCutoff armCount : ℝ)) +
            1 / (armCount : ℝ)) * Real.log (armCount : ℝ) :=
        mul_le_mul_of_nonneg_right hfraction hlogNonnegative
      _ = confidenceLog *
            (Real.log (armCount : ℝ) / (sourceOptMaximizeCutoff armCount : ℝ)) +
          Real.log (armCount : ℝ) / (armCount : ℝ) := by
        ring

/--
Pick-Anchor's full ceiling-corrected comparison cap is sublinear in the
population at fixed accuracy and confidence.  This keeps the source's actual
rounded sample count instead of substituting a real-valued sample size.
-/
theorem tendsto_sourceOptMaximizePickAnchorComparisonFraction_nhds_zero
    {lower anchorDelta : ℝ} (hlower : 0 < lower)
    (hanchorDelta : 0 < anchorDelta) (hanchorDeltaLeOne : anchorDelta ≤ 1) :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (((pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta - 1 : ℕ) : ℝ) *
          (2 / lower ^ 2 *
            Real.log
              (4 *
                (pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta : ℝ) /
                  anchorDelta) + 1)) /
          (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  let sampleCount : ℕ → ℕ := fun armCount =>
    pickAnchorSampleCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta
  let accuracyFactor : ℝ := 2 / lower ^ 2
  let confidenceConstant : ℝ := Real.log (4 / anchorDelta)
  have hsampleFraction :
      Filter.Tendsto
        (fun armCount : ℕ => (sampleCount armCount : ℝ) / (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [sampleCount] using
      tendsto_sourceOptMaximizePickAnchorSampleFraction_nhds_zero
        hanchorDelta hanchorDeltaLeOne
  have hsampleLogFraction :
      Filter.Tendsto
        (fun armCount : ℕ =>
          ((sampleCount armCount : ℝ) / (armCount : ℝ)) * Real.log (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [sampleCount] using
      tendsto_sourceOptMaximizePickAnchorSampleFraction_mul_log_nhds_zero
        hanchorDelta hanchorDeltaLeOne
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          accuracyFactor *
              (((sampleCount armCount : ℝ) / (armCount : ℝ)) * Real.log (armCount : ℝ)) +
            (accuracyFactor * confidenceConstant + 1) *
              ((sampleCount armCount : ℝ) / (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using hsampleLogFraction.const_mul accuracyFactor |>.add
      (hsampleFraction.const_mul (accuracyFactor * confidenceConstant + 1))
  change Filter.Tendsto
    (fun armCount : ℕ =>
      (((sampleCount armCount - 1 : ℕ) : ℝ) *
        (accuracyFactor *
          Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1)) /
        (armCount : ℝ))
    Filter.atTop (nhds 0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < armCount :=
      lt_of_lt_of_le (by norm_num : 0 < 1) harmCount
    have hcutoffPositive : 0 < sourceOptMaximizeCutoff armCount :=
      sourceOptMaximizeCutoff_pos armCount hpopulationPositive
    have hsamplePositive : 0 < sampleCount armCount := by
      dsimp [sampleCount]
      exact pickAnchorSampleCount_pos armCount (sourceOptMaximizeCutoff armCount) anchorDelta
        hpopulationPositive hcutoffPositive hanchorDelta hanchorDeltaLeOne
    have hlogNonnegative : 0 ≤
        Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hanchorDelta).mpr
      have hsampleOne : 1 ≤ (sampleCount armCount : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr hsamplePositive
      nlinarith
    have hfactorNonnegative : 0 ≤
        accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1 := by
      dsimp [accuracyFactor]
      positivity
    have hsampleMinusOneNonnegative : 0 ≤ ((sampleCount armCount - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.zero_le (sampleCount armCount - 1)
    have hpopulationNonnegative : 0 ≤ (armCount : ℝ) := by
      exact_mod_cast Nat.zero_le armCount
    exact div_nonneg
      (mul_nonneg hsampleMinusOneNonnegative hfactorNonnegative) hpopulationNonnegative
  · filter_upwards [Filter.eventually_ge_atTop 1] with armCount harmCount
    have hpopulationPositive : 0 < armCount :=
      lt_of_lt_of_le (by norm_num : 0 < 1) harmCount
    have hpopulationRealPositive : 0 < (armCount : ℝ) := by
      exact_mod_cast hpopulationPositive
    have hcutoffPositive : 0 < sourceOptMaximizeCutoff armCount :=
      sourceOptMaximizeCutoff_pos armCount hpopulationPositive
    have hsamplePositive : 0 < sampleCount armCount := by
      dsimp [sampleCount]
      exact pickAnchorSampleCount_pos armCount (sourceOptMaximizeCutoff armCount) anchorDelta
        hpopulationPositive hcutoffPositive hanchorDelta hanchorDeltaLeOne
    have hsampleLePopulation : sampleCount armCount ≤ armCount := by
      dsimp [sampleCount]
      exact pickAnchorSampleCount_le_armCount armCount (sourceOptMaximizeCutoff armCount) anchorDelta
    have hsampleRealPositive : 0 < (sampleCount armCount : ℝ) := by
      exact_mod_cast hsamplePositive
    have hsampleLePopulationReal : (sampleCount armCount : ℝ) ≤ (armCount : ℝ) := by
      exact_mod_cast hsampleLePopulation
    have hlogSampleNonnegative : 0 ≤
        Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) := by
      apply Real.log_nonneg
      apply (le_div_iff₀ hanchorDelta).mpr
      have hsampleOne : 1 ≤ (sampleCount armCount : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr hsamplePositive
      nlinarith
    have hfactorSampleNonnegative : 0 ≤
        accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1 := by
      dsimp [accuracyFactor]
      positivity
    have hlogLe : Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) ≤
        Real.log (4 * (armCount : ℝ) / anchorDelta) := by
      apply Real.log_le_log
      · positivity
      · apply (div_le_div_iff_of_pos_right hanchorDelta).2
        gcongr
    have hlogRewrite : Real.log (4 * (armCount : ℝ) / anchorDelta) =
        Real.log (armCount : ℝ) + confidenceConstant := by
      dsimp [confidenceConstant]
      rw [show 4 * (armCount : ℝ) / anchorDelta =
          (armCount : ℝ) * (4 / anchorDelta) by
        field_simp [ne_of_gt hanchorDelta]]
      rw [Real.log_mul (ne_of_gt hpopulationRealPositive) (by positivity)]
    have hfactorLe :
        accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1 ≤
          accuracyFactor * (Real.log (armCount : ℝ) + confidenceConstant) + 1 := by
      rw [← hlogRewrite]
      dsimp [accuracyFactor]
      gcongr
    have hsampleMinusOneLe : ((sampleCount armCount - 1 : ℕ) : ℝ) ≤
        (sampleCount armCount : ℝ) := by
      exact_mod_cast Nat.sub_le (sampleCount armCount) 1
    have hsampleFractionNonnegative : 0 ≤
        (sampleCount armCount : ℝ) / (armCount : ℝ) :=
      div_nonneg (by exact_mod_cast Nat.zero_le (sampleCount armCount))
        hpopulationRealPositive.le
    have hsampleMinusOneFractionLe : ((sampleCount armCount - 1 : ℕ) : ℝ) /
        (armCount : ℝ) ≤ (sampleCount armCount : ℝ) / (armCount : ℝ) :=
      (div_le_div_iff_of_pos_right hpopulationRealPositive).2 hsampleMinusOneLe
    calc
      (((sampleCount armCount - 1 : ℕ) : ℝ) *
          (accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1)) /
          (armCount : ℝ) =
          (((sampleCount armCount - 1 : ℕ) : ℝ) / (armCount : ℝ)) *
            (accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1) := by
        field_simp [ne_of_gt hpopulationRealPositive]
      _ ≤ ((sampleCount armCount : ℝ) / (armCount : ℝ)) *
            (accuracyFactor * Real.log (4 * (sampleCount armCount : ℝ) / anchorDelta) + 1) :=
        mul_le_mul_of_nonneg_right hsampleMinusOneFractionLe hfactorSampleNonnegative
      _ ≤ ((sampleCount armCount : ℝ) / (armCount : ℝ)) *
            (accuracyFactor * (Real.log (armCount : ℝ) + confidenceConstant) + 1) :=
        mul_le_mul_of_nonneg_left hfactorLe hsampleFractionNonnegative
      _ = accuracyFactor *
            (((sampleCount armCount : ℝ) / (armCount : ℝ)) * Real.log (armCount : ℝ)) +
          (accuracyFactor * confidenceConstant + 1) *
            ((sampleCount armCount : ℝ) / (armCount : ℝ)) := by
        ring

end FalahatgarEtAl2017MaxingRanking
