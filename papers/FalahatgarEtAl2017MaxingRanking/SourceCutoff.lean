import AppliedModelingLib.Foundations.Math.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Rounded source cutoff for OPT-Maximize

Algorithm 3 uses a cardinality cutoff written as `sqrt (6 n log n)`.  The
algorithmic object must be integral, so this module uses a strictly larger
rounded value and caps it at the population size.  The cap is inactive on the
only branch that runs Prune.
-/

namespace FalahatgarEtAl2017MaxingRanking

/-- A total integer realization of Algorithm 3's displayed Prune cutoff. -/
noncomputable def sourceOptMaximizeCutoff (armCount : ℕ) : ℕ :=
  min armCount (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1)

/-- The rounded cutoff never exceeds the available population. -/
theorem sourceOptMaximizeCutoff_le_armCount (armCount : ℕ) :
    sourceOptMaximizeCutoff armCount ≤ armCount := by
  exact Nat.min_le_left _ _

/-- The capped cutoff is no larger than its upward-rounded source expression. -/
theorem sourceOptMaximizeCutoff_le_raw (armCount : ℕ) :
    sourceOptMaximizeCutoff armCount ≤
      ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 := by
  exact Nat.min_le_right _ _

/--
The source cutoff is within two of the displayed square-root expression.  The
second unit accounts for the strict integral realization after taking a
natural ceiling.
-/
theorem sourceOptMaximizeCutoff_real_lt_sqrt_add_two (armCount : ℕ) :
    (sourceOptMaximizeCutoff armCount : ℝ) <
      Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) + 2 := by
  have hraw := sourceOptMaximizeCutoff_le_raw armCount
  have hrawReal : (sourceOptMaximizeCutoff armCount : ℝ) ≤
      ((⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hraw
  have hceil : (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) <
      Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (ha := Real.sqrt_nonneg _)
  rw [Nat.cast_add, Nat.cast_one] at hrawReal
  calc
    (sourceOptMaximizeCutoff armCount : ℝ) ≤
        (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) + 1 := hrawReal
    _ < Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) + 2 := by linarith

/--
The rounded Algorithm-3 cutoff is negligible relative to the population size.
This is the analytic bridge behind the source's square-root cutoff display;
the finite algorithm continues to use `sourceOptMaximizeCutoff` itself.
-/
theorem tendsto_sourceOptMaximizeCutoff_div_nat_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ =>
        (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ))
      Filter.atTop (nhds 0) := by
  have hroot :
      Filter.Tendsto
        (fun armCount : ℕ =>
          Real.sqrt
            (6 * (Real.log (armCount : ℝ) / (armCount : ℝ))))
        Filter.atTop (nhds 0) := by
    have hinside :
        Filter.Tendsto
          (fun armCount : ℕ =>
            6 * (Real.log (armCount : ℝ) / (armCount : ℝ)))
          Filter.atTop (nhds 0) := by
      simpa using
        AppliedModelingLib.Math.tendsto_log_nat_div_nat_nhds_zero.const_mul (6 : ℝ)
    simpa only [Function.comp_apply, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hinside
  have hroot' :
      Filter.Tendsto
        (fun armCount : ℕ =>
          Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) /
            (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    refine Filter.Tendsto.congr' ?_ hroot
    filter_upwards [Filter.eventually_ge_atTop 3] with armCount harmCount
    have harmCountPos : 0 < (armCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) harmCount)
    have hlogNonneg : 0 ≤ Real.log (armCount : ℝ) := by
      apply Real.log_nonneg
      exact_mod_cast (le_trans (by norm_num : 1 ≤ 3) harmCount)
    have hleftNonneg :
        0 ≤ Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) /
          (armCount : ℝ) :=
      div_nonneg (Real.sqrt_nonneg _) harmCountPos.le
    have hrightNonneg :
        0 ≤ Real.sqrt
          (6 * (Real.log (armCount : ℝ) / (armCount : ℝ))) :=
      Real.sqrt_nonneg _
    have hleftSquare :
        (Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) /
            (armCount : ℝ)) ^ 2 =
          6 * (Real.log (armCount : ℝ) / (armCount : ℝ)) := by
      rw [div_pow, Real.sq_sqrt]
      · field_simp [harmCountPos.ne']
      · positivity
    have hrightSquare :
        (Real.sqrt
          (6 * (Real.log (armCount : ℝ) / (armCount : ℝ)))) ^ 2 =
          6 * (Real.log (armCount : ℝ) / (armCount : ℝ)) := by
      rw [Real.sq_sqrt]
      exact mul_nonneg (by norm_num) (div_nonneg hlogNonneg harmCountPos.le)
    nlinarith
  have htwo :
      Filter.Tendsto (fun armCount : ℕ => 2 / (armCount : ℝ))
        Filter.atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat 2
  have hupper :
      Filter.Tendsto
        (fun armCount : ℕ =>
          (Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) + 2) /
            (armCount : ℝ))
        Filter.atTop (nhds 0) := by
    simpa [add_div] using hroot'.add htwo
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    exact div_nonneg (by exact_mod_cast Nat.zero_le (sourceOptMaximizeCutoff armCount))
      (by exact_mod_cast harmCount.le)
  · filter_upwards [Filter.eventually_gt_atTop 0] with armCount harmCount
    have harmCountReal : 0 < (armCount : ℝ) := by exact_mod_cast harmCount
    have hcutoff := sourceOptMaximizeCutoff_real_lt_sqrt_add_two armCount
    exact (div_le_div_iff_of_pos_right harmCountReal).2 hcutoff.le

/--
For every fixed positive confidence parameter, sufficiently large populations
take the repaired Prune branch.  This follows from the rounded source cutoff,
not from a separate asymptotic replacement of the algorithm.
-/
theorem eventually_six_sourceOptMaximizeCutoff_div_lt
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ armCount : ℕ in Filter.atTop,
      6 * (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) < delta := by
  have hscaled :
      Filter.Tendsto
        (fun armCount : ℕ =>
          6 * ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)))
        Filter.atTop (nhds 0) := by
    simpa using tendsto_sourceOptMaximizeCutoff_div_nat_nhds_zero.const_mul (6 : ℝ)
  have heventual :
      ∀ᶠ armCount : ℕ in Filter.atTop,
        6 * ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) < delta :=
    hscaled.eventually (eventually_lt_nhds hdelta)
  filter_upwards [heventual] with armCount harmCount
  calc
    6 * (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) =
        6 * ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) := by ring
    _ < delta := harmCount

/-- The rounded source cutoff itself diverges with the population size. -/
theorem tendsto_sourceOptMaximizeCutoff_atTop :
    Filter.Tendsto sourceOptMaximizeCutoff Filter.atTop Filter.atTop := by
  have hroot :
      Filter.Tendsto
        (fun armCount : ℕ =>
          Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)))
        Filter.atTop Filter.atTop := by
    have hproduct :
        Filter.Tendsto
          (fun armCount : ℕ =>
            (armCount : ℝ) * Real.log (armCount : ℝ))
          Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_atTop₀
        AppliedModelingLib.Math.tendsto_log_nat_atTop
    have hscaled :
        Filter.Tendsto
          (fun armCount : ℕ =>
            6 * ((armCount : ℝ) * Real.log (armCount : ℝ)))
          Filter.atTop Filter.atTop :=
      hproduct.const_mul_atTop (by norm_num)
    simpa only [Function.comp_apply, mul_assoc] using
      Real.tendsto_sqrt_atTop.comp hscaled
  let raw : ℕ → ℕ := fun armCount =>
    ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1
  have hraw : Filter.Tendsto raw Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro bound
    filter_upwards [hroot.eventually_ge_atTop (bound : ℝ)] with armCount harmCount
    have hceil : (bound : ℝ) ≤
        (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) :=
      harmCount.trans (Nat.le_ceil _)
    have hceilNat : bound ≤
        ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ := by
      exact_mod_cast hceil
    dsimp [raw]
    omega
  refine Filter.tendsto_atTop.2 ?_
  intro bound
  filter_upwards [Filter.eventually_ge_atTop bound, hraw.eventually_ge_atTop bound]
    with armCount harmCount hrawCount
  unfold sourceOptMaximizeCutoff
  change bound ≤ min armCount (raw armCount)
  exact le_min harmCount hrawCount

/-- The reciprocal source cutoff vanishes, controlling Pick-Anchor's sample fraction. -/
theorem tendsto_one_div_sourceOptMaximizeCutoff_nhds_zero :
    Filter.Tendsto
      (fun armCount : ℕ => 1 / (sourceOptMaximizeCutoff armCount : ℝ))
      Filter.atTop (nhds 0) :=
  Filter.Tendsto.const_div_atTop
    (tendsto_natCast_atTop_atTop.comp tendsto_sourceOptMaximizeCutoff_atTop) (1 : ℝ)

/-- A nonempty population has a positive rounded cutoff. -/
theorem sourceOptMaximizeCutoff_pos (armCount : ℕ) (hcount : 0 < armCount) :
    0 < sourceOptMaximizeCutoff armCount := by
  unfold sourceOptMaximizeCutoff
  rw [lt_min_iff]
  exact ⟨hcount, Nat.succ_pos _⟩

/-- Whenever the rounded cutoff is strictly below the population, the cap is
inactive.  This structural form avoids tying source rounding to any particular
confidence-allocation constant. -/
theorem sourceOptMaximizeCutoff_eq_raw_of_lt_armCount
    (armCount : ℕ)
    (hcutoffLt : sourceOptMaximizeCutoff armCount < armCount) :
    sourceOptMaximizeCutoff armCount =
      ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 := by
  let raw : ℕ := ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1
  have hrawLe : raw ≤ armCount := by
    by_contra hrawLe
    have hrawGt : armCount < raw := Nat.lt_of_not_ge hrawLe
    have hcutoffEq : sourceOptMaximizeCutoff armCount = armCount := by
      unfold sourceOptMaximizeCutoff
      change min armCount raw = armCount
      exact Nat.min_eq_left (Nat.le_of_lt hrawGt)
    rw [hcutoffEq] at hcutoffLt
    exact (Nat.lt_irrefl armCount hcutoffLt)
  unfold sourceOptMaximizeCutoff
  change min armCount raw = raw
  exact Nat.min_eq_right hrawLe

/-- An inactive cap makes the integral cutoff strictly exceed the displayed
square-root threshold, independently of how the caller allocates confidence. -/
theorem sourceOptMaximizeCutoff_sqrt_lt_of_lt_armCount
    (armCount : ℕ)
    (hcutoffLt : sourceOptMaximizeCutoff armCount < armCount) :
    Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) <
      (sourceOptMaximizeCutoff armCount : ℝ) := by
  rw [sourceOptMaximizeCutoff_eq_raw_of_lt_armCount armCount hcutoffLt]
  calc
    Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) ≤
        (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ < ((⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self _

/-- If Prune's whole population is not already below twice the source cutoff,
then the rounded square-root cutoff is at least four. -/
theorem four_le_sourceOptMaximizeCutoff_of_two_mul_lt
    (armCount : ℕ)
    (hlarge : 2 * sourceOptMaximizeCutoff armCount < armCount) :
    4 ≤ sourceOptMaximizeCutoff armCount := by
  have hcountPos : 0 < armCount := by omega
  have hcutoffPos := sourceOptMaximizeCutoff_pos armCount hcountPos
  have hcountThree : 3 ≤ armCount := by omega
  have hlogTwo : (1 / 2 : ℝ) < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlog : (1 / 2 : ℝ) < Real.log (armCount : ℝ) := by
    calc
      (1 / 2 : ℝ) < Real.log 2 := hlogTwo
      _ ≤ Real.log (armCount : ℝ) := by
        apply Real.log_le_log (by norm_num)
        exact_mod_cast (show 2 ≤ armCount by omega)
  have hcountThreeReal : (3 : ℝ) ≤ armCount := by exact_mod_cast hcountThree
  have hradicand : (3 : ℝ) ^ 2 <
      6 * (armCount : ℝ) * Real.log (armCount : ℝ) := by
    nlinarith
  have hsqrt : (3 : ℝ) <
      Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) :=
    Real.lt_sqrt_of_sq_lt hradicand
  have hcutoffLt : sourceOptMaximizeCutoff armCount < armCount := by omega
  have hrounded := sourceOptMaximizeCutoff_sqrt_lt_of_lt_armCount armCount hcutoffLt
  have hthreeLt : (3 : ℝ) < sourceOptMaximizeCutoff armCount := hsqrt.trans hrounded
  exact_mod_cast hthreeLt

/-- The preceding rounded-cutoff fact gives the population lower bound needed
to charge the inverse-square contraction tail to one eighth of confidence. -/
theorem nine_le_armCount_of_two_mul_sourceOptMaximizeCutoff_lt
    (armCount : ℕ)
    (hlarge : 2 * sourceOptMaximizeCutoff armCount < armCount) :
    9 ≤ armCount := by
  have hcutoffFour := four_le_sourceOptMaximizeCutoff_of_two_mul_lt armCount hlarge
  omega

/--
Whenever the rescaled Algorithm-3 branch can reach Prune, capping has not
altered the rounded source cutoff.
-/
theorem sourceOptMaximizeCutoff_eq_raw_of_six_ratio_lt
    (armCount : ℕ) (delta : ℝ) (hcount : 0 < armCount) (hdeltaLeOne : delta ≤ 1)
    (hbranch : 6 * (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) < delta) :
    sourceOptMaximizeCutoff armCount =
      ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 := by
  have hcountReal : 0 < (armCount : ℝ) := by exact_mod_cast hcount
  have hbranch' : 6 *
      ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) < delta := by
    calc
      6 * ((sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ)) =
          6 * (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) := by ring
      _ < delta := hbranch
  have hratio : (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) < 1 := by
    nlinarith
  have hcutoffLt : sourceOptMaximizeCutoff armCount < armCount := by
    have hcutoffLtReal : (sourceOptMaximizeCutoff armCount : ℝ) < (armCount : ℝ) :=
      (div_lt_one hcountReal).mp hratio
    exact_mod_cast hcutoffLtReal
  let raw : ℕ := ⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1
  have hrawLe : raw ≤ armCount := by
    by_contra hrawLe
    have hrawGt : armCount < raw := Nat.lt_of_not_ge hrawLe
    have hcutoffEq : sourceOptMaximizeCutoff armCount = armCount := by
      unfold sourceOptMaximizeCutoff
      change min armCount raw = armCount
      exact Nat.min_eq_left (Nat.le_of_lt hrawGt)
    rw [hcutoffEq] at hcutoffLt
    exact (Nat.lt_irrefl armCount hcutoffLt)
  unfold sourceOptMaximizeCutoff
  change min armCount raw = raw
  exact Nat.min_eq_right hrawLe

/--
On the non-base rescaled branch, the integral source cutoff strictly exceeds
the displayed square-root threshold required by the multi-round Prune proof.
-/
theorem sourceOptMaximizeCutoff_sqrt_lt_of_six_ratio_lt
    (armCount : ℕ) (delta : ℝ) (hcount : 0 < armCount) (hdeltaLeOne : delta ≤ 1)
    (hbranch : 6 * (sourceOptMaximizeCutoff armCount : ℝ) / (armCount : ℝ) < delta) :
    Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) <
      (sourceOptMaximizeCutoff armCount : ℝ) := by
  have hraw := sourceOptMaximizeCutoff_eq_raw_of_six_ratio_lt armCount delta hcount
    hdeltaLeOne hbranch
  rw [hraw]
  calc
    Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ)) ≤
        (⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ : ℝ) :=
      Nat.le_ceil _
    _ < ((⌈Real.sqrt (6 * (armCount : ℝ) * Real.log (armCount : ℝ))⌉₊ + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.lt_succ_self _

/--
The source integer base-two horizon is at most the corresponding real natural
logarithm divided by `log 2`.  This is the bridge from Algorithm 2's loop cap
to the logarithmic resource display.
-/
theorem natLogTwo_real_mul_log_two_le_log (armCount : ℕ) :
    (Nat.log 2 armCount : ℝ) * Real.log 2 ≤ Real.log (armCount : ℝ) := by
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hsource : (Nat.log 2 armCount : ℝ) ≤
      Real.log (armCount : ℝ) / Real.log 2 := by
    simpa only [Nat.log2_eq_log_two, Real.logb] using Real.log2_le_logb armCount
  exact (le_div_iff₀ hlogTwo).mp hsource

end FalahatgarEtAl2017MaxingRanking
