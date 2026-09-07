import PG24NoisyMatchingMarkets.MainTheorems
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic

/-!
# PG24 Theorem 3 logarithmic maximum bound

This module isolates the analytic dyadic argument used in
`source_tex/proof-attenuating.tex:279-309`.  The probabilistic comparison of
an iid maximum over `2 n` draws with the maximum of two iid `n`-draw blocks is
kept as a separate, explicit obligation below; the results here do not assume
any conclusion about cutoffs or matching probabilities.
-/

namespace PG24NoisyMatchingMarkets

noncomputable section

open Filter Topology MeasureTheory
open scoped BigOperators ProbabilityTheory

/--
If a monotone real sequence has arbitrarily small increments when its index
is doubled, then its increments on the dyadic subsequence converge to zero.
This is the purely analytic part of the source proof's first display after
Lemma `log-bound`.
-/
theorem theorem3_dyadicIncrement_tendsto_zero
    {f : ℕ → ℝ}
    (hmono : Monotone f)
    (hdoubling : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ ε) :
    Tendsto (fun k : ℕ => f (2 ^ (k + 1)) - f (2 ^ k)) atTop (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards with k
    exact lt_of_lt_of_le ha (sub_nonneg.mpr
      (hmono (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ k))))
  · intro a ha
    have hhalf_pos : 0 < a / 2 := by linarith
    have hlarge : ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ a / 2 :=
      hdoubling (a / 2) hhalf_pos
    have hpows : Tendsto (fun k : ℕ => 2 ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    filter_upwards [hpows.eventually hlarge] with k hk
    have hrewrite : 2 * 2 ^ k = 2 ^ (k + 1) := by
      rw [show k + 1 = k.succ by omega, Nat.pow_succ]
      omega
    rw [hrewrite] at hk
    linarith

/--
The telescoping/Cesaro form of the dyadic argument.  It turns vanishing
dyadic increments into sublinear growth of the dyadic subsequence.
-/
theorem theorem3_dyadicGrowth_div_index_tendsto_zero
    {f : ℕ → ℝ}
    (hmono : Monotone f)
    (hdoubling : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ ε) :
    Tendsto
      (fun k : ℕ => (f (2 ^ k) - f 1) / (k : ℝ))
      atTop (nhds 0) := by
  let g : ℕ → ℝ := fun k => f (2 ^ k)
  have hinc : Tendsto (fun k : ℕ => g (k + 1) - g k) atTop (nhds 0) := by
    simpa [g] using theorem3_dyadicIncrement_tendsto_zero hmono hdoubling
  have hcesaro := hinc.cesaro
  have htelescoping :
      (fun k : ℕ => ((k : ℝ)⁻¹) * ∑ i ∈ Finset.range k,
        (g (i + 1) - g i)) =
        fun k : ℕ => (g k - g 0) / (k : ℝ) := by
    funext k
    rw [Finset.sum_range_sub]
    simp only [div_eq_mul_inv, mul_comm]
  rw [htelescoping] at hcesaro
  simpa [g] using hcesaro

/--
The dyadic estimate controls every index, not only powers of two.  The proof
uses `Nat.log 2 n` to place `n` between two consecutive dyadic blocks, and
then applies monotonicity.  This is the formal analytic content of
`E[X^(n)] = o(log n)` once the iid maximum comparison supplies
`hdoubling`.
-/
theorem theorem3_monotone_doubling_sub_div_log_tendsto_zero
    {f : ℕ → ℝ}
    (hmono : Monotone f)
    (hdoubling : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ ε) :
    Tendsto
      (fun n : ℕ => (f n - f 1) / Real.log (n : ℝ))
      atTop (nhds 0) := by
  have hdyadic := theorem3_dyadicGrowth_div_index_tendsto_zero hmono hdoubling
  have hlogNat : Tendsto (fun n : ℕ => Nat.log 2 n) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop (2 ^ K)] with n hn
    exact Nat.le_log_of_pow_le (by norm_num) hn
  have hlogNatSucc : Tendsto (fun n : ℕ => Nat.log 2 n + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro K
    filter_upwards [hlogNat.eventually_ge_atTop K] with n hn
    omega
  have hdyadicAtLog :
      Tendsto
        (fun n : ℕ =>
          (f (2 ^ (Nat.log 2 n + 1)) - f 1) /
            ((Nat.log 2 n + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    simpa [Function.comp_def] using hdyadic.comp hlogNatSucc
  let L : ℝ := Real.log 2
  have hL_pos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by norm_num)
  have hupper_tendsto :
      Tendsto
        (fun n : ℕ => (2 / L) *
          ((f (2 ^ (Nat.log 2 n + 1)) - f 1) /
            ((Nat.log 2 n + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa using (hdyadicAtLog.const_mul (2 / L))
  refine squeeze_zero' ?_ ?_ hupper_tendsto
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hnum_nonneg : 0 ≤ f n - f 1 :=
      sub_nonneg.mpr (hmono (by omega))
    have hdenom_nonneg : 0 ≤ Real.log (n : ℝ) := by
      apply Real.log_nonneg
      have hone_le_n : 1 ≤ n := by omega
      exact_mod_cast hone_le_n
    exact div_nonneg hnum_nonneg hdenom_nonneg
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let k : ℕ := Nat.log 2 n
    have hn_pos : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have hk_pos : 0 < k := by
      dsimp [k]
      have htwo_le_n : 2 ^ 1 ≤ n := by simpa using hn
      exact lt_of_lt_of_le (by norm_num : 0 < 1)
        (Nat.le_log_of_pow_le (by norm_num) htwo_le_n)
    have hk_real_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos
    have hk_succ_real_pos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
    have hF_nonneg : 0 ≤ f n - f 1 :=
      sub_nonneg.mpr (hmono (by omega))
    have hF_big_nonneg : 0 ≤ f (2 ^ (k + 1)) - f 1 :=
      sub_nonneg.mpr (hmono (by
        have : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num)
        exact this))
    have hpow_le : 2 ^ k ≤ n := by
      exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hn_pos)
    have hlt_pow : n < 2 ^ (k + 1) := by
      apply Nat.lt_pow_of_log_lt (by norm_num)
      change Nat.log 2 n < Nat.log 2 n + 1
      omega
    have hF_le_big : f n - f 1 ≤ f (2 ^ (k + 1)) - f 1 := by
      exact sub_le_sub_right (hmono hlt_pow.le) _
    have hlog_lower : (k : ℝ) * L ≤ Real.log (n : ℝ) := by
      calc
        (k : ℝ) * L = Real.log (((2 ^ k : ℕ) : ℝ)) := by
          dsimp [L]
          rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        _ ≤ Real.log (n : ℝ) := by
          apply Real.log_le_log
          · positivity
          · exact_mod_cast hpow_le
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      exact Real.log_pos (by exact_mod_cast hn)
    have hkL_pos : 0 < (k : ℝ) * L := mul_pos hk_real_pos hL_pos
    have hfirst :
        (f n - f 1) / Real.log (n : ℝ) ≤
          (f (2 ^ (k + 1)) - f 1) / ((k : ℝ) * L) := by
      exact div_le_div₀ hF_big_nonneg hF_le_big hkL_pos hlog_lower
    have hratio_scalar : (1 : ℝ) / (k : ℝ) ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
      rw [div_le_div_iff₀ hk_real_pos hk_succ_real_pos]
      norm_num
      exact_mod_cast (show k + 1 ≤ 2 * k by omega)
    have hratio_numer :
        (f (2 ^ (k + 1)) - f 1) / (k : ℝ) ≤
          2 * ((f (2 ^ (k + 1)) - f 1) /
            ((k + 1 : ℕ) : ℝ)) := by
      calc
        (f (2 ^ (k + 1)) - f 1) / (k : ℝ) =
            (f (2 ^ (k + 1)) - f 1) * ((1 : ℝ) / (k : ℝ)) := by ring
        _ ≤ (f (2 ^ (k + 1)) - f 1) *
            (2 / ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hratio_scalar hF_big_nonneg
        _ = 2 * ((f (2 ^ (k + 1)) - f 1) /
            ((k + 1 : ℕ) : ℝ)) := by ring
    have hsecond :
        (f (2 ^ (k + 1)) - f 1) / ((k : ℝ) * L) ≤
          (2 / L) * ((f (2 ^ (k + 1)) - f 1) /
            ((k + 1 : ℕ) : ℝ)) := by
      calc
        (f (2 ^ (k + 1)) - f 1) / ((k : ℝ) * L) =
            ((f (2 ^ (k + 1)) - f 1) / (k : ℝ)) / L := by
              field_simp
        _ ≤ (2 * ((f (2 ^ (k + 1)) - f 1) /
              ((k + 1 : ℕ) : ℝ))) / L :=
              div_le_div_of_nonneg_right hratio_numer hL_pos.le
        _ = (2 / L) * ((f (2 ^ (k + 1)) - f 1) /
              ((k + 1 : ℕ) : ℝ)) := by ring
    calc
      (f n - f 1) / Real.log (n : ℝ) ≤
          (f (2 ^ (k + 1)) - f 1) / ((k : ℝ) * L) := hfirst
      _ ≤ (2 / L) * ((f (2 ^ (k + 1)) - f 1) /
          ((k + 1 : ℕ) : ℝ)) := hsecond
      _ = (2 / L) * ((f (2 ^ (Nat.log 2 n + 1)) - f 1) /
          ((Nat.log 2 n + 1 : ℕ) : ℝ)) := by simp [k]

/--
Adding back the fixed one-sample expectation preserves the logarithmic little
`o` conclusion.  This is the exact abstract conclusion used by the source's
large-gap branch.
-/
theorem theorem3_monotone_doubling_div_log_tendsto_zero
    {f : ℕ → ℝ}
    (hmono : Monotone f)
    (hdoubling : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ ε) :
    Tendsto
      (fun n : ℕ => f n / Real.log (n : ℝ))
      atTop (nhds 0) := by
  have hsub := theorem3_monotone_doubling_sub_div_log_tendsto_zero hmono hdoubling
  have hconst := AppliedModelingLib.Math.tendsto_const_div_log_nat_nhds_zero (f 1)
  have hadd := hsub.add hconst
  have heq :
      (fun n : ℕ =>
        (f n - f 1) / Real.log (n : ℝ) + f 1 / Real.log (n : ℝ)) =ᶠ[atTop]
        fun n : ℕ => f n / Real.log (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hlt : 1 < n := by omega
    have hlog_pos : 0 < Real.log (n : ℝ) := by
      apply Real.log_pos
      exact_mod_cast hlt
    field_simp [ne_of_gt hlog_pos]
    ring
  simpa using hadd.congr' heq

/--
The logarithmic dyadic estimate only needs monotonicity after a finite
index.  This is the form appropriate for the source beta-max premise, whose
finite-second-moment guarantee is eventual rather than global.  The proof
shifts the sequence past that index, applies the global analytic lemma to the
shift, and sandwiches the original sequence between the shifted base value
and shifted sequence.
-/
theorem theorem3_eventuallyMonotone_doubling_div_log_tendsto_zero
    {f : ℕ → ℝ}
    (hmono : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, n ≤ m → f n ≤ f m)
    (hdoubling : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, f (2 * n) - f n ≤ ε) :
    Tendsto
      (fun n : ℕ => f n / Real.log (n : ℝ))
      atTop (nhds 0) := by
  rcases Filter.eventually_atTop.1 hmono with ⟨N, hN⟩
  let g : ℕ → ℝ := fun n => f (n + N)
  have hmono_g : Monotone g := by
    intro n m hnm
    dsimp [g]
    exact hN (n + N) (by omega) (m + N) (by omega)
  have hdoubling_g : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop, g (2 * n) - g n ≤ ε := by
    intro ε hε
    rcases Filter.eventually_atTop.1 (hdoubling ε hε) with ⟨M, hM⟩
    filter_upwards [eventually_ge_atTop M] with n hn
    dsimp [g]
    calc
      f (2 * n + N) - f (n + N) ≤
          f (2 * (n + N)) - f (n + N) := by
        apply sub_le_sub_right
        exact hN (2 * n + N) (by omega) (2 * (n + N)) (by omega)
      _ ≤ ε := hM (n + N) (by omega)
  have hg := theorem3_monotone_doubling_div_log_tendsto_zero
    hmono_g hdoubling_g
  have hbase := AppliedModelingLib.Math.tendsto_const_div_log_nat_nhds_zero (f N)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hbase hg ?_ ?_
  · filter_upwards [eventually_ge_atTop (max N 2)] with n hn
    have hN_le_n : N ≤ n := le_trans (le_max_left _ _) hn
    have htwo_le_n : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact (Real.log_pos (by exact_mod_cast htwo_le_n)).le
    exact div_le_div_of_nonneg_right
      (hN N (le_refl _) n hN_le_n) hlog_nonneg
  · filter_upwards [eventually_ge_atTop (max N 2)] with n hn
    have hN_le_n : N ≤ n := le_trans (le_max_left _ _) hn
    have htwo_le_n : 2 ≤ n := le_trans (le_max_right _ _) hn
    have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
      exact (Real.log_pos (by exact_mod_cast htwo_le_n)).le
    apply div_le_div_of_nonneg_right _ hlog_nonneg
    simpa [g] using hN n hN_le_n (n + N) (by omega)

/--
The `L¹`--`L²` step used in the source proof of Lemma `log-bound`.  Under a
probability measure, the mean absolute deviation of an `L²` variable is at
most the square root of its variance.
-/
theorem theorem3_integral_abs_centered_le_sqrt_variance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (X : Omega -> ℝ) (hX : MemLp X 2 mu) :
    integral mu (fun w => |X w - integral mu X|) <=
      Real.sqrt (ProbabilityTheory.variance X mu) := by
  let mean : ℝ := integral mu X
  let centered : Omega -> ℝ := fun w => X w - mean
  have hcentered : MemLp centered 2 mu := by
    simpa [centered] using hX.sub (memLp_const mean)
  have habs : MemLp (fun w => |centered w|) 2 mu := by
    simpa only [Real.norm_eq_abs] using hcentered.norm
  have hholder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := mu) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by constructor <;> norm_num : (2 : ℝ).HolderConjugate 2)
    (f := fun _ : Omega => (1 : ℝ)) (g := fun w => |centered w|)
    (Filter.Eventually.of_forall fun _ => zero_le_one)
    (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    (by simpa using (memLp_const (μ := mu) (p := (2 : ENNReal)) (1 : ℝ)))
    (by simpa using habs)
  have hone : integral mu (fun _ : Omega => ((1 : ℝ) ^ (2 : ℝ))) = 1 := by
    rw [show (fun _ : Omega => ((1 : ℝ) ^ (2 : ℝ))) = fun _ => (1 : ℝ) by
      ext
      norm_num,
      MeasureTheory.integral_const, MeasureTheory.probReal_univ]
    norm_num
  have hvariance :
      integral mu (fun w => |centered w| ^ (2 : ℝ)) =
        ProbabilityTheory.variance X mu := by
    rw [show (fun w : Omega => |centered w| ^ (2 : ℝ)) =
        fun w => (centered w) ^ 2 by
      ext w
      rw [Real.rpow_two, sq_abs],
      ProbabilityTheory.variance_eq_integral hX.aemeasurable]
  have hleft : integral mu (fun w => (1 : ℝ) * |centered w|) =
      integral mu (fun w => |centered w|) := by simp
  rw [hleft, hone, hvariance, Real.one_rpow, one_mul] at hholder
  simpa [centered, mean, Real.sqrt_eq_rpow] using hholder

/--
Pointwise maximum comparison integrated over a finite measure.  This is the
first inequality in the source proof after introducing the two iid block
maxima; it does not use independence.
-/
theorem theorem3_integral_max_le_integral_left_add_integral_abs_sub
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (W1 W2 : Omega -> ℝ) (hW1 : MemLp W1 2 mu) (hW2 : MemLp W2 2 mu) :
    integral mu (fun w => max (W1 w) (W2 w)) <=
      integral mu W1 + integral mu (fun w => |W2 w - W1 w|) := by
  have hW1_int : Integrable W1 mu := hW1.integrable (by norm_num)
  have hW2_int : Integrable W2 mu := hW2.integrable (by norm_num)
  have hdiff_int : Integrable (fun w => |W2 w - W1 w|) mu := by
    simpa only [Real.norm_eq_abs] using (hW2_int.sub hW1_int).norm
  have hmax_int : Integrable (fun w => max (W1 w) (W2 w)) mu := by
    apply Integrable.mono' (by
      simpa only [Pi.add_apply] using hW1_int.abs.add hW2_int.abs)
    · exact (hW1.aemeasurable.max hW2.aemeasurable).aestronglyMeasurable
    · filter_upwards with w
      have habs : |max (W1 w) (W2 w)| <= |W1 w| + |W2 w| := by
        apply abs_le.mpr
        constructor
        · calc
            -(|W1 w| + |W2 w|) <= W1 w := by
              linarith [neg_abs_le (W1 w), abs_nonneg (W2 w)]
            _ <= max (W1 w) (W2 w) := le_max_left _ _
        · apply max_le
          · linarith [le_abs_self (W1 w), abs_nonneg (W2 w)]
          · linarith [le_abs_self (W2 w), abs_nonneg (W1 w)]
      simpa only [Real.norm_eq_abs] using habs
  calc
    integral mu (fun w => max (W1 w) (W2 w)) <=
        integral mu (fun w => W1 w + |W2 w - W1 w|) := by
      apply MeasureTheory.integral_mono_ae hmax_int (hW1_int.add hdiff_int)
      filter_upwards with w
      change max (W1 w) (W2 w) <= W1 w + |W2 w - W1 w|
      apply max_le
      · exact le_add_of_nonneg_right (abs_nonneg _)
      · linarith [le_abs_self (W2 w - W1 w)]
    _ = integral mu W1 + integral mu (fun w => |W2 w - W1 w|) :=
      MeasureTheory.integral_add hW1_int hdiff_int

/--
The checked `L¹`--`L²` maximum inequality.  If two block maxima have the
same mean and variance, their joint maximum raises expectation by at most
twice the common standard deviation.  Independence is not needed for this
inequality itself; it is needed separately to identify the joint maximum with
the iid maximum over the union of the two blocks.
-/
theorem theorem3_integral_max_le_mean_add_two_sqrt_variance
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (W1 W2 : Omega -> ℝ) (hW1 : MemLp W1 2 mu) (hW2 : MemLp W2 2 mu)
    (hmean : integral mu W2 = integral mu W1)
    (hvariance : ProbabilityTheory.variance W2 mu = ProbabilityTheory.variance W1 mu) :
    integral mu (fun w => max (W1 w) (W2 w)) <=
      integral mu W1 + 2 * Real.sqrt (ProbabilityTheory.variance W1 mu) := by
  have hW1_int : Integrable W1 mu := hW1.integrable (by norm_num)
  have hW2_int : Integrable W2 mu := hW2.integrable (by norm_num)
  have hdiff_int : Integrable (fun w => |W2 w - W1 w|) mu := by
    simpa only [Real.norm_eq_abs] using (hW2_int.sub hW1_int).norm
  have hcenter2_int :
      Integrable (fun w => |W2 w - integral mu W1|) mu := by
    rw [<- hmean]
    simpa only [Real.norm_eq_abs] using (hW2_int.sub (integrable_const _)).norm
  have hcenter1_int :
      Integrable (fun w => |W1 w - integral mu W1|) mu := by
    simpa only [Real.norm_eq_abs] using (hW1_int.sub (integrable_const _)).norm
  have hdiff_le :
      integral mu (fun w => |W2 w - W1 w|) <=
        integral mu (fun w => |W2 w - integral mu W1|) +
          integral mu (fun w => |W1 w - integral mu W1|) := by
    calc
      integral mu (fun w => |W2 w - W1 w|) <=
          integral mu (fun w => |W2 w - integral mu W1| +
            |W1 w - integral mu W1|) := by
        apply MeasureTheory.integral_mono_ae hdiff_int (hcenter2_int.add hcenter1_int)
        filter_upwards with w
        simpa only [Pi.add_apply, abs_sub_comm] using
          (abs_sub_le (W2 w) (integral mu W1) (W1 w))
      _ = integral mu (fun w => |W2 w - integral mu W1|) +
          integral mu (fun w => |W1 w - integral mu W1|) :=
        MeasureTheory.integral_add hcenter2_int hcenter1_int
  have hcenter2_le :
      integral mu (fun w => |W2 w - integral mu W1|) <=
        Real.sqrt (ProbabilityTheory.variance W1 mu) := by
    rw [<- hmean]
    calc
      integral mu (fun w => |W2 w - integral mu W2|) <=
          Real.sqrt (ProbabilityTheory.variance W2 mu) :=
        theorem3_integral_abs_centered_le_sqrt_variance mu W2 hW2
      _ = Real.sqrt (ProbabilityTheory.variance W1 mu) := by rw [hvariance]
  have hcenter1_le :
      integral mu (fun w => |W1 w - integral mu W1|) <=
        Real.sqrt (ProbabilityTheory.variance W1 mu) :=
    theorem3_integral_abs_centered_le_sqrt_variance mu W1 hW1
  calc
    integral mu (fun w => max (W1 w) (W2 w)) <=
        integral mu W1 + integral mu (fun w => |W2 w - W1 w|) :=
      theorem3_integral_max_le_integral_left_add_integral_abs_sub mu W1 W2 hW1 hW2
    _ <= integral mu W1 +
          (integral mu (fun w => |W2 w - integral mu W1|) +
            integral mu (fun w => |W1 w - integral mu W1|)) :=
      add_le_add_right hdiff_le _
    _ <= integral mu W1 +
          (Real.sqrt (ProbabilityTheory.variance W1 mu) +
            Real.sqrt (ProbabilityTheory.variance W1 mu)) := by
      gcongr
    _ = integral mu W1 + 2 * Real.sqrt (ProbabilityTheory.variance W1 mu) := by ring

/--
One concrete iid-block witness yields the source's doubling increment bound.
The caller must identify `W1` and `W2` as the two iid `n`-sample maxima and
their joint maximum as the `2n`-sample maximum.  All subsequent arithmetic,
including the variance-envelope substitution, is proved here.
-/
theorem theorem3_doubling_increment_le_of_block_maximum_witness
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {expectedMax maxVariance : ℕ -> ℝ} (n : ℕ)
    (W1 W2 : Omega -> ℝ) (hW1 : MemLp W1 2 mu) (hW2 : MemLp W2 2 mu)
    (hsame_mean : integral mu W2 = integral mu W1)
    (hsame_variance : ProbabilityTheory.variance W2 mu = ProbabilityTheory.variance W1 mu)
    (hleft : integral mu W1 = expectedMax n)
    (hjoint : integral mu (fun w => max (W1 w) (W2 w)) = expectedMax (2 * n))
    (hvariance_bound : ProbabilityTheory.variance W1 mu <= maxVariance n) :
    expectedMax (2 * n) - expectedMax n <=
      2 * Real.sqrt (maxVariance n) := by
  have hmax := theorem3_integral_max_le_mean_add_two_sqrt_variance
    mu W1 W2 hW1 hW2 hsame_mean hsame_variance
  have hvar_sqrt :
      Real.sqrt (ProbabilityTheory.variance W1 mu) <= Real.sqrt (maxVariance n) :=
    Real.sqrt_le_sqrt hvariance_bound
  have hmax_bound : expectedMax (2 * n) <=
      expectedMax n + 2 * Real.sqrt (maxVariance n) := by
    calc
      expectedMax (2 * n) = integral mu (fun w => max (W1 w) (W2 w)) := hjoint.symm
      _ <= integral mu W1 + 2 * Real.sqrt (ProbabilityTheory.variance W1 mu) := hmax
      _ <= integral mu W1 + 2 * Real.sqrt (maxVariance n) := by
        gcongr
      _ = expectedMax n + 2 * Real.sqrt (maxVariance n) := by rw [hleft]
  linarith

/--
The off-by-one-safe version of the iid two-block comparison.  When two
`n + 1` blocks are coupled, their joint maximum has `2 * n + 2` coordinates,
whereas the source sequence at index `2 * n` has `2 * n + 1`.  A projection
therefore supplies only an upper bound by the block maximum, which is all the
dyadic increment estimate needs.
-/
theorem theorem3_doubling_increment_le_of_block_maximum_upper_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {expectedMax maxVariance : ℕ -> ℝ} (n : ℕ)
    (W1 W2 : Omega -> ℝ) (hW1 : MemLp W1 2 mu) (hW2 : MemLp W2 2 mu)
    (hsame_mean : integral mu W2 = integral mu W1)
    (hsame_variance : ProbabilityTheory.variance W2 mu = ProbabilityTheory.variance W1 mu)
    (hleft : integral mu W1 = expectedMax n)
    (hjoint_upper : expectedMax (2 * n) ≤ integral mu (fun w => max (W1 w) (W2 w)))
    (hvariance_bound : ProbabilityTheory.variance W1 mu <= maxVariance n) :
    expectedMax (2 * n) - expectedMax n <=
      2 * Real.sqrt (maxVariance n) := by
  have hmax := theorem3_integral_max_le_mean_add_two_sqrt_variance
    mu W1 W2 hW1 hW2 hsame_mean hsame_variance
  have hvar_sqrt :
      Real.sqrt (ProbabilityTheory.variance W1 mu) <= Real.sqrt (maxVariance n) :=
    Real.sqrt_le_sqrt hvariance_bound
  have hmax_bound : expectedMax (2 * n) <=
      expectedMax n + 2 * Real.sqrt (maxVariance n) := by
    calc
      expectedMax (2 * n) ≤ integral mu (fun w => max (W1 w) (W2 w)) :=
        hjoint_upper
      _ ≤ integral mu W1 + 2 * Real.sqrt (ProbabilityTheory.variance W1 mu) := hmax
      _ ≤ integral mu W1 + 2 * Real.sqrt (maxVariance n) := by
        gcongr
      _ = expectedMax n + 2 * Real.sqrt (maxVariance n) := by rw [hleft]
  linarith

/--
The concrete probabilistic bridge needed by the source's `log-bound` proof.
`expectedMax` is the expectation of the iid maximum at a given sample size,
and `maxVariance` is an upper bound on its variance.  The second field is the
two independent-block comparison plus the `L¹`--`L²` estimate; it is stated
as a numerical inequality rather than as the desired logarithmic conclusion.
-/
structure Theorem3MaximumDyadicVarianceBridge
    (expectedMax maxVariance : ℕ → ℝ) : Prop where
  monotone_expectedMax : Monotone expectedMax
  doubling_increment_le :
    ∀ᶠ n : ℕ in atTop,
      expectedMax (2 * n) - expectedMax n ≤
        2 * Real.sqrt (maxVariance n)

/--
The beta-max variance rate makes the source's two-block error term vanish.
No iid coupling is used here; that coupling is recorded explicitly in
`Theorem3MaximumDyadicVarianceBridge`.
-/
theorem theorem3_two_mul_sqrt_variance_tendsto_zero_of_beta
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n) :
    Tendsto (fun n : ℕ => 2 * Real.sqrt (maxVariance n)) atTop (nhds 0) := by
  have hvariance_zero := hbeta.tendsto_zero hvariance_nonneg
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (maxVariance n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hvariance_zero)
  simpa using hsqrt.const_mul 2

/--
Source-facing form of the preceding variance decay lemma.  An eventual bound
by the actual variance of the iid top order statistic supplies the needed
nonnegativity of the named variance envelope automatically.
-/
theorem theorem3_two_mul_sqrt_variance_tendsto_zero_of_beta_variance_bound
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {maxVariance : ℕ → ℝ} {β : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n) :
    Tendsto (fun n : ℕ => 2 * Real.sqrt (maxVariance n)) atTop (nhds 0) := by
  have hvariance_zero := hbeta.tendsto_zero_of_variance_bound hvariance_bound
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (maxVariance n)) atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hvariance_zero)
  simpa using hsqrt.const_mul 2

/--
An explicit two-block maximum comparison and the beta-max variance rate imply
the source Lemma `log-bound`: expected iid maxima are little `o(log n)`.
The theorem deliberately exposes the comparison bridge so a future measure
theory proof must discharge the iid product/reindexing and `L¹`--`L²` steps.
-/
theorem theorem3_expectedMaximum_div_log_tendsto_zero_of_beta
    {expectedMax maxVariance : ℕ → ℝ} {β : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hvariance_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ maxVariance n)
    (hbridge : Theorem3MaximumDyadicVarianceBridge expectedMax maxVariance) :
    Tendsto
      (fun n : ℕ => expectedMax n / Real.log (n : ℝ))
      atTop (nhds 0) := by
  have herror_zero :=
    theorem3_two_mul_sqrt_variance_tendsto_zero_of_beta hbeta hvariance_nonneg
  apply theorem3_monotone_doubling_div_log_tendsto_zero
    hbridge.monotone_expectedMax
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (maxVariance n) < ε :=
    herror_zero (isOpen_Iio.mem_nhds hε)
  filter_upwards [hbridge.doubling_increment_le, hsmall] with n hbridge_n hsmall_n
  exact hbridge_n.trans (le_of_lt hsmall_n)

/--
The iid top-order-statistic variance premise in the PG24 source model is
sufficient for the beta-rate side of `log-bound`; only the explicit
two-block maximum comparison remains to be connected to the product measure.
-/
theorem theorem3_expectedMaximum_div_log_tendsto_zero_of_beta_variance_bound
    {sampleLaw : ∀ n : ℕ, MeasureTheory.Measure (Fin (n + 1) → ℝ)}
    {expectedMax maxVariance : ℕ → ℝ} {β : ℝ}
    (hbeta : betaMaxConcentratingVariance maxVariance β)
    (hvariance_bound :
      ∀ᶠ n : ℕ in atTop,
        ProbabilityTheory.variance
          (fun sample : Fin (n + 1) → ℝ =>
            AppliedModelingLib.Probability.upperOrderStatistic sample
              (AppliedModelingLib.Probability.topSampleRank (n := n + 1)))
          (sampleLaw n) ≤ maxVariance n)
    (hbridge : Theorem3MaximumDyadicVarianceBridge expectedMax maxVariance) :
    Tendsto
      (fun n : ℕ => expectedMax n / Real.log (n : ℝ))
      atTop (nhds 0) := by
  have herror_zero :=
    theorem3_two_mul_sqrt_variance_tendsto_zero_of_beta_variance_bound
      hbeta hvariance_bound
  apply theorem3_monotone_doubling_div_log_tendsto_zero
    hbridge.monotone_expectedMax
  intro ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop,
      2 * Real.sqrt (maxVariance n) < ε :=
    herror_zero (isOpen_Iio.mem_nhds hε)
  filter_upwards [hbridge.doubling_increment_le, hsmall] with n hbridge_n hsmall_n
  exact hbridge_n.trans (le_of_lt hsmall_n)

end

end PG24NoisyMatchingMarkets
