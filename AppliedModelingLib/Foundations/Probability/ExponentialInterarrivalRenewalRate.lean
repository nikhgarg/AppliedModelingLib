import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalRenewalCount
import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalStrongLaw
import Mathlib.Tactic

/-!
# Inverse strong law for the canonical exponential renewal count

This module converts the arrival-epoch strong law for the canonical
exponential-interarrival construction into its corresponding count-rate law.
It is an input-process fact only: no queue, workload, or stability conclusion
is made here.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped Topology ProbabilityTheory Function

noncomputable section

/--
The pathwise inverse-renewal theorem for the canonical count.  It is stated
with the exponential-rate parameter directly: arrival epochs converging to
mean interarrival time `1 / rate` imply count rate `rate`.
-/
theorem tendsto_canonicalRenewalCount_div_atTop_of_arrivalTime_div_nat_succ
    {rate : Real} (hrate : 0 < rate) (omega : Nat -> Real)
    (harrival : Tendsto
      (fun n : Nat => arrivalTime n omega / ((n + 1 : Nat) : Real))
      atTop (nhds (1 / rate)))
    (hdiv : Tendsto (fun n : Nat => arrivalTime n omega) atTop atTop)
    (hmono : Monotone (fun n : Nat => arrivalTime n omega)) :
    Tendsto
      (fun t : Real => (canonicalRenewalCount t omega : Real) / t)
      atTop (nhds rate) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  let delta : Real := min (eps / 4) (rate / 4)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by linarith) (by linarith)
  have hdelta_eps : delta <= eps / 4 := by
    exact min_le_left _ _
  have hdelta_rate : delta <= rate / 4 := by
    exact min_le_right _ _
  have hrate_sub_delta : 0 < rate - delta := by
    linarith
  have hrate_add_delta : 0 < rate + delta := by
    linarith
  have hlowerLimit : 1 / (rate + delta) < 1 / rate := by
    exact one_div_lt_one_div_of_lt hrate (by linarith)
  have hupperLimit : 1 / rate < 1 / (rate - delta) := by
    have h := one_div_lt_one_div_of_lt hrate_sub_delta (by linarith : rate - delta < rate)
    simpa using h
  have hseqLower : ∀ᶠ n : Nat in atTop,
      1 / (rate + delta) <
        arrivalTime n omega / ((n + 1 : Nat) : Real) :=
    Filter.Tendsto.eventually_const_lt hlowerLimit harrival
  have hseqUpper : ∀ᶠ n : Nat in atTop,
      arrivalTime n omega / ((n + 1 : Nat) : Real) <
        1 / (rate - delta) :=
    Filter.Tendsto.eventually_lt_const hupperLimit harrival
  have hseq : ∀ᶠ n : Nat in atTop,
      1 / (rate + delta) <
        arrivalTime n omega / ((n + 1 : Nat) : Real) /\
      arrivalTime n omega / ((n + 1 : Nat) : Real) <
        1 / (rate - delta) :=
    hseqLower.and hseqUpper
  rcases (eventually_atTop.1 hseq) with ⟨N, hN⟩
  refine ⟨max (arrivalTime N omega) (2 / delta), ?_⟩
  intro t ht
  have ht_arrival : arrivalTime N omega <= t := le_trans (le_max_left _ _) ht
  have ht_large : 2 / delta <= t := le_trans (le_max_right _ _) ht
  have ht_pos : 0 < t := by
    have : 0 < 2 / delta := by positivity
    exact lt_of_lt_of_le this ht_large
  let k := canonicalRenewalCount t omega
  have hk_gt_N : N < k :=
    (lt_canonicalRenewalCount_iff_arrivalTime_le_of_tendsto omega hdiv hmono t N).mpr
      ht_arrival
  have hk_pos : 0 < k := lt_of_le_of_lt (Nat.zero_le N) hk_gt_N
  have hkm1_ge_N : N <= k - 1 := by omega
  have hk_ge_N : N <= k := Nat.le_of_lt hk_gt_N
  have hseqPrev := hN (k - 1) hkm1_ge_N
  have hseqNext := hN k hk_ge_N
  have hprev_le_t : arrivalTime (k - 1) omega <= t := by
    have hlt : k - 1 < k := by omega
    exact arrivalTime_le_of_lt_canonicalRenewalCount t omega
      (exists_arrivalTime_gt_of_tendsto_atTop omega hdiv t) hlt
  have ht_lt_next : t < arrivalTime k omega :=
    lt_arrivalTime_canonicalRenewalCount t omega
      (exists_arrivalTime_gt_of_tendsto_atTop omega hdiv t)
  have hk_real_pos : 0 < (k : Real) := by exact_mod_cast hk_pos
  have hk_succ_real_pos : 0 < ((k + 1 : Nat) : Real) := by positivity
  have hupper_count : (k : Real) / t < rate + eps := by
    have hratio := hseqPrev.1
    have hdenom : ((k - 1 + 1 : Nat) : Real) = (k : Real) := by
      norm_cast
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hk_pos)
    rw [hdenom] at hratio
    have harrival_lower : (k : Real) / (rate + delta) < arrivalTime (k - 1) omega := by
      apply (div_lt_iff₀ hrate_add_delta).mpr
      have hcross := (div_lt_div_iff₀ hrate_add_delta hk_real_pos).mp hratio
      nlinarith
    have hk_lt : (k : Real) < (rate + delta) * t := by
      have := harrival_lower.trans_le hprev_le_t
      rw [div_lt_iff₀ hrate_add_delta] at this
      nlinarith
    have : (k : Real) / t < rate + delta := (div_lt_iff₀ ht_pos).mpr (by nlinarith)
    linarith
  have hlower_count : rate - eps < (k : Real) / t := by
    have hratio := hseqNext.2
    have harrival_upper : arrivalTime k omega <
        ((k + 1 : Nat) : Real) / (rate - delta) := by
      apply (lt_div_iff₀ hrate_sub_delta).mpr
      have hcross := (div_lt_div_iff₀ hk_succ_real_pos hrate_sub_delta).mp hratio
      nlinarith
    have ht_scaled : (rate - delta) * t < (k + 1 : Nat) := by
      have := ht_lt_next.trans harrival_upper
      rw [lt_div_iff₀ hrate_sub_delta] at this
      simpa [mul_comm] using this
    have hdelta_t_gt_one : 1 < delta * t := by
      have htwo : 2 <= delta * t := by
        have h := (div_le_iff₀ hdelta).mp ht_large
        simpa [mul_comm] using h
      linarith
    have htarget_scaled : (rate - eps) * t < (k : Real) := by
      norm_num at ht_scaled ⊢
      have heps_delta : 2 * delta <= eps := by linarith
      nlinarith
    exact (lt_div_iff₀ ht_pos).mpr (by nlinarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/--
At positive exponential rate, the canonical renewal count has the expected
almost-sure long-run rate.  This is a statement about the actual canonical
input process, not a queueing stability assertion.
-/
theorem ae_tendsto_canonicalRenewalCount_div_atTop
    {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ omega ∂exponentialInterarrivalMeasure rate,
      Tendsto
        (fun t : Real => (canonicalRenewalCount t omega : Real) / t)
        atTop (nhds rate) := by
  filter_upwards [ae_tendsto_arrivalTime_div_nat_succ hrate,
    ae_arrivalTime_tendsto_atTop hrate, ae_arrivalTime_monotone hrate]
    with omega harrival hdiv hmono
  exact tendsto_canonicalRenewalCount_div_atTop_of_arrivalTime_div_nat_succ
    hrate omega harrival hdiv hmono

end

end AppliedModelingLib.Probability.PoissonProcess
