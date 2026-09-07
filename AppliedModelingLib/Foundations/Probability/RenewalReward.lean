import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

namespace AppliedModelingLib

open Filter
open MeasureTheory
open scoped Function ProbabilityTheory Topology

/-!
# Renewal-reward algebra

This module collects deterministic algebra used after a stochastic process has
been reduced to renewal-reward summaries.  The main use case is a driver (or
agent) who receives expected reward `W` during accepted jobs, spends expected
busy time `T`, and faces Poisson opportunities at rate `lambda`.

## Main declarations

- `renewalRewardRate`: `lambda * W / (1 + lambda * T)`.
- `averageRewardRate`: `W / T`.
- `renewalRewardRate_le_add_component_of_le_average`: adding a positive-time
  component whose average rate is at least the current renewal rate cannot
  decrease the renewal rate.
- `renewalRewardRate_remove_component_ge_of_average_le`: removing a
  positive-time component whose average rate is at most the current renewal
  rate cannot decrease the renewal rate.
- `renewalRewardRate_lt_replace_reward_same_time_of_lt`: replacing a component
  by another component with the same time contribution and strictly larger
  reward strictly increases the renewal rate.
- `AlmostSureRatioLimitCertificate`: a reusable stochastic bridge from
  almost-sure limits of normalized numerator/denominator processes to an
  almost-sure limit of their quotient.
- `ae_tendsto_empirical_mean_real_of_iid` and
  `ae_tendsto_sum_ratio_of_iid`: narrow wrappers around mathlib's strong law
  for renewal-cycle sample averages and reward/time quotients.
-/

noncomputable section

/-- Renewal-reward earnings rate from arrival rate, expected reward, and expected busy time. -/
def renewalRewardRate (lambda reward time : ℝ) : ℝ :=
  lambda * reward / (1 + lambda * time)

/-- Average reward per unit busy time for a component. -/
def averageRewardRate (reward time : ℝ) : ℝ :=
  reward / time

/--
Adding a positive-time component whose average reward rate is at least the
current renewal-reward rate weakly increases the renewal-reward rate.
-/
theorem renewalRewardRate_le_add_component_of_le_average
    (lambda reward time addedReward addedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_nonneg : 0 ≤ time)
    (hadded_time_pos : 0 < addedTime)
    (hcurrent_le_added_average :
      renewalRewardRate lambda reward time ≤
        averageRewardRate addedReward addedTime) :
    renewalRewardRate lambda reward time ≤
      renewalRewardRate lambda (reward + addedReward) (time + addedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_added : 0 < 1 + lambda * (time + addedTime) := by
    nlinarith [mul_pos hlambda hadded_time_pos]
  have hcross :
      lambda * reward * addedTime ≤
        addedReward * (1 + lambda * time) := by
    rw [div_le_div_iff₀ hden_current hadded_time_pos] at hcurrent_le_added_average
    nlinarith
  rw [div_le_div_iff₀ hden_current hden_added]
  nlinarith

/--
Removing a positive-time component whose average reward rate is at most the
current renewal-reward rate weakly increases the renewal-reward rate.
-/
theorem renewalRewardRate_remove_component_ge_of_average_le
    (lambda reward time removedReward removedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_remaining_nonneg : 0 ≤ time - removedTime)
    (hremoved_time_pos : 0 < removedTime)
    (hremoved_average_le_current :
      averageRewardRate removedReward removedTime ≤
        renewalRewardRate lambda reward time) :
    renewalRewardRate lambda reward time ≤
      renewalRewardRate lambda (reward - removedReward) (time - removedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have htime_nonneg : 0 ≤ time := by
    linarith [le_of_lt hremoved_time_pos]
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_remaining : 0 < 1 + lambda * (time - removedTime) := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_remaining_nonneg]
  have hcross :
      removedReward * (1 + lambda * time) ≤
        lambda * reward * removedTime := by
    rw [div_le_div_iff₀ hremoved_time_pos hden_current] at hremoved_average_le_current
    nlinarith
  rw [div_le_div_iff₀ hden_current hden_remaining]
  nlinarith

/--
Adding a positive-time component whose average reward rate is strictly above
the current renewal-reward rate strictly increases the renewal-reward rate.
-/
theorem renewalRewardRate_lt_add_component_of_lt_average
    (lambda reward time addedReward addedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_nonneg : 0 ≤ time)
    (hadded_time_pos : 0 < addedTime)
    (hcurrent_lt_added_average :
      renewalRewardRate lambda reward time <
        averageRewardRate addedReward addedTime) :
    renewalRewardRate lambda reward time <
      renewalRewardRate lambda (reward + addedReward) (time + addedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_added : 0 < 1 + lambda * (time + addedTime) := by
    nlinarith [mul_pos hlambda hadded_time_pos]
  have hcross :
      lambda * reward * addedTime <
        addedReward * (1 + lambda * time) := by
    rw [div_lt_div_iff₀ hden_current hadded_time_pos] at hcurrent_lt_added_average
    nlinarith
  rw [div_lt_div_iff₀ hden_current hden_added]
  nlinarith

/--
Removing a positive-time component whose average reward rate is strictly below
the current renewal-reward rate strictly increases the renewal-reward rate.
-/
theorem renewalRewardRate_remove_component_gt_of_average_lt
    (lambda reward time removedReward removedTime : ℝ)
    (hlambda : 0 < lambda)
    (htime_remaining_nonneg : 0 ≤ time - removedTime)
    (hremoved_time_pos : 0 < removedTime)
    (hremoved_average_lt_current :
      averageRewardRate removedReward removedTime <
        renewalRewardRate lambda reward time) :
    renewalRewardRate lambda reward time <
      renewalRewardRate lambda (reward - removedReward) (time - removedTime) := by
  unfold renewalRewardRate averageRewardRate at *
  have htime_nonneg : 0 ≤ time := by
    linarith [le_of_lt hremoved_time_pos]
  have hden_current : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hden_remaining : 0 < 1 + lambda * (time - removedTime) := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_remaining_nonneg]
  have hcross :
      removedReward * (1 + lambda * time) <
        lambda * reward * removedTime := by
    rw [div_lt_div_iff₀ hremoved_time_pos hden_current] at hremoved_average_lt_current
    nlinarith
  rw [div_lt_div_iff₀ hden_current hden_remaining]
  nlinarith

/--
If a policy replacement keeps total busy time fixed but strictly increases the
per-cycle reward, then the renewal-reward earnings rate strictly increases.
-/
theorem renewalRewardRate_lt_replace_reward_same_time_of_lt
    (lambda reward time newReward : ℝ)
    (hlambda : 0 < lambda)
    (htime_nonneg : 0 ≤ time)
    (hreward_lt : reward < newReward) :
    renewalRewardRate lambda reward time <
      renewalRewardRate lambda newReward time := by
  unfold renewalRewardRate
  have hden : 0 < 1 + lambda * time := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  have hnum : lambda * reward < lambda * newReward :=
    mul_lt_mul_of_pos_left hreward_lt hlambda
  rw [div_lt_div_iff₀ hden hden]
  exact mul_lt_mul_of_pos_right hnum hden

/--
Generic quotient-limit theorem.  This is the deterministic core used by
renewal-reward LLN bridges after the stochastic law has supplied almost-sure
limits for normalized rewards and times.
-/
theorem tendsto_div_of_tendsto_of_ne
    {ι : Type*} {l : Filter ι} {numerator denominator : ι → ℝ}
    {numeratorLimit denominatorLimit : ℝ}
    (hnumerator :
      Tendsto numerator l (nhds numeratorLimit))
    (hdenominator :
      Tendsto denominator l (nhds denominatorLimit))
    (hdenominator_ne : denominatorLimit ≠ 0) :
    Tendsto (fun n => numerator n / denominator n) l
      (nhds (numeratorLimit / denominatorLimit)) :=
  hnumerator.div hdenominator hdenominator_ne

/--
Almost-sure quotient-limit theorem.  If normalized reward and normalized time
processes satisfy the LLN assumptions almost surely, then the long-run reward
quotient has the corresponding almost-sure limit.
-/
theorem ae_tendsto_div_of_ae_tendsto_of_ne
    {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι}
    {numerator denominator : Ω → ι → ℝ}
    {numeratorLimit denominatorLimit : ℝ}
    (hnumerator :
      ∀ᵐ ω ∂P, Tendsto (numerator ω) l (nhds numeratorLimit))
    (hdenominator :
      ∀ᵐ ω ∂P, Tendsto (denominator ω) l (nhds denominatorLimit))
    (hdenominator_ne : denominatorLimit ≠ 0) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n => numerator ω n / denominator ω n) l
        (nhds (numeratorLimit / denominatorLimit)) := by
  filter_upwards [hnumerator, hdenominator] with ω hn hd
  exact tendsto_div_of_tendsto_of_ne hn hd hdenominator_ne

/--
Strong-law wrapper for real-valued IID renewal-cycle observations.  The
sequence need only be pairwise independent, matching mathlib's Etemadi strong
law.
-/
theorem ae_tendsto_empirical_mean_real_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (X : ℕ → Ω → ℝ)
    (hint : Integrable (X 0) P)
    (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X))
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, X i ω) / n)
        atTop (nhds (∫ ω, X 0 ω ∂P)) :=
  ProbabilityTheory.strong_law_ae_real X hint hindep hident

/--
Almost-sure limit of a renewal reward/time quotient from IID cycle rewards and
times.  This packages the recurring proof move: apply the strong law to the two
cycle sequences, then divide the two sample-average limits.
-/
theorem ae_tendsto_sum_ratio_of_iid
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    (reward time : ℕ → Ω → ℝ)
    (hreward_int : Integrable (reward 0) P)
    (htime_int : Integrable (time 0) P)
    (hreward_indep : Pairwise ((· ⟂ᵢ[P] ·) on reward))
    (htime_indep : Pairwise ((· ⟂ᵢ[P] ·) on time))
    (hreward_ident :
      ∀ i, ProbabilityTheory.IdentDistrib (reward i) (reward 0) P P)
    (htime_ident :
      ∀ i, ProbabilityTheory.IdentDistrib (time i) (time 0) P P)
    (htime_mean_ne : (∫ ω, time 0 ω ∂P) ≠ 0) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ =>
          (∑ i ∈ Finset.range n, reward i ω) /
            (∑ i ∈ Finset.range n, time i ω))
        atTop
        (nhds ((∫ ω, reward 0 ω ∂P) / (∫ ω, time 0 ω ∂P))) := by
  have hreward :=
    ae_tendsto_empirical_mean_real_of_iid reward hreward_int
      hreward_indep hreward_ident
  have htime :=
    ae_tendsto_empirical_mean_real_of_iid time htime_int
      htime_indep htime_ident
  have hratio :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n : ℕ =>
            ((∑ i ∈ Finset.range n, reward i ω) / n) /
              ((∑ i ∈ Finset.range n, time i ω) / n))
          atTop
          (nhds ((∫ ω, reward 0 ω ∂P) / (∫ ω, time 0 ω ∂P))) :=
    ae_tendsto_div_of_ae_tendsto_of_ne hreward htime htime_mean_ne
  filter_upwards [hratio] with ω hω
  refine hω.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn_ne]

/--
Reusable stochastic certificate for a renewal-reward or regeneration argument:
`numeratorAverage` and `denominatorAverage` are the normalized sample-path
quantities, and their almost-sure limits determine the long-run quotient.
-/
structure AlmostSureRatioLimitCertificate
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (l : Filter ι)
    (numeratorAverage denominatorAverage : Ω → ι → ℝ)
    (numeratorLimit denominatorLimit : ℝ) where
  denominatorLimit_ne : denominatorLimit ≠ 0
  numerator_tendsto :
    ∀ᵐ ω ∂P, Tendsto (numeratorAverage ω) l (nhds numeratorLimit)
  denominator_tendsto :
    ∀ᵐ ω ∂P, Tendsto (denominatorAverage ω) l (nhds denominatorLimit)

/--
The long-run quotient supplied by an `AlmostSureRatioLimitCertificate`.
-/
theorem AlmostSureRatioLimitCertificate.tendsto_ratio
    {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι}
    {numeratorAverage denominatorAverage : Ω → ι → ℝ}
    {numeratorLimit denominatorLimit : ℝ}
    (C :
      AlmostSureRatioLimitCertificate P l numeratorAverage denominatorAverage
        numeratorLimit denominatorLimit) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n => numeratorAverage ω n / denominatorAverage ω n) l
        (nhds (numeratorLimit / denominatorLimit)) :=
  ae_tendsto_div_of_ae_tendsto_of_ne
    C.numerator_tendsto C.denominator_tendsto C.denominatorLimit_ne

/--
Almost-sure convergence of the two-state weighted reward decomposition:
time fractions and state reward rates converging almost surely imply
convergence of `μ₁R₁ + μ₂R₂` almost surely.
-/
theorem ae_tendsto_two_state_weighted_reward_of_ae_tendsto
    {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {l : Filter ι}
    {timeFractionI timeFractionJ rewardRateI rewardRateJ : Ω → ι → ℝ}
    {μI μJ RI RJ : ℝ}
    (htimeI :
      ∀ᵐ ω ∂P, Tendsto (timeFractionI ω) l (nhds μI))
    (htimeJ :
      ∀ᵐ ω ∂P, Tendsto (timeFractionJ ω) l (nhds μJ))
    (hrewardI :
      ∀ᵐ ω ∂P, Tendsto (rewardRateI ω) l (nhds RI))
    (hrewardJ :
      ∀ᵐ ω ∂P, Tendsto (rewardRateJ ω) l (nhds RJ)) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n =>
          timeFractionI ω n * rewardRateI ω n +
            timeFractionJ ω n * rewardRateJ ω n)
        l (nhds (μI * RI + μJ * RJ)) := by
  filter_upwards [htimeI, htimeJ, hrewardI, hrewardJ] with
    ω hμI hμJ hRI hRJ
  exact (hμI.mul hRI).add (hμJ.mul hRJ)

end

end AppliedModelingLib
