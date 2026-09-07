import AppliedModelingLib.Foundations.Probability.RenewalReward
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace AppliedModelingLib

open Filter
open MeasureTheory
open scoped Topology

noncomputable section

/-!
# Continuous accepted-set reward primitives

Reusable measure/integral accounting for papers where an agent accepts a
measurable set of positive real quantities, such as trip lengths, service
durations, or job sizes.  This module records generic accepted-set reward
accounting: accepted mass, accepted time/size, accepted reward,
positive-domain feasibility, and the positive-denominator bridge from zero
accepted time to zero accepted mass.

## Main declarations

- `positiveRealAcceptAll`: the positive-real feasible domain.
- `acceptedSetMass`: real-valued measure of an accepted set.
- `acceptedSetTime`: integral of the positive real quantity over an accepted set.
- `acceptedSetReward`: integral of a reward/payment function over an accepted set.
- `continuousSetRenewalRewardRate`: renewal-reward rate from accepted-set
  reward/time primitives.
- `acceptedSetMass_eq_zero_of_time_zero_subset_positive`: a feasible measurable
  set with zero accepted positive time has zero accepted mass.
-/

/-- Feasible positive real quantities. -/
abbrev positiveRealAcceptAll : Set ℝ :=
  Set.Ioi 0

/-- A policy accepts every feasible positive real quantity. -/
abbrev acceptsAllPositiveReal (σ : Set ℝ) : Prop :=
  positiveRealAcceptAll ⊆ σ

/-- The positive-real feasible domain is measurable. -/
theorem measurableSet_positiveRealAcceptAll :
    MeasurableSet positiveRealAcceptAll := by
  simpa [positiveRealAcceptAll] using measurableSet_Ioi

/-- Real-valued mass of an accepted set. -/
abbrev acceptedSetMass (μ : Measure ℝ) (σ : Set ℝ) : ℝ :=
  (μ σ).toReal

/-- Expected accepted positive quantity. -/
abbrev acceptedSetTime (μ : Measure ℝ) (σ : Set ℝ) : ℝ :=
  ∫ x in σ, x ∂μ

/-- Expected reward/payment contributed by an accepted set. -/
abbrev acceptedSetReward (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) : ℝ :=
  ∫ x in σ, reward x ∂μ

/-- Renewal-reward rate from accepted-set reward and time primitives. -/
abbrev continuousSetRenewalRewardRate
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) : ℝ :=
  arrivalRate * acceptedSetReward μ reward σ /
    (1 + arrivalRate * acceptedSetTime μ σ)

/-- Accepted-set reward rate is the generic renewal-reward summary of set integrals. -/
theorem continuousSetRenewalRewardRate_eq_renewalRewardRate
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) :
    continuousSetRenewalRewardRate μ arrivalRate reward σ =
      renewalRewardRate arrivalRate
        (acceptedSetReward μ reward σ) (acceptedSetTime μ σ) := by
  rfl

/-- Average reward per accepted positive quantity. -/
abbrev acceptedSetAverageRewardRate
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) : ℝ :=
  averageRewardRate (acceptedSetReward μ reward σ) (acceptedSetTime μ σ)

/-- Accepted mass is nonnegative for every set. -/
theorem acceptedSetMass_nonneg (μ : Measure ℝ) (σ : Set ℝ) :
    0 ≤ acceptedSetMass μ σ := by
  unfold acceptedSetMass
  exact ENNReal.toReal_nonneg

/-- Unit real-valued mass rules out infinite underlying measure. -/
theorem acceptedSetMass_ne_top_of_eq_one
    {μ : Measure ℝ} {σ : Set ℝ}
    (hmass : acceptedSetMass μ σ = 1) :
    μ σ ≠ ⊤ := by
  intro htop
  have hzero : acceptedSetMass μ σ = 0 := by
    simp [acceptedSetMass, htop]
  linarith

/-- Real accepted mass is monotone under set inclusion when the larger set has finite measure. -/
theorem acceptedSetMass_le_of_subset_of_ne_top
    (μ : Measure ℝ) {σ τ : Set ℝ}
    (hsubset : σ ⊆ τ) (hfinite : μ τ ≠ ⊤) :
    acceptedSetMass μ σ ≤ acceptedSetMass μ τ := by
  unfold acceptedSetMass
  exact ENNReal.toReal_mono hfinite (measure_mono hsubset)

/-- Positive real accepted mass is equivalent to positive finite underlying measure mass. -/
theorem acceptedSetMass_pos_of_measure_ne_zero_ne_top
    (μ : Measure ℝ) (σ : Set ℝ)
    (h_ne_zero : μ σ ≠ 0)
    (h_ne_top : μ σ ≠ ⊤) :
    0 < acceptedSetMass μ σ :=
  ENNReal.toReal_pos h_ne_zero h_ne_top

/-- Positive real accepted mass implies positive underlying measure mass. -/
theorem measure_pos_of_acceptedSetMass_pos
    (μ : Measure ℝ) (σ : Set ℝ)
    (hmass_pos : 0 < acceptedSetMass μ σ) :
    0 < μ σ := by
  simpa [acceptedSetMass] using (ENNReal.toReal_pos_iff.mp hmass_pos).1

/-- Accepted positive quantity is nonnegative for measurable feasible accepted sets. -/
theorem acceptedSetTime_nonneg_of_subset_positive
    (μ : Measure ℝ) (σ : Set ℝ)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ positiveRealAcceptAll) :
    0 ≤ acceptedSetTime μ σ := by
  unfold acceptedSetTime
  exact setIntegral_nonneg hσ_measurable (fun x hx =>
    le_of_lt (hσ_subset hx))

/-- Accepted reward is nonnegative when the reward function is nonnegative on the set. -/
theorem acceptedSetReward_nonneg_of_pointwise_nonneg
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ)
    (hσ_measurable : MeasurableSet σ)
    (hreward_nonneg : ∀ x ∈ σ, 0 ≤ reward x) :
    0 ≤ acceptedSetReward μ reward σ := by
  unfold acceptedSetReward
  exact setIntegral_nonneg hσ_measurable hreward_nonneg

/-- Reward integral over a disjoint union of accepted sets. -/
theorem acceptedSetReward_union
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ added : Set ℝ)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (hreward_integrable_added : IntegrableOn reward added μ) :
    acceptedSetReward μ reward (σ ∪ added) =
      acceptedSetReward μ reward σ + acceptedSetReward μ reward added := by
  unfold acceptedSetReward
  exact setIntegral_union hdisjoint hadded_measurable
    hreward_integrable_σ hreward_integrable_added

/-- Accepted positive quantity over a disjoint union of accepted sets. -/
theorem acceptedSetTime_union
    (μ : Measure ℝ) (σ added : Set ℝ)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (htime_integrable_added : IntegrableOn (fun x : ℝ => x) added μ) :
    acceptedSetTime μ (σ ∪ added) =
      acceptedSetTime μ σ + acceptedSetTime μ added := by
  unfold acceptedSetTime
  exact setIntegral_union hdisjoint hadded_measurable
    htime_integrable_σ htime_integrable_added

/-- Reward integral after removing a measurable accepted subset. -/
theorem acceptedSetReward_diff
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ removed : Set ℝ)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hreward_integrable_σ : IntegrableOn reward σ μ) :
    acceptedSetReward μ reward (σ \ removed) =
      acceptedSetReward μ reward σ - acceptedSetReward μ reward removed := by
  unfold acceptedSetReward
  exact setIntegral_diff hremoved_measurable hreward_integrable_σ hremoved_subset

/-- Accepted positive quantity after removing a measurable accepted subset. -/
theorem acceptedSetTime_diff
    (μ : Measure ℝ) (σ removed : Set ℝ)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ) :
    acceptedSetTime μ (σ \ removed) =
      acceptedSetTime μ σ - acceptedSetTime μ removed := by
  unfold acceptedSetTime
  exact setIntegral_diff hremoved_measurable htime_integrable_σ hremoved_subset

/-- A measure-zero accepted component has zero reward integral. -/
theorem acceptedSetReward_eq_zero_of_measure_zero
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ)
    (hmeasure_zero : μ σ = 0) :
    acceptedSetReward μ reward σ = 0 := by
  unfold acceptedSetReward
  have hrestrict_zero : μ.restrict σ = 0 :=
    Measure.restrict_eq_zero.2 hmeasure_zero
  rw [hrestrict_zero, integral_zero_measure]

/-- A measure-zero accepted component has zero accepted positive quantity. -/
theorem acceptedSetTime_eq_zero_of_measure_zero
    (μ : Measure ℝ) (σ : Set ℝ)
    (hmeasure_zero : μ σ = 0) :
    acceptedSetTime μ σ = 0 := by
  unfold acceptedSetTime
  have hrestrict_zero : μ.restrict σ = 0 :=
    Measure.restrict_eq_zero.2 hmeasure_zero
  rw [hrestrict_zero, integral_zero_measure]

/--
If every accepted quantity has reward at least `targetRate * x`, then the
accepted-set average reward rate is at least `targetRate`.
-/
theorem le_acceptedSetAverageRewardRate_of_pointwise_le
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable : IntegrableOn (fun x : ℝ => x) σ μ)
    (hreward_integrable : IntegrableOn reward σ μ)
    (htime_pos : 0 < acceptedSetTime μ σ)
    (hpointwise : ∀ x ∈ σ, targetRate * x ≤ reward x) :
    targetRate ≤ acceptedSetAverageRewardRate μ reward σ := by
  unfold acceptedSetAverageRewardRate averageRewardRate
  rw [le_div_iff₀ htime_pos]
  unfold acceptedSetReward acceptedSetTime
  have hmono :
      ∫ x in σ, targetRate * x ∂μ ≤ ∫ x in σ, reward x ∂μ :=
    setIntegral_mono_on (htime_integrable.const_mul targetRate)
      hreward_integrable hσ_measurable hpointwise
  rw [integral_const_mul] at hmono
  exact hmono

/--
If every accepted quantity has reward at most `targetRate * x`, then the
accepted-set average reward rate is at most `targetRate`.
-/
theorem acceptedSetAverageRewardRate_le_of_pointwise_le
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable : IntegrableOn (fun x : ℝ => x) σ μ)
    (hreward_integrable : IntegrableOn reward σ μ)
    (htime_pos : 0 < acceptedSetTime μ σ)
    (hpointwise : ∀ x ∈ σ, reward x ≤ targetRate * x) :
    acceptedSetAverageRewardRate μ reward σ ≤ targetRate := by
  unfold acceptedSetAverageRewardRate averageRewardRate
  rw [div_le_iff₀ htime_pos]
  unfold acceptedSetReward acceptedSetTime
  have hmono :
      ∫ x in σ, reward x ∂μ ≤ ∫ x in σ, targetRate * x ∂μ :=
    setIntegral_mono_on hreward_integrable
      (htime_integrable.const_mul targetRate) hσ_measurable hpointwise
  rw [integral_const_mul] at hmono
  exact hmono

/--
If every accepted quantity has reward strictly above `targetRate * x`, then
the accepted-set average reward rate is strictly above `targetRate`.
-/
theorem lt_acceptedSetAverageRewardRate_of_pointwise_lt
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable : IntegrableOn (fun x : ℝ => x) σ μ)
    (hreward_integrable : IntegrableOn reward σ μ)
    (htime_pos : 0 < acceptedSetTime μ σ)
    (hpointwise : ∀ x ∈ σ, targetRate * x < reward x) :
    targetRate < acceptedSetAverageRewardRate μ reward σ := by
  unfold acceptedSetAverageRewardRate averageRewardRate
  rw [lt_div_iff₀ htime_pos]
  unfold acceptedSetReward acceptedSetTime
  have hdiff_integrable :
      IntegrableOn (fun x : ℝ => reward x - targetRate * x) σ μ :=
    hreward_integrable.sub (htime_integrable.const_mul targetRate)
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ] (fun x : ℝ => reward x - targetRate * x) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun x hx =>
        le_of_lt (sub_pos.mpr (hpointwise x hx))))
  have hsupport :
      Function.support (fun x : ℝ => reward x - targetRate * x) ∩ σ = σ := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨ne_of_gt (sub_pos.mpr (hpointwise x hx)), hx⟩
  have hmeasure_pos : 0 < μ σ := by
    by_contra hnot_pos
    have hmeasure_zero : μ σ = 0 :=
      le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
    have hrestrict_zero : μ.restrict σ = 0 :=
      Measure.restrict_eq_zero.2 hmeasure_zero
    unfold acceptedSetTime at htime_pos
    rw [hrestrict_zero, integral_zero_measure] at htime_pos
    exact (lt_irrefl (0 : ℝ)) htime_pos
  have hdiff_pos :
      0 < ∫ x in σ, reward x - targetRate * x ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae hdiff_integrable).2 (by
        simpa [hsupport] using hmeasure_pos)
  rw [integral_sub hreward_integrable (htime_integrable.const_mul targetRate),
    integral_const_mul] at hdiff_pos
  linarith

/--
If every accepted quantity has reward strictly below `targetRate * x`, then
the accepted-set average reward rate is strictly below `targetRate`.
-/
theorem acceptedSetAverageRewardRate_lt_of_pointwise_lt
    (μ : Measure ℝ) (reward : ℝ → ℝ) (σ : Set ℝ) (targetRate : ℝ)
    (hσ_measurable : MeasurableSet σ)
    (htime_integrable : IntegrableOn (fun x : ℝ => x) σ μ)
    (hreward_integrable : IntegrableOn reward σ μ)
    (htime_pos : 0 < acceptedSetTime μ σ)
    (hpointwise : ∀ x ∈ σ, reward x < targetRate * x) :
    acceptedSetAverageRewardRate μ reward σ < targetRate := by
  unfold acceptedSetAverageRewardRate averageRewardRate
  rw [div_lt_iff₀ htime_pos]
  unfold acceptedSetReward acceptedSetTime
  have hdiff_integrable :
      IntegrableOn (fun x : ℝ => targetRate * x - reward x) σ μ :=
    (htime_integrable.const_mul targetRate).sub hreward_integrable
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ] (fun x : ℝ => targetRate * x - reward x) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun x hx =>
        le_of_lt (sub_pos.mpr (hpointwise x hx))))
  have hsupport :
      Function.support (fun x : ℝ => targetRate * x - reward x) ∩ σ = σ := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨ne_of_gt (sub_pos.mpr (hpointwise x hx)), hx⟩
  have hmeasure_pos : 0 < μ σ := by
    by_contra hnot_pos
    have hmeasure_zero : μ σ = 0 :=
      le_antisymm (le_of_not_gt hnot_pos) (zero_le _)
    have hrestrict_zero : μ.restrict σ = 0 :=
      Measure.restrict_eq_zero.2 hmeasure_zero
    unfold acceptedSetTime at htime_pos
    rw [hrestrict_zero, integral_zero_measure] at htime_pos
    exact (lt_irrefl (0 : ℝ)) htime_pos
  have hdiff_pos :
      0 < ∫ x in σ, targetRate * x - reward x ∂μ :=
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae hdiff_integrable).2 (by
        simpa [hsupport] using hmeasure_pos)
  rw [integral_sub (htime_integrable.const_mul targetRate) hreward_integrable,
    integral_const_mul] at hdiff_pos
  linarith

/-- Renewal reward is positive when arrival rate and accepted reward are positive. -/
theorem continuousSetRenewalRewardRate_pos_of_reward_pos
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ) (σ : Set ℝ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ acceptedSetTime μ σ)
    (hreward_pos : 0 < acceptedSetReward μ reward σ) :
    0 < continuousSetRenewalRewardRate μ arrivalRate reward σ := by
  unfold continuousSetRenewalRewardRate
  have hnum_pos :
      0 < arrivalRate * acceptedSetReward μ reward σ :=
    mul_pos hlambda hreward_pos
  have hden_pos :
      0 < 1 + arrivalRate * acceptedSetTime μ σ := by
    nlinarith [mul_nonneg (le_of_lt hlambda) htime_nonneg]
  exact div_pos hnum_pos hden_pos

/--
Adding a disjoint positive-time set whose average reward rate is at least the
current renewal reward cannot reduce the accepted-set renewal reward.
-/
theorem continuousSetRenewalRewardRate_le_union_of_le_average
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ added : Set ℝ)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (hreward_integrable_added : IntegrableOn reward added μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (htime_integrable_added : IntegrableOn (fun x : ℝ => x) added μ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ acceptedSetTime μ σ)
    (hadded_time_pos : 0 < acceptedSetTime μ added)
    (hcurrent_le_added_average :
      continuousSetRenewalRewardRate μ arrivalRate reward σ ≤
        acceptedSetAverageRewardRate μ reward added) :
    continuousSetRenewalRewardRate μ arrivalRate reward σ ≤
      continuousSetRenewalRewardRate μ arrivalRate reward (σ ∪ added) := by
  change
    renewalRewardRate arrivalRate
        (acceptedSetReward μ reward σ) (acceptedSetTime μ σ) ≤
      renewalRewardRate arrivalRate
        (acceptedSetReward μ reward (σ ∪ added))
        (acceptedSetTime μ (σ ∪ added))
  rw [acceptedSetReward_union μ reward σ added hdisjoint hadded_measurable
      hreward_integrable_σ hreward_integrable_added,
    acceptedSetTime_union μ σ added hdisjoint hadded_measurable
      htime_integrable_σ htime_integrable_added]
  exact renewalRewardRate_le_add_component_of_le_average
    arrivalRate (acceptedSetReward μ reward σ) (acceptedSetTime μ σ)
    (acceptedSetReward μ reward added) (acceptedSetTime μ added)
    hlambda htime_nonneg hadded_time_pos
    (by
      simpa [continuousSetRenewalRewardRate,
        acceptedSetAverageRewardRate, renewalRewardRate] using
          hcurrent_le_added_average)

/--
Removing a positive-time accepted subset whose average reward rate is at most
the current renewal reward cannot reduce the accepted-set renewal reward.
-/
theorem continuousSetRenewalRewardRate_le_diff_of_average_le
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ removed : Set ℝ)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (hlambda : 0 < arrivalRate)
    (htime_remaining_nonneg :
      0 ≤ acceptedSetTime μ σ - acceptedSetTime μ removed)
    (hremoved_time_pos : 0 < acceptedSetTime μ removed)
    (hremoved_average_le_current :
      acceptedSetAverageRewardRate μ reward removed ≤
        continuousSetRenewalRewardRate μ arrivalRate reward σ) :
    continuousSetRenewalRewardRate μ arrivalRate reward σ ≤
      continuousSetRenewalRewardRate μ arrivalRate reward (σ \ removed) := by
  change
    renewalRewardRate arrivalRate
        (acceptedSetReward μ reward σ) (acceptedSetTime μ σ) ≤
      renewalRewardRate arrivalRate
        (acceptedSetReward μ reward (σ \ removed))
        (acceptedSetTime μ (σ \ removed))
  rw [acceptedSetReward_diff μ reward σ removed hremoved_subset
      hremoved_measurable hreward_integrable_σ,
    acceptedSetTime_diff μ σ removed hremoved_subset hremoved_measurable
      htime_integrable_σ]
  exact renewalRewardRate_remove_component_ge_of_average_le
    arrivalRate (acceptedSetReward μ reward σ) (acceptedSetTime μ σ)
    (acceptedSetReward μ reward removed) (acceptedSetTime μ removed)
    hlambda htime_remaining_nonneg hremoved_time_pos
    (by
      simpa [continuousSetRenewalRewardRate,
        acceptedSetAverageRewardRate, renewalRewardRate] using
          hremoved_average_le_current)

/--
Adding a disjoint positive-time set whose average reward rate is strictly above
the current renewal reward strictly increases the accepted-set renewal reward.
-/
theorem continuousSetRenewalRewardRate_lt_union_of_lt_average
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ added : Set ℝ)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (hreward_integrable_added : IntegrableOn reward added μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (htime_integrable_added : IntegrableOn (fun x : ℝ => x) added μ)
    (hlambda : 0 < arrivalRate)
    (htime_nonneg : 0 ≤ acceptedSetTime μ σ)
    (hadded_time_pos : 0 < acceptedSetTime μ added)
    (hcurrent_lt_added_average :
      continuousSetRenewalRewardRate μ arrivalRate reward σ <
        acceptedSetAverageRewardRate μ reward added) :
    continuousSetRenewalRewardRate μ arrivalRate reward σ <
      continuousSetRenewalRewardRate μ arrivalRate reward (σ ∪ added) := by
  change
    renewalRewardRate arrivalRate
        (acceptedSetReward μ reward σ) (acceptedSetTime μ σ) <
      renewalRewardRate arrivalRate
        (acceptedSetReward μ reward (σ ∪ added))
        (acceptedSetTime μ (σ ∪ added))
  rw [acceptedSetReward_union μ reward σ added hdisjoint hadded_measurable
      hreward_integrable_σ hreward_integrable_added,
    acceptedSetTime_union μ σ added hdisjoint hadded_measurable
      htime_integrable_σ htime_integrable_added]
  exact renewalRewardRate_lt_add_component_of_lt_average
    arrivalRate (acceptedSetReward μ reward σ) (acceptedSetTime μ σ)
    (acceptedSetReward μ reward added) (acceptedSetTime μ added)
    hlambda htime_nonneg hadded_time_pos
    (by
      simpa [continuousSetRenewalRewardRate,
        acceptedSetAverageRewardRate, renewalRewardRate] using
          hcurrent_lt_added_average)

/--
Removing a positive-time accepted subset whose average reward rate is strictly
below the current renewal reward strictly increases the accepted-set renewal
reward.
-/
theorem continuousSetRenewalRewardRate_lt_diff_of_average_lt
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ removed : Set ℝ)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (hlambda : 0 < arrivalRate)
    (htime_remaining_nonneg :
      0 ≤ acceptedSetTime μ σ - acceptedSetTime μ removed)
    (hremoved_time_pos : 0 < acceptedSetTime μ removed)
    (hremoved_average_lt_current :
      acceptedSetAverageRewardRate μ reward removed <
        continuousSetRenewalRewardRate μ arrivalRate reward σ) :
    continuousSetRenewalRewardRate μ arrivalRate reward σ <
      continuousSetRenewalRewardRate μ arrivalRate reward (σ \ removed) := by
  change
    renewalRewardRate arrivalRate
        (acceptedSetReward μ reward σ) (acceptedSetTime μ σ) <
      renewalRewardRate arrivalRate
        (acceptedSetReward μ reward (σ \ removed))
        (acceptedSetTime μ (σ \ removed))
  rw [acceptedSetReward_diff μ reward σ removed hremoved_subset
      hremoved_measurable hreward_integrable_σ,
    acceptedSetTime_diff μ σ removed hremoved_subset hremoved_measurable
      htime_integrable_σ]
  exact renewalRewardRate_remove_component_gt_of_average_lt
    arrivalRate (acceptedSetReward μ reward σ) (acceptedSetTime μ σ)
    (acceptedSetReward μ reward removed) (acceptedSetTime μ removed)
    hlambda htime_remaining_nonneg hremoved_time_pos
    (by
      simpa [continuousSetRenewalRewardRate,
        acceptedSetAverageRewardRate, renewalRewardRate] using
          hremoved_average_lt_current)

/-- Removing a zero reward/time accepted subset leaves renewal reward unchanged. -/
theorem continuousSetRenewalRewardRate_diff_eq_self_of_zero_component
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ removed : Set ℝ)
    (hremoved_subset : removed ⊆ σ)
    (hremoved_measurable : MeasurableSet removed)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (hremoved_reward_zero : acceptedSetReward μ reward removed = 0)
    (hremoved_time_zero : acceptedSetTime μ removed = 0) :
    continuousSetRenewalRewardRate μ arrivalRate reward (σ \ removed) =
      continuousSetRenewalRewardRate μ arrivalRate reward σ := by
  unfold continuousSetRenewalRewardRate
  rw [acceptedSetReward_diff μ reward σ removed hremoved_subset
      hremoved_measurable hreward_integrable_σ,
    acceptedSetTime_diff μ σ removed hremoved_subset hremoved_measurable
      htime_integrable_σ]
  rw [hremoved_reward_zero, hremoved_time_zero]
  ring

/-- Adding a disjoint zero reward/time set leaves renewal reward unchanged. -/
theorem continuousSetRenewalRewardRate_union_eq_self_of_zero_component
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ added : Set ℝ)
    (hdisjoint : Disjoint σ added)
    (hadded_measurable : MeasurableSet added)
    (hreward_integrable_σ : IntegrableOn reward σ μ)
    (hreward_integrable_added : IntegrableOn reward added μ)
    (htime_integrable_σ : IntegrableOn (fun x : ℝ => x) σ μ)
    (htime_integrable_added : IntegrableOn (fun x : ℝ => x) added μ)
    (hadded_reward_zero : acceptedSetReward μ reward added = 0)
    (hadded_time_zero : acceptedSetTime μ added = 0) :
    continuousSetRenewalRewardRate μ arrivalRate reward (σ ∪ added) =
      continuousSetRenewalRewardRate μ arrivalRate reward σ := by
  unfold continuousSetRenewalRewardRate
  rw [acceptedSetReward_union μ reward σ added hdisjoint hadded_measurable
      hreward_integrable_σ hreward_integrable_added,
    acceptedSetTime_union μ σ added hdisjoint hadded_measurable
      htime_integrable_σ htime_integrable_added]
  rw [hadded_reward_zero, hadded_time_zero]
  ring

/--
If accepted reward and accepted time vanish along a filter, then the
accepted-set renewal reward vanishes along that filter.
-/
theorem continuousSetRenewalRewardRate_tendsto_zero_of_reward_time_tendsto_zero
    {ι : Type*} (l : Filter ι)
    (μ : Measure ℝ) (arrivalRate : ℝ) (reward : ℝ → ℝ)
    (σ : ι → Set ℝ)
    (hreward_tendsto_zero :
      Tendsto (fun i => acceptedSetReward μ reward (σ i)) l (𝓝 0))
    (htime_tendsto_zero :
      Tendsto (fun i => acceptedSetTime μ (σ i)) l (𝓝 0)) :
    Tendsto
      (fun i => continuousSetRenewalRewardRate μ arrivalRate reward (σ i))
      l (𝓝 0) := by
  unfold continuousSetRenewalRewardRate
  have hnum :
      Tendsto
        (fun i => arrivalRate * acceptedSetReward μ reward (σ i))
        l (𝓝 (arrivalRate * 0)) :=
    tendsto_const_nhds.mul hreward_tendsto_zero
  have hden :
      Tendsto
        (fun i => 1 + arrivalRate * acceptedSetTime μ (σ i))
        l (𝓝 (1 + arrivalRate * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul htime_tendsto_zero)
  have hdiv :
      Tendsto
        (fun i =>
          (arrivalRate * acceptedSetReward μ reward (σ i)) /
            (1 + arrivalRate * acceptedSetTime μ (σ i)))
        l (𝓝 ((arrivalRate * 0) / (1 + arrivalRate * 0))) :=
    hnum.div hden (by norm_num)
  simpa using hdiv

/--
A measurable feasible set with zero accepted positive quantity has zero mass.
This captures the common "no mass at zero" bridge for domains restricted to
positive real quantities.
-/
theorem acceptedSetMass_eq_zero_of_time_zero_subset_positive
    (μ : Measure ℝ) (σ : Set ℝ)
    (hσ_measurable : MeasurableSet σ)
    (hσ_subset : σ ⊆ positiveRealAcceptAll)
    (htime_integrable_acceptAll :
      IntegrableOn (fun x : ℝ => x) positiveRealAcceptAll μ)
    (htime_zero : acceptedSetTime μ σ = 0) :
    acceptedSetMass μ σ = 0 := by
  have htime_integrable :
      IntegrableOn (fun x : ℝ => x) σ μ :=
    htime_integrable_acceptAll.mono_set hσ_subset
  have hnonneg_ae :
      0 ≤ᵐ[μ.restrict σ] (fun x : ℝ => x) :=
    (ae_restrict_iff' hσ_measurable).2
      (Filter.Eventually.of_forall (fun x hx =>
        le_of_lt (hσ_subset hx)))
  have hsupport :
      Function.support (fun x : ℝ => x) ∩ σ = σ := by
    ext x
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨ne_of_gt (hσ_subset hx), hx⟩
  have hmeasure_zero : μ σ = 0 := by
    by_contra hmeasure_ne_zero
    have hmeasure_pos : 0 < μ σ := pos_iff_ne_zero.2 hmeasure_ne_zero
    have hintegral_pos :
        0 < ∫ x in σ, x ∂μ := by
      exact (setIntegral_pos_iff_support_of_nonneg_ae
        hnonneg_ae htime_integrable).2 (by
          simpa [hsupport] using hmeasure_pos)
    unfold acceptedSetTime at htime_zero
    rw [htime_zero] at hintegral_pos
    exact (lt_irrefl (0 : ℝ)) hintegral_pos
  unfold acceptedSetMass
  simp [hmeasure_zero]

end

end AppliedModelingLib
