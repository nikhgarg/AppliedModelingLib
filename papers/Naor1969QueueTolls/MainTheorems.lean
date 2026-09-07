import Naor1969QueueTolls.Definitions
import Mathlib

/-!
# Paper-Facing Theorems: The Regulation of Queue Size by Levying Tolls

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace Naor1969QueueTolls

open AppliedModelingLib Probability
open AppliedModelingLib.Probability.Queueing

/-- The finite-capacity birth--death law supplies the source paper's stationary
queue-length calculation, including the traffic-intensity-one boundary. -/
theorem finiteCapacityStationaryLaw_impl
    (rho serviceRate : ℝ) (capacity : ℕ) (hrho_nonneg : 0 ≤ rho) :
    ∃ law : GeneratorStationaryLaw
      (finiteCapacityBirthDeathRates (rho * serviceRate) serviceRate capacity),
      law.mass = finiteCapacityGeometricMass rho capacity := by
  refine ⟨finiteCapacity_geometricGeneratorStationaryLaw rho serviceRate
    hrho_nonneg capacity, rfl⟩

/-- The finite-capacity stationary law gives the probability generating
function and the arrival/service flow identities used in the source model. -/
theorem stationaryPerformance_impl
    (rho serviceRate z : ℝ) (capacity : ℕ) (hrho_pos : 0 < rho) :
    expectedQueueSize rho capacity =
        finiteCapacityWeightedGeometricSum rho capacity /
          finiteCapacityGeometricNormalizer rho capacity ∧
      stationaryGeneratingFunction rho z capacity =
        finiteCapacityGeometricNormalizer (rho * z) capacity /
          finiteCapacityGeometricNormalizer rho capacity ∧
      divertedArrivalRate (rho * serviceRate) rho capacity +
          admittedArrivalRate (rho * serviceRate) rho capacity = rho * serviceRate ∧
      admittedArrivalRate (rho * serviceRate) rho capacity =
        serviceRate * busyFraction rho capacity ∧
      (0 < capacity →
        busyFraction rho capacity /
            (1 - stationaryProbability rho capacity capacity) = rho) := by
  constructor
  · exact expectedQueueSize_eq_finiteCapacityExpectedState rho capacity
  constructor
  · exact stationaryGeneratingFunction_eq_normalizer_ratio rho z capacity
  constructor
  · simpa only [admittedArrivalRate_eq_finiteCapacityAdmittedArrivalRate,
        divertedArrivalRate_eq_finiteCapacityRejectedArrivalRate] using
      (add_comm (finiteCapacityRejectedArrivalRate (rho * serviceRate) rho capacity)
        (finiteCapacityAdmittedArrivalRate (rho * serviceRate) rho capacity)).trans
        (finiteCapacityAdmitted_add_rejected_eq_arrivalRate (rho * serviceRate) rho capacity)
  constructor
  · exact admittedArrivalRate_eq_serviceRate_mul_busyFraction hrho_pos.le capacity
  · exact busyFraction_div_admissionProbability_eq_trafficIntensity hrho_pos capacity

/-- At a visible M/M/1 state, the expected net gain from joining is nonnegative
exactly below the source paper's selfish threshold. -/
theorem selfOptimizingThreshold_impl
    (reward queueCost serviceRate : ℝ)
    (hqueueCost_pos : 0 < queueCost) (hserviceRate_pos : 0 < serviceRate)
    (hmeaningful : 1 ≤ reward * serviceRate / queueCost) :
    (∀ queueLength : ℕ,
      queueLength < Nat.floor (reward * serviceRate / queueCost) →
        0 ≤ reward - ((queueLength + 1 : ℕ) : ℝ) * queueCost / serviceRate) ∧
      (∀ queueLength : ℕ,
        Nat.floor (reward * serviceRate / queueCost) ≤ queueLength →
          reward - ((queueLength + 1 : ℕ) : ℝ) * queueCost / serviceRate < 0) := by
  let value := reward * serviceRate / queueCost
  have hvalue_nonneg : 0 ≤ value := by
    dsimp [value]
    linarith
  have hgain (queueLength : ℕ) :
      reward - ((queueLength + 1 : ℕ) : ℝ) * queueCost / serviceRate =
        (queueCost / serviceRate) *
          (value - ((queueLength + 1 : ℕ) : ℝ)) := by
    dsimp [value]
    field_simp [ne_of_gt hqueueCost_pos, ne_of_gt hserviceRate_pos]
  constructor
  · intro queueLength hqueueLength
    change queueLength < Nat.floor value at hqueueLength
    have hsuccessor : queueLength + 1 ≤ Nat.floor value := by
      omega
    have hsuccessor_real : ((queueLength + 1 : ℕ) : ℝ) ≤ value := by
      calc
        ((queueLength + 1 : ℕ) : ℝ) ≤ (Nat.floor value : ℝ) := by
          exact_mod_cast hsuccessor
        _ ≤ value := Nat.floor_le hvalue_nonneg
    rw [hgain]
    exact mul_nonneg (div_nonneg hqueueCost_pos.le hserviceRate_pos.le)
      (sub_nonneg.mpr hsuccessor_real)
  · intro queueLength hqueueLength
    change Nat.floor value ≤ queueLength at hqueueLength
    have hsuccessor : Nat.floor value + 1 ≤ queueLength + 1 := by
      omega
    have hsuccessor_real : value < ((queueLength + 1 : ℕ) : ℝ) := by
      calc
        value < (Nat.floor value : ℝ) + 1 := Nat.lt_floor_add_one value
        _ ≤ ((queueLength + 1 : ℕ) : ℝ) := by
          exact_mod_cast hsuccessor
    rw [hgain]
    exact mul_neg_of_pos_of_neg (div_pos hqueueCost_pos hserviceRate_pos)
      (sub_neg.mpr hsuccessor_real)

/-- The welfare objective has a finite global maximizer no larger than the
individual-admission threshold.  Its construction is the first capacity at
which the cumulative delay exposure exceeds the service value. -/
theorem socialOptimalThreshold_exists_with_cross_impl
    (rho reward queueCost serviceRate : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate)
    (hmeaningful : 1 ≤ reward * serviceRate / queueCost) :
    ∃ socialCapacity : ℕ,
      (∀ capacity : ℕ,
        finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho capacity ≤
          finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
            socialCapacity) ∧
      reward * serviceRate / queueCost <
        finiteCapacityOpportunityCost rho socialCapacity ∧
      socialCapacity ≤ Nat.floor (reward * serviceRate / queueCost) := by
  let value := reward * serviceRate / queueCost
  have hvalue_nonneg : 0 ≤ value := by
    dsimp [value]
    linarith
  have hcross_at_floor :
      value < finiteCapacityOpportunityCost rho (Nat.floor value) := by
    calc
      value < ((Nat.floor value + 1 : ℕ) : ℝ) := by
        norm_num
        exact Nat.lt_floor_add_one value
      _ ≤ finiteCapacityOpportunityCost rho (Nat.floor value) :=
        finiteCapacityOpportunityCost_lower_bound hrho_nonneg (Nat.floor value)
  have hcross_exists : ∃ capacity : ℕ,
      value < finiteCapacityOpportunityCost rho capacity :=
    ⟨Nat.floor value, hcross_at_floor⟩
  let socialCapacity := Nat.find hcross_exists
  have hsocial_cross : value < finiteCapacityOpportunityCost rho socialCapacity := by
    simpa [socialCapacity] using Nat.find_spec hcross_exists
  have hsocial_le_floor : socialCapacity ≤ Nat.floor value := by
    simpa [socialCapacity] using Nat.find_min' hcross_exists hcross_at_floor
  refine ⟨socialCapacity, ?_, hsocial_cross, hsocial_le_floor⟩
  apply adjacentUnimodal_isGreatest
  · intro capacity hcapacity
    have hnot_cross : ¬ value < finiteCapacityOpportunityCost rho capacity := by
      simpa [socialCapacity] using Nat.find_min hcross_exists hcapacity
    have hfactor_nonneg :
        0 ≤ queueCost * rho ^ (capacity + 1) /
          (finiteCapacityGeometricNormalizer rho capacity *
            finiteCapacityGeometricNormalizer rho (capacity + 1)) := by
      apply div_nonneg
      · exact mul_nonneg hqueueCost_pos.le (pow_nonneg hrho_nonneg _)
      · exact mul_nonneg
          (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity).le
          (finiteCapacityGeometricNormalizer_pos hrho_nonneg (capacity + 1)).le
    have hvalue_ge : finiteCapacityOpportunityCost rho capacity ≤ value :=
      le_of_not_gt hnot_cross
    have hdiff :
        0 ≤ finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
              (capacity + 1) -
            finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
              capacity := by
      rw [finiteCapacityLinearHoldingReward_succ_sub hrho_nonneg hqueueCost_pos]
      exact mul_nonneg hfactor_nonneg (sub_nonneg.mpr hvalue_ge)
    exact sub_nonneg.mp hdiff
  · intro capacity hcapacity
    have hdelay_ge :
        finiteCapacityOpportunityCost rho socialCapacity ≤
          finiteCapacityOpportunityCost rho capacity :=
      finiteCapacityOpportunityCost_monotone hrho_nonneg hcapacity
    have hvalue_lt : value < finiteCapacityOpportunityCost rho capacity :=
      hsocial_cross.trans_le hdelay_ge
    have hfactor_nonneg :
        0 ≤ queueCost * rho ^ (capacity + 1) /
          (finiteCapacityGeometricNormalizer rho capacity *
            finiteCapacityGeometricNormalizer rho (capacity + 1)) := by
      apply div_nonneg
      · exact mul_nonneg hqueueCost_pos.le (pow_nonneg hrho_nonneg _)
      · exact mul_nonneg
          (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity).le
          (finiteCapacityGeometricNormalizer_pos hrho_nonneg (capacity + 1)).le
    have hdiff :
        finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
              (capacity + 1) -
            finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
              capacity ≤ 0 := by
      rw [finiteCapacityLinearHoldingReward_succ_sub hrho_nonneg hqueueCost_pos]
      exact mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg (sub_nonpos.mpr hvalue_lt.le)
    exact sub_nonpos.mp hdiff

/-- The welfare objective has a finite global maximizer no larger than the
individual-admission threshold. -/
theorem socialOptimalThreshold_exists_impl
    (rho reward queueCost serviceRate : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate)
    (hmeaningful : 1 ≤ reward * serviceRate / queueCost) :
    ∃ socialCapacity : ℕ,
      (∀ capacity : ℕ,
        finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho capacity ≤
          finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
            socialCapacity) ∧
      socialCapacity ≤ Nat.floor (reward * serviceRate / queueCost) := by
  obtain ⟨socialCapacity, hmax, _hcross, hbound⟩ :=
    socialOptimalThreshold_exists_with_cross_impl rho reward queueCost serviceRate
      hrho_nonneg hqueueCost_pos hserviceRate_pos hmeaningful
  exact ⟨socialCapacity, hmax, hbound⟩

/-- Once cumulative delay exposure reaches service value, raising the admission
threshold can no longer increase toll revenue at the corresponding threshold
implementing fees. -/
theorem revenueThreshold_succ_le_of_value_le_opportunityCost
    (rho reward queueCost serviceRate : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate) (capacity : ℕ)
    (hvalue_le : reward * serviceRate / queueCost ≤
      finiteCapacityOpportunityCost rho capacity) :
    finiteCapacityAdmissionRevenue (rho * serviceRate)
        (reward - ((capacity + 1 : ℕ) : ℝ) * queueCost / serviceRate) rho
        (capacity + 1) ≤
      finiteCapacityAdmissionRevenue (rho * serviceRate)
        (reward - (capacity : ℝ) * queueCost / serviceRate) rho capacity := by
  have hpower_nonneg : 0 ≤ rho ^ capacity := pow_nonneg hrho_nonneg capacity
  have hcapacity_nonneg : 0 ≤ (capacity : ℝ) := Nat.cast_nonneg capacity
  have hinside :
      (reward * serviceRate / queueCost - (capacity : ℝ)) * rho ^ capacity -
          finiteCapacityGeometricNormalizer rho capacity ^ 2 ≤ 0 := by
    apply sub_nonpos.mpr
    calc
      (reward * serviceRate / queueCost - (capacity : ℝ)) * rho ^ capacity ≤
          (reward * serviceRate / queueCost) * rho ^ capacity := by
        nlinarith
      _ ≤ finiteCapacityOpportunityCost rho capacity * rho ^ capacity :=
        mul_le_mul_of_nonneg_right hvalue_le hpower_nonneg
      _ = rho ^ capacity * finiteCapacityOpportunityCost rho capacity := by ring
      _ ≤ finiteCapacityGeometricNormalizer rho capacity ^ 2 :=
        finiteCapacity_terminal_mul_opportunityCost_le_normalizer_sq hrho_nonneg capacity
  have hfactor_nonneg :
      0 ≤ queueCost * rho /
          (finiteCapacityGeometricNormalizer rho capacity *
            finiteCapacityGeometricNormalizer rho (capacity + 1)) := by
    apply div_nonneg
    · exact mul_nonneg hqueueCost_pos.le hrho_nonneg
    · exact mul_nonneg
        (finiteCapacityGeometricNormalizer_pos hrho_nonneg capacity).le
        (finiteCapacityGeometricNormalizer_pos hrho_nonneg (capacity + 1)).le
  have hdiff :
      finiteCapacityAdmissionRevenue (rho * serviceRate)
          (reward - ((capacity + 1 : ℕ) : ℝ) * queueCost / serviceRate) rho
          (capacity + 1) -
        finiteCapacityAdmissionRevenue (rho * serviceRate)
          (reward - (capacity : ℝ) * queueCost / serviceRate) rho capacity ≤ 0 := by
    rw [finiteCapacityAdmissionRevenue_succ_sub hrho_nonneg hqueueCost_pos
      hserviceRate_pos]
    exact mul_nonpos_of_nonneg_of_nonpos hfactor_nonneg hinside
  exact sub_nonpos.mp hdiff

/-- A revenue-maximizing threshold can be selected no higher than the social
threshold.  The proof maximizes revenue on the finite social prefix and uses
the delay-exposure comparison to rule out every larger threshold. -/
theorem socialAndRevenueThresholdOrder_impl
    (rho reward queueCost serviceRate : ℝ)
    (hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate)
    (hmeaningful : 1 ≤ reward * serviceRate / queueCost) :
    ∃ revenueCapacity socialCapacity : ℕ,
      (∀ capacity : ℕ, (capacity : ℝ) ≤ reward * serviceRate / queueCost →
        finiteCapacityAdmissionRevenue (rho * serviceRate)
            (reward - (capacity : ℝ) * queueCost / serviceRate) rho capacity ≤
          finiteCapacityAdmissionRevenue (rho * serviceRate)
            (reward - (revenueCapacity : ℝ) * queueCost / serviceRate) rho
            revenueCapacity) ∧
      (∀ capacity : ℕ,
        finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho capacity ≤
          finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho
            socialCapacity) ∧
      revenueCapacity ≤ socialCapacity ∧
      socialCapacity ≤ Nat.floor (reward * serviceRate / queueCost) := by
  obtain ⟨socialCapacity, hsocial_max, hsocial_cross, hsocial_bound⟩ :=
    socialOptimalThreshold_exists_with_cross_impl rho reward queueCost serviceRate
      hrho_nonneg hqueueCost_pos hserviceRate_pos hmeaningful
  let revenueObjective : ℕ → ℝ := fun capacity =>
    finiteCapacityAdmissionRevenue (rho * serviceRate)
      (reward - (capacity : ℝ) * queueCost / serviceRate) rho capacity
  have hpref_nonempty : (Finset.range (socialCapacity + 1)).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  obtain ⟨revenueCapacity, hcapacity_mem, hprefix_max⟩ :=
    Finset.exists_max_image (Finset.range (socialCapacity + 1)) revenueObjective
      hpref_nonempty
  have hcapacity_le_social : revenueCapacity ≤ socialCapacity := by
    simpa using (Finset.mem_range_succ_iff.mp hcapacity_mem)
  have htail : ∀ capacity : ℕ, socialCapacity ≤ capacity →
      revenueObjective capacity ≤ revenueObjective socialCapacity := by
    intro capacity hcapacity
    refine Nat.le_induction ?_ ?_ capacity hcapacity
    · exact le_rfl
    · intro n hn ih
      have hdelay_ge :
          finiteCapacityOpportunityCost rho socialCapacity ≤
            finiteCapacityOpportunityCost rho n :=
        finiteCapacityOpportunityCost_monotone hrho_nonneg hn
      have hvalue_le : reward * serviceRate / queueCost ≤
          finiteCapacityOpportunityCost rho n :=
        hsocial_cross.le.trans hdelay_ge
      exact (revenueThreshold_succ_le_of_value_le_opportunityCost rho reward queueCost
        serviceRate hrho_nonneg hqueueCost_pos hserviceRate_pos n hvalue_le).trans ih
  refine ⟨revenueCapacity, socialCapacity, ?_, hsocial_max,
    hcapacity_le_social, hsocial_bound⟩
  intro capacity _hfeasible
  change revenueObjective capacity ≤ revenueObjective revenueCapacity
  rcases le_total capacity socialCapacity with hprefix | htail_capacity
  · exact hprefix_max capacity (by
      simpa using (Finset.mem_range_succ_iff.mpr hprefix))
  · calc
      revenueObjective capacity ≤ revenueObjective socialCapacity :=
        htail capacity htail_capacity
      _ ≤ revenueObjective revenueCapacity := hprefix_max socialCapacity (by simp)

/-- A toll in the source interval produces the selected threshold under the
same tie-breaking convention as the paper. -/
theorem socialTollImplementsOptimalThreshold_impl
    (rho reward queueCost serviceRate toll : ℝ) (socialCapacity : ℕ)
    (_hrho_nonneg : 0 ≤ rho) (hqueueCost_pos : 0 < queueCost)
    (hserviceRate_pos : 0 < serviceRate)
    (_hsocial_optimal : ∀ capacity : ℕ,
      finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho capacity ≤
        finiteCapacityLinearHoldingReward (rho * serviceRate) reward queueCost rho socialCapacity)
    (htoll_lower : reward - ((socialCapacity + 1 : ℕ) : ℝ) * queueCost / serviceRate < toll)
    (htoll_upper : toll ≤ reward - (socialCapacity : ℝ) * queueCost / serviceRate) :
    Nat.floor ((reward - toll) * serviceRate / queueCost) = socialCapacity := by
  let netValue := (reward - toll) * serviceRate / queueCost
  have hcapacity_lower : (socialCapacity : ℝ) ≤ netValue := by
    apply (le_div_iff₀ hqueueCost_pos).mpr
    apply (div_le_iff₀ hserviceRate_pos).mp
    linarith
  have hcapacity_upper : netValue < ((socialCapacity + 1 : ℕ) : ℝ) := by
    apply (div_lt_iff₀ hqueueCost_pos).mpr
    apply (lt_div_iff₀ hserviceRate_pos).mp
    linarith
  apply Nat.le_antisymm
  · apply Nat.lt_succ_iff.mp
    exact (Nat.floor_lt (le_trans (by positivity) hcapacity_lower)).mpr hcapacity_upper
  · exact Nat.le_floor hcapacity_lower

end Naor1969QueueTolls
