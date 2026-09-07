import Naor1969QueueTolls.PaperInterface
import Naor1969QueueTolls.MainTheorems

/-!
# Proof Interface: The Regulation of Queue Size by Levying Tolls

This file contains exact-type proof endpoints for the transparent propositions
in `PaperInterface.lean`. It is not a human semantic-review surface: one source
claim is reviewed once, against its expanded `...Spec : Prop` declaration.
-/

namespace Naor1969QueueTolls

/--
Lean proof endpoint for `finiteCapacityStationaryLawSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem finiteCapacityStationaryLaw :
  finiteCapacityStationaryLawSpec := by
  intro rho serviceRate capacity hrho_pos _hserviceRate_pos
  simpa only [stationaryProbability_eq_finiteCapacityGeometricMass] using
    finiteCapacityStationaryLaw_impl rho serviceRate capacity hrho_pos.le

/-- Lean proof endpoint for `stationaryPerformanceSpec`. -/
theorem stationaryPerformance :
  stationaryPerformanceSpec := by
  intro rho serviceRate z capacity hrho_nonneg _hserviceRate_pos
  exact stationaryPerformance_impl rho serviceRate z capacity hrho_nonneg

/--
Lean proof endpoint for `selfOptimizingThresholdSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem selfOptimizingThreshold :
  selfOptimizingThresholdSpec := by
  intro reward queueCost serviceRate hqueueCost_pos hserviceRate_pos hvalue_gt_one
  exact selfOptimizingThreshold_impl reward queueCost serviceRate hqueueCost_pos
    hserviceRate_pos hvalue_gt_one.le

/--
Lean proof endpoint for `socialOptimalThresholdSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem socialOptimalThreshold :
  socialOptimalThresholdSpec := by
  unfold socialOptimalThresholdSpec
  intro rho reward queueCost serviceRate hrho_pos hqueueCost_pos hserviceRate_pos hvalue_gt_one
  obtain ⟨socialCapacity, hmax, hbound⟩ :=
    socialOptimalThreshold_exists_impl rho reward queueCost serviceRate hrho_pos.le
      hqueueCost_pos hserviceRate_pos hvalue_gt_one.le
  refine ⟨socialCapacity, ?_, ?_⟩
  · intro capacity
    simpa only [socialWelfare_eq_finiteCapacityLinearHoldingReward] using hmax capacity
  · simpa only [serviceValue] using hbound

/--
Lean proof endpoint for `socialAndRevenueThresholdOrderSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem socialAndRevenueThresholdOrder :
  socialAndRevenueThresholdOrderSpec := by
  unfold socialAndRevenueThresholdOrderSpec
  intro rho reward queueCost serviceRate hrho_pos hqueueCost_pos hserviceRate_pos hvalue_gt_one
  simpa only [serviceValue,
    tollRevenue_eq_finiteCapacityAdmissionRevenue,
    socialWelfare_eq_finiteCapacityLinearHoldingReward] using
    socialAndRevenueThresholdOrder_impl rho reward queueCost serviceRate hrho_pos.le
      hqueueCost_pos hserviceRate_pos hvalue_gt_one.le

/--
Lean proof endpoint for `socialTollImplementsOptimalThresholdSpec`.

This theorem is intentionally outside `PaperInterface.lean`: Lean Meta checks
that it has exactly the transparent Spec type, while source-to-Lean semantic
review compares the raw source bundle only to that Spec.
-/
theorem socialTollImplementsOptimalThreshold :
  socialTollImplementsOptimalThresholdSpec := by
  unfold socialTollImplementsOptimalThresholdSpec
  intro rho reward queueCost serviceRate toll socialCapacity hrho_pos hqueueCost_pos
    hserviceRate_pos _hvalue_meaningful hsocial_optimal htoll_lower htoll_upper
  constructor
  · intro capacity
    rw [combinedIncomeAfterToll_eq_socialWelfare,
      combinedIncomeAfterToll_eq_socialWelfare]
    exact hsocial_optimal capacity
  · apply socialTollImplementsOptimalThreshold_impl rho reward queueCost serviceRate toll
      socialCapacity hrho_pos.le hqueueCost_pos hserviceRate_pos
    · intro capacity
      simpa only [socialWelfare_eq_finiteCapacityLinearHoldingReward] using
        hsocial_optimal capacity
    · simpa only [joiningGain] using htoll_lower
    · simpa only [thresholdFee] using htoll_upper

end Naor1969QueueTolls
