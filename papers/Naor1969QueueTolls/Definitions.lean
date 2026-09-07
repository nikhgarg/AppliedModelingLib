import AppliedModelingLib.Queueing.FiniteCapacity

/-!
# Source-facing definitions for Naor (1969)

These definitions preserve the paper's finite-threshold M/M/1 notation.  The
corresponding reusable queueing APIs are proved equivalent below so the paper
interface can display the source formulas without duplicating infrastructure.
-/

namespace Naor1969QueueTolls

open AppliedModelingLib Probability
open AppliedModelingLib.Probability.Queueing

/-- The dimensionless arrival-to-service ratio denoted by `p` in the source. -/
noncomputable def trafficIntensity (arrivalRate serviceRate : ℝ) : ℝ :=
  arrivalRate / serviceRate

/-- The source paper's stationary probability of observing `state` customers
under a finite admission threshold. -/
noncomputable def stationaryProbability
    (rho : ℝ) (threshold state : ℕ) : ℝ :=
  if state ≤ threshold then
    rho ^ state /
      ∑ i ∈ Finset.range (threshold + 1), rho ^ i
  else 0

/-- The source paper's stationary expected queue size. -/
noncomputable def expectedQueueSize (rho : ℝ) (threshold : ℕ) : ℝ :=
  (∑ state ∈ Finset.range (threshold + 1), (state : ℝ) * rho ^ state) /
    ∑ state ∈ Finset.range (threshold + 1), rho ^ state

/-- Equation (5): the probability generating function of the stationary queue
length under a finite admission threshold. -/
noncomputable def stationaryGeneratingFunction
    (rho z : ℝ) (threshold : ℕ) : ℝ :=
  ∑ state ∈ Finset.range (threshold + 1),
    stationaryProbability rho threshold state * z ^ state

/-- The expected number of arrivals diverted per unit time at a finite
threshold, corresponding to the source's equation (7). -/
noncomputable def divertedArrivalRate
    (arrivalRate rho : ℝ) (threshold : ℕ) : ℝ :=
  arrivalRate * stationaryProbability rho threshold threshold

/-- The stationary busy fraction, corresponding to the source's equation (8). -/
noncomputable def busyFraction (rho : ℝ) (threshold : ℕ) : ℝ :=
  1 - stationaryProbability rho threshold 0

/-- The stationary admitted arrival flow, corresponding to the source's
equation (9). -/
noncomputable def admittedArrivalRate
    (arrivalRate rho : ℝ) (threshold : ℕ) : ℝ :=
  arrivalRate * (1 - stationaryProbability rho threshold threshold)

/-- A customer's net gain from joining when `queueLength` customers are
already present. -/
noncomputable def joiningGain
    (reward queueCost serviceRate : ℝ) (queueLength : ℕ) : ℝ :=
  reward - ((queueLength + 1 : ℕ) : ℝ) * queueCost / serviceRate

/-- The dimensionless service value used for all three threshold comparisons. -/
noncomputable def serviceValue (reward queueCost serviceRate : ℝ) : ℝ :=
  reward * serviceRate / queueCost

/-- The fee that makes a visible queue length `threshold` the first rejected
state under the source paper's convention. -/
noncomputable def thresholdFee
    (reward queueCost serviceRate : ℝ) (threshold : ℕ) : ℝ :=
  reward - (threshold : ℝ) * queueCost / serviceRate

/-- Equation (17): steady-state aggregate reward less queueing cost under a
finite admission threshold. -/
noncomputable def socialWelfare
    (arrivalRate reward queueCost rho : ℝ) (threshold : ℕ) : ℝ :=
  reward * arrivalRate * (1 - stationaryProbability rho threshold threshold) -
    queueCost * expectedQueueSize rho threshold

/-- Equation (27): toll revenue when the threshold is implemented by its
corresponding admission fee. -/
noncomputable def tollRevenue
    (arrivalRate reward queueCost serviceRate rho : ℝ) (threshold : ℕ) : ℝ :=
  arrivalRate * (1 - stationaryProbability rho threshold threshold) *
    thresholdFee reward queueCost serviceRate threshold

/-- The customers' aggregate income after an admission toll is paid. -/
noncomputable def customerIncomeAfterToll
    (arrivalRate reward queueCost toll rho : ℝ) (threshold : ℕ) : ℝ :=
  socialWelfare arrivalRate reward queueCost rho threshold -
    toll * admittedArrivalRate arrivalRate rho threshold

/-- The combined income of customers and the toll collector.  Equation (26)
uses this transfer-inclusive quantity when it says that the toll implements a
socially optimal threshold. -/
noncomputable def combinedIncomeAfterToll
    (arrivalRate reward queueCost toll rho : ℝ) (threshold : ℕ) : ℝ :=
  customerIncomeAfterToll arrivalRate reward queueCost toll rho threshold +
    toll * admittedArrivalRate arrivalRate rho threshold

/-- The source stationary formula is the reusable finite-capacity geometric
mass, including its well-defined traffic-intensity-one case. -/
theorem stationaryProbability_eq_finiteCapacityGeometricMass
    (rho : ℝ) (threshold state : ℕ) :
    stationaryProbability rho threshold state =
      finiteCapacityGeometricMass rho threshold state := by
  rfl

/-- The source expected queue-size formula is the reusable finite-capacity
stationary expectation. -/
theorem expectedQueueSize_eq_finiteCapacityExpectedState
    (rho : ℝ) (threshold : ℕ) :
    expectedQueueSize rho threshold = finiteCapacityExpectedState rho threshold := by
  rfl

/-- The source probability generating function is the finite geometric
normalizer ratio, with no singular special case at traffic intensity one. -/
theorem stationaryGeneratingFunction_eq_normalizer_ratio
    (rho z : ℝ) (threshold : ℕ) :
    stationaryGeneratingFunction rho z threshold =
      finiteCapacityGeometricNormalizer (rho * z) threshold /
        finiteCapacityGeometricNormalizer rho threshold := by
  change finiteCapacityGeometricProbabilityGeneratingFunction rho z threshold = _
  exact finiteCapacityGeometricProbabilityGeneratingFunction_eq_normalizer_ratio rho z threshold

/-- The source diversion formula is the generic finite-capacity rejected
arrival rate. -/
theorem divertedArrivalRate_eq_finiteCapacityRejectedArrivalRate
    (arrivalRate rho : ℝ) (threshold : ℕ) :
    divertedArrivalRate arrivalRate rho threshold =
      finiteCapacityRejectedArrivalRate arrivalRate rho threshold := by
  rfl

/-- The source busy fraction is the generic finite-capacity busy fraction. -/
theorem busyFraction_eq_finiteCapacityBusyFraction (rho : ℝ) (threshold : ℕ) :
    busyFraction rho threshold = finiteCapacityBusyFraction rho threshold := by
  rfl

/-- The source admitted-arrival formula is the generic finite-capacity
admission rate. -/
theorem admittedArrivalRate_eq_finiteCapacityAdmittedArrivalRate
    (arrivalRate rho : ℝ) (threshold : ℕ) :
    admittedArrivalRate arrivalRate rho threshold =
      finiteCapacityAdmittedArrivalRate arrivalRate rho threshold := by
  rfl

/-- The source's stationary flow equality: admitted arrivals equal completed
services. -/
theorem admittedArrivalRate_eq_serviceRate_mul_busyFraction
    {rho serviceRate : ℝ} (hrho_nonneg : 0 ≤ rho) (threshold : ℕ) :
    admittedArrivalRate (rho * serviceRate) rho threshold =
      serviceRate * busyFraction rho threshold := by
  simpa only [admittedArrivalRate_eq_finiteCapacityAdmittedArrivalRate,
    busyFraction_eq_finiteCapacityBusyFraction] using
    finiteCapacity_admittedArrivalRate_eq_serviceRate_mul_busyFraction hrho_nonneg threshold

/-- For a nonzero threshold, the source's equation (11) recovers traffic
intensity as busy fraction divided by the probability an arrival is admitted. -/
theorem busyFraction_div_admissionProbability_eq_trafficIntensity
    {rho : ℝ} (hrho_pos : 0 < rho) (threshold : ℕ) (hthreshold_pos : 0 < threshold) :
    busyFraction rho threshold /
        (1 - stationaryProbability rho threshold threshold) = rho := by
  simpa only [stationaryProbability_eq_finiteCapacityGeometricMass,
    busyFraction_eq_finiteCapacityBusyFraction] using
    finiteCapacity_busyFraction_div_admissionProbability_eq_rho hrho_pos threshold hthreshold_pos

/-- The source aggregate welfare formula agrees with the generic
reward-minus-holding-cost objective. -/
theorem socialWelfare_eq_finiteCapacityLinearHoldingReward
    (arrivalRate reward queueCost rho : ℝ) (threshold : ℕ) :
    socialWelfare arrivalRate reward queueCost rho threshold =
      finiteCapacityLinearHoldingReward arrivalRate reward queueCost rho threshold := by
  simp [socialWelfare, finiteCapacityLinearHoldingReward,
    finiteCapacityAdmittedArrivalRate, stationaryProbability,
    expectedQueueSize, finiteCapacityGeometricMass, finiteCapacityExpectedState,
    finiteCapacityGeometricNormalizer, finiteCapacityWeightedGeometricSum]
  ring

/-- The source toll-revenue formula agrees with the generic admission-revenue
objective. -/
theorem tollRevenue_eq_finiteCapacityAdmissionRevenue
    (arrivalRate reward queueCost serviceRate rho : ℝ) (threshold : ℕ) :
    tollRevenue arrivalRate reward queueCost serviceRate rho threshold =
      finiteCapacityAdmissionRevenue arrivalRate
        (thresholdFee reward queueCost serviceRate threshold) rho threshold := by
  simp [tollRevenue, finiteCapacityAdmissionRevenue,
    finiteCapacityAdmittedArrivalRate, stationaryProbability,
    finiteCapacityGeometricMass, finiteCapacityGeometricNormalizer]
  ring

/-- A toll is a transfer: after including its revenue, the combined income is
exactly the paper's social-welfare objective. -/
theorem combinedIncomeAfterToll_eq_socialWelfare
    (arrivalRate reward queueCost toll rho : ℝ) (threshold : ℕ) :
    combinedIncomeAfterToll arrivalRate reward queueCost toll rho threshold =
      socialWelfare arrivalRate reward queueCost rho threshold := by
  simp only [combinedIncomeAfterToll, customerIncomeAfterToll]
  ring

end Naor1969QueueTolls
