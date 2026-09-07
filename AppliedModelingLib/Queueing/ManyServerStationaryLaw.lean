import AppliedModelingLib.Queueing.ManyServerTrajectory
import Mathlib.Tactic

/-!
# Stationary law of the uniformized many-server queue

This module names the probability measure induced by the normalized
many-server PMF and connects its point probabilities to the real stationary
masses.  The law is invariant for the checked potential-event Markov kernel.
It is a stationary-law layer for static queue-length statements; constructing a
continuous-time càdlàg semigroup remains separate.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The probability law on queue lengths associated with the normalized
many-server stationary PMF. -/
noncomputable def manyServerStationaryLaw
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    Measure ℕ :=
  (manyServerStationaryPMF trafficIntensity servers htraffic_nonneg htraffic_lt_one).toMeasure

/-- The named many-server stationary law is invariant for the checked
uniformized potential-event kernel. -/
theorem manyServerStationaryLaw_uniformized_invariant
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    Kernel.Invariant
      (countablePMFKernel
        (manyServerUniformizedKernel trafficIntensity servers hservers))
      (manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)) := by
  exact manyServer_uniformized_kernelInvariant
    trafficIntensity servers hservers htraffic_lt_one

/-- A singleton probability under the stationary law is the corresponding
PMF mass. -/
theorem manyServerStationaryLaw_apply_singleton
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (state : ℕ) :
    manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one {state} =
      manyServerStationaryPMF trafficIntensity servers htraffic_nonneg htraffic_lt_one state := by
  unfold manyServerStationaryLaw
  exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)

/-- The real singleton probability under the stationary law is the normalized
factorial/geometric mass used in the queueing algebra. -/
theorem manyServerStationaryLaw_apply_singleton_toReal
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (state : ℕ) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one {state}).toReal =
      manyServerStationaryMass trafficIntensity servers state := by
  rw [manyServerStationaryLaw_apply_singleton]
  exact manyServerStationaryPMF_toReal
    trafficIntensity servers htraffic_nonneg htraffic_lt_one state

end AppliedModelingLib.Probability.Queueing
