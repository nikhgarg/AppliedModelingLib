import AppliedModelingLib.Queueing.ManyServerStationaryLaw
import AppliedModelingLib.Foundations.Math.NatTailSums
import Mathlib.Tactic

/-!
# Tail events under the many-server stationary law

This module connects the offset-indexed stationary geometric tail to the
probability of the all-servers-busy event under the invariant PMF law.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- A finite initial segment under the invariant stationary law has the
corresponding finite sum of normalized M/M/s masses. -/
theorem manyServerStationaryLaw_range_toReal_eq_sum
    (trafficIntensity : ℝ) (servers cutoff : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_nonneg htraffic_lt_one
      (Finset.range cutoff)).toReal =
      ∑ state ∈ Finset.range cutoff,
        manyServerStationaryMass trafficIntensity servers state := by
  unfold manyServerStationaryLaw
  rw [PMF.toMeasure_apply_finset]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro state hstate
    exact manyServerStationaryPMF_toReal
      trafficIntensity servers htraffic_nonneg htraffic_lt_one state
  · intro state _
    exact PMF.apply_ne_top _ _

/-- Under the invariant many-server stationary law, the event that all servers
are occupied has exactly the Erlang-C delay probability. -/
theorem manyServerStationaryLaw_Ici_eq_delayProbability
    (trafficIntensity : ℝ) {servers : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Set.Ici servers) =
      ENNReal.ofReal (manyServerDelayProbability trafficIntensity servers) := by
  let pmf := manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one
  let delay : NNReal := ⟨manyServerDelayProbability trafficIntensity servers,
    (manyServerDelayProbability_pos servers htraffic_pos htraffic_lt_one).le⟩
  have htailReal := hasSum_manyServerStationaryMass_delayedTail
    trafficIntensity servers htraffic_pos.le htraffic_lt_one
  have htailIndicatorReal : HasSum
      (fun state : ℕ => if servers ≤ state then
        manyServerStationaryMass trafficIntensity servers state else 0)
      (manyServerDelayProbability trafficIntensity servers) := by
    exact AppliedModelingLib.hasSum_nat_Ici_indicator_of_hasSum_shift htailReal
  have htailIndicatorNN : HasSum
      (fun state : ℕ => if servers ≤ state then
        manyServerStationaryMassNN trafficIntensity servers
          htraffic_pos.le htraffic_lt_one state else 0) delay := by
    apply NNReal.hasSum_coe.mp
    convert htailIndicatorReal using 1
    · ext state
      by_cases hstate : servers ≤ state
      · simp [hstate]
        rfl
      · simp [hstate]
  have htailIndicator : HasSum
      (fun state : ℕ => if servers ≤ state then pmf state else 0)
      (delay : ENNReal) := by
    convert ENNReal.hasSum_coe.mpr htailIndicatorNN using 1
    · ext state
      by_cases hstate : servers ≤ state
      · simp [hstate]
        rfl
      · simp [hstate]
  unfold manyServerStationaryLaw
  rw [PMF.toMeasure_apply _ measurableSet_Ici]
  have hdelay : ENNReal.ofReal (manyServerDelayProbability trafficIntensity servers) =
      (delay : ENNReal) := by
    change ENNReal.ofReal (↑delay : ℝ) = (delay : ENNReal)
    exact (ENNReal.coe_nnreal_eq delay).symm
  rw [hdelay]
  simpa [pmf, Set.indicator] using htailIndicator.tsum_eq

/-- The real-valued version of the stationary all-servers-busy identity. -/
theorem manyServerStationaryLaw_Ici_toReal_eq_delayProbability
    (trafficIntensity : ℝ) {servers : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Set.Ici servers)).toReal =
      manyServerDelayProbability trafficIntensity servers := by
  rw [manyServerStationaryLaw_Ici_eq_delayProbability
    trafficIntensity hservers htraffic_pos htraffic_lt_one]
  exact ENNReal.toReal_ofReal
    (manyServerDelayProbability_pos servers htraffic_pos htraffic_lt_one).le

/-- A delayed upper-tail event under the invariant stationary law is the
corresponding shifted stationary tail mass. -/
theorem manyServerStationaryLaw_Ici_add_toReal_eq_delayedTailMass
    (trafficIntensity : ℝ) (servers tail : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Set.Ici (tail + servers))).toReal =
      manyServerStationaryDelayedTailMass trafficIntensity servers tail := by
  let pmf := manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one
  have htailMass : manyServerStationaryDelayedTailMass trafficIntensity servers tail =
      trafficIntensity ^ tail * manyServerDelayProbability trafficIntensity servers := by
    rw [manyServerStationaryDelayedTailMass_eq]
    · exact htraffic_pos.le
    · exact htraffic_lt_one
  let tailMass : NNReal := ⟨manyServerStationaryDelayedTailMass trafficIntensity servers tail,
    by
      rw [htailMass]
      exact mul_nonneg (pow_nonneg htraffic_pos.le _)
        (manyServerDelayProbability_pos servers htraffic_pos htraffic_lt_one).le⟩
  have htailReal := hasSum_manyServerStationaryMass_delayedTail_shift
    trafficIntensity servers tail htraffic_pos.le htraffic_lt_one
  have htailIndicatorReal : HasSum
      (fun state : ℕ => if tail + servers ≤ state then
        manyServerStationaryMass trafficIntensity servers state else 0)
      (manyServerStationaryDelayedTailMass trafficIntensity servers tail) := by
    rw [htailMass]
    apply AppliedModelingLib.hasSum_nat_Ici_indicator_of_hasSum_shift
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htailReal
  have htailIndicatorNN : HasSum
      (fun state : ℕ => if tail + servers ≤ state then
        manyServerStationaryMassNN trafficIntensity servers
          htraffic_pos.le htraffic_lt_one state else 0) tailMass := by
    apply NNReal.hasSum_coe.mp
    convert htailIndicatorReal using 1
    · ext state
      by_cases hstate : tail + servers ≤ state
      · simp [hstate]
        rfl
      · simp [hstate]
  have htailIndicator : HasSum
      (fun state : ℕ => if tail + servers ≤ state then pmf state else 0)
      (tailMass : ENNReal) := by
    convert ENNReal.hasSum_coe.mpr htailIndicatorNN using 1
    · ext state
      by_cases hstate : tail + servers ≤ state
      · simp [hstate]
        rfl
      · simp [hstate]
  unfold manyServerStationaryLaw
  rw [PMF.toMeasure_apply _ measurableSet_Ici]
  have hsum : ∑' state : ℕ,
      (Set.Ici (tail + servers)).indicator pmf state = (tailMass : ENNReal) := by
    simpa [Set.indicator] using htailIndicator.tsum_eq
  rw [hsum]
  exact ENNReal.coe_toReal tailMass

end AppliedModelingLib.Probability.Queueing
