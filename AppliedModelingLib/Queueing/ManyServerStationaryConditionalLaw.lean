import AppliedModelingLib.Queueing.ManyServerStationaryTailLaw
import AppliedModelingLib.Queueing.ManyServerPoisson
import Mathlib.Tactic

/-!
# Conditional finite-head laws for many-server queues

Exact links between the invariant stationary probability law and the
finite-head conditional masses used in many-server asymptotics.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- The probability of being strictly below full occupancy under the invariant
stationary law is the finite normalizer divided by the full normalizer. -/
theorem manyServerStationaryLaw_range_servers_toReal
    (trafficIntensity : ℝ) {servers : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Finset.range servers)).toReal =
      manyServerHeadNormalizer trafficIntensity servers /
        manyServerStationaryNormalizer trafficIntensity servers := by
  rw [manyServerStationaryLaw_range_toReal_eq_sum]
  unfold manyServerHeadNormalizer
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state hstate
  rw [manyServerStationaryMass_eq_head]
  · ring
  · exact Nat.le_of_lt (Finset.mem_range.mp hstate)

/-- The strictly-underloaded event under the invariant law has probability
one minus the all-servers-busy probability. -/
theorem manyServerStationaryLaw_range_servers_toReal_eq_one_sub_delayProbability
    (trafficIntensity : ℝ) {servers : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Finset.range servers)).toReal =
      1 - manyServerDelayProbability trafficIntensity servers := by
  rw [manyServerStationaryLaw_range_servers_toReal trafficIntensity hservers htraffic_pos
    htraffic_lt_one]
  rw [manyServerDelayProbability_eq_tailNormalizer_div_normalizer,
    manyServerStationaryNormalizer_eq_head_add_tail]
  have hnormalizer_ne :
      manyServerHeadNormalizer trafficIntensity servers +
        manyServerTailNormalizer trafficIntensity servers ≠ 0 := by
    rw [← manyServerStationaryNormalizer_eq_head_add_tail]
    exact (manyServerStationaryNormalizer_pos trafficIntensity servers
      htraffic_pos.le htraffic_lt_one).ne'
  field_simp [hnormalizer_ne]
  ring

/-- The strictly-underloaded event has positive probability in every stable
positive many-server system. -/
theorem manyServerStationaryLaw_range_servers_toReal_pos
    (trafficIntensity : ℝ) {servers : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    0 < (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
      (Finset.range servers)).toReal := by
  rw [manyServerStationaryLaw_range_servers_toReal trafficIntensity hservers htraffic_pos
    htraffic_lt_one]
  exact div_pos
    (manyServerHeadNormalizer_pos trafficIntensity hservers htraffic_pos.le)
    (manyServerStationaryNormalizer_pos trafficIntensity servers htraffic_pos.le
      htraffic_lt_one)

/-- A strictly-underloaded singleton probability conditioned on the finite
head is exactly the reusable finite-head conditional mass. -/
theorem manyServerStationaryHeadConditionalPointMass_eq_law_ratio
    (trafficIntensity : NNReal) {servers state : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (hstate : state < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadConditionalPointMass trafficIntensity servers state =
      (manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one) {state}).toReal /
        (manyServerStationaryLaw (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)
          (Finset.range servers)).toReal := by
  rw [manyServerStationaryLaw_apply_singleton_toReal,
    manyServerStationaryLaw_range_servers_toReal]
  · unfold manyServerStationaryHeadConditionalPointMass
    ring
  · exact hservers
  · exact_mod_cast htraffic_pos

/-- The conditional finite-head cumulative mass is the literal stationary-law
conditional probability of the corresponding finite initial event. -/
theorem manyServerStationaryHeadConditionalCumulativeMass_eq_law_ratio
    (trafficIntensity : NNReal) {servers cutoff : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (hcutoff : cutoff ≤ servers) (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadConditionalCumulativeMass trafficIntensity servers cutoff =
      (manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)
        (Finset.range cutoff)).toReal /
        (manyServerStationaryLaw (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)
          (Finset.range servers)).toReal := by
  rw [manyServerStationaryLaw_range_toReal_eq_sum,
    manyServerStationaryLaw_range_servers_toReal]
  · unfold manyServerStationaryHeadConditionalCumulativeMass
      manyServerStationaryHeadConditionalPointMass
    rw [← Finset.sum_div]
  · exact hservers
  · exact_mod_cast htraffic_pos

/-- A finite initial event factors into its conditional mass below full
occupancy and the probability of being strictly underloaded. -/
theorem manyServerStationaryLaw_range_toReal_eq_headConditionalCumulative_mul
    (trafficIntensity : NNReal) {servers cutoff : ℕ}
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (hcutoff : cutoff ≤ servers) (htraffic_lt_one : trafficIntensity < 1) :
    (manyServerStationaryLaw (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one)
      (Finset.range cutoff)).toReal =
      manyServerStationaryHeadConditionalCumulativeMass trafficIntensity servers cutoff *
        (manyServerStationaryLaw (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one)
          (Finset.range servers)).toReal := by
  rw [manyServerStationaryHeadConditionalCumulativeMass_eq_law_ratio
    trafficIntensity hservers htraffic_pos hcutoff htraffic_lt_one]
  have hhead_ne :
      (manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)
        (Finset.range servers)).toReal ≠ 0 := by
    exact (manyServerStationaryLaw_range_servers_toReal_pos
      (trafficIntensity : ℝ) hservers (by positivity)
      (by exact_mod_cast htraffic_lt_one)).ne'
  field_simp [hhead_ne]

/-- The delayed stationary tail conditional on full occupancy is the literal
conditional probability of the corresponding upper-tail event under the
invariant stationary law. -/
theorem manyServerStationaryDelayedTailConditionalMass_eq_law_ratio
    (trafficIntensity : ℝ) (servers tail : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedTailConditionalMass trafficIntensity servers tail =
      (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
        (Set.Ici (tail + servers))).toReal /
        (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
          (Set.Ici servers)).toReal := by
  unfold manyServerStationaryDelayedTailConditionalMass
  rw [manyServerStationaryLaw_Ici_add_toReal_eq_delayedTailMass
      trafficIntensity servers tail hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryLaw_Ici_toReal_eq_delayProbability
      trafficIntensity hservers htraffic_pos htraffic_lt_one]

/-- The delayed singleton conditional mass is the literal conditional
probability of that queue length given full occupancy under the invariant
stationary law. -/
theorem manyServerStationaryDelayedPointConditionalMass_eq_law_ratio
    (trafficIntensity : ℝ) (servers tail : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedPointConditionalMass trafficIntensity servers tail =
      (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
        {tail + servers}).toReal /
        (manyServerStationaryLaw trafficIntensity servers htraffic_pos.le htraffic_lt_one
          (Set.Ici servers)).toReal := by
  unfold manyServerStationaryDelayedPointConditionalMass
  rw [manyServerStationaryLaw_apply_singleton_toReal,
    manyServerStationaryLaw_Ici_toReal_eq_delayProbability
      trafficIntensity hservers htraffic_pos htraffic_lt_one]

end AppliedModelingLib.Probability.Queueing
