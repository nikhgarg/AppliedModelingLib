import AppliedModelingLib.Queueing.ManyServerBirthDeath
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Tactic

/-!
# Poisson representations for many-server normalizers

This module relates the factorial and geometric normalizers of a many-server
queue to finite lower tails and point masses of the Poisson distribution.  The
identities are exact and leave asymptotic normal and local-limit estimates as
separate results.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped ENNReal NNReal
open ProbabilityTheory

/-- The probability that a Poisson variable lies strictly below a natural
cutoff, represented as a finite real sum. -/
noncomputable def poissonLowerTailProbability (mean : ℝ≥0) (cutoff : ℕ) : ℝ :=
  ∑ state ∈ Finset.range cutoff, (poissonMeasure mean).real {state}

/-- The point probability of a Poisson variable at a natural state. -/
noncomputable def poissonPointProbability (mean : ℝ≥0) (state : ℕ) : ℝ :=
  (poissonMeasure mean).real {state}

/-- Finite Poisson lower tails expand into the usual exponential/factorial
series. -/
theorem poissonLowerTailProbability_eq
    (mean : ℝ≥0) (cutoff : ℕ) :
    poissonLowerTailProbability mean cutoff =
      ∑ state ∈ Finset.range cutoff,
        Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ state / (state.factorial : ℝ) := by
  unfold poissonLowerTailProbability
  simp_rw [poissonMeasure_real_singleton]

/-- The finite lower-tail sum is the real measure of the corresponding
strict-integer lower-tail event. -/
theorem poissonLowerTailProbability_eq_measureReal_Iio
    (mean : ℝ≥0) (cutoff : ℕ) :
    poissonLowerTailProbability mean cutoff =
      (poissonMeasure mean).real (Set.Iio cutoff) := by
  unfold poissonLowerTailProbability
  rw [MeasureTheory.sum_measureReal_singleton (μ := poissonMeasure mean)]
  congr 1
  ext state
  simp

/-- A Poisson point probability expands into the usual exponential/factorial
term. -/
theorem poissonPointProbability_eq
    (mean : ℝ≥0) (state : ℕ) :
    poissonPointProbability mean state =
      Real.exp (-(mean : ℝ)) * (mean : ℝ) ^ state / (state.factorial : ℝ) := by
  unfold poissonPointProbability
  rw [poissonMeasure_real_singleton]

/-- The factorial part of the many-server normalizer is an exponential tilt
of the lower Poisson tail. -/
theorem manyServerHeadNormalizer_eq_exp_mul_poissonLowerTail
    (trafficIntensity : ℝ≥0) (servers : ℕ) :
    manyServerHeadNormalizer (trafficIntensity : ℝ) servers =
      Real.exp ((servers : ℝ) * trafficIntensity) *
        poissonLowerTailProbability (servers * trafficIntensity) servers := by
  unfold manyServerHeadNormalizer poissonLowerTailProbability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro state hstate
  rw [poissonMeasure_real_singleton]
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  have hexp : Real.exp ((servers : ℝ) * trafficIntensity) *
      Real.exp (-((servers : ℝ) * trafficIntensity)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) =
        1 * (((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)) := by ring
    _ = (Real.exp ((servers : ℝ) * trafficIntensity) *
        Real.exp (-((servers : ℝ) * trafficIntensity))) *
          (((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)) := by rw [hexp]
    _ = Real.exp ((servers : ℝ) * trafficIntensity) *
        (Real.exp (-((servers : ℝ) * trafficIntensity)) *
          ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)) := by ring

/-- The full-occupancy factorial weight is an exponential tilt of the
corresponding Poisson point probability. -/
theorem manyServerFullOccupancyWeight_eq_exp_mul_poissonPoint
    (trafficIntensity : ℝ≥0) (servers : ℕ) :
    manyServerFullOccupancyWeight (trafficIntensity : ℝ) servers =
      Real.exp ((servers : ℝ) * trafficIntensity) *
        poissonPointProbability (servers * trafficIntensity) servers := by
  unfold manyServerFullOccupancyWeight poissonPointProbability
  rw [poissonMeasure_real_singleton]
  simp only [NNReal.coe_mul]
  have hexp : Real.exp ((servers : ℝ) * trafficIntensity) *
      Real.exp (-((servers : ℝ) * trafficIntensity)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    ((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ) =
        1 * (((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ)) := by ring
    _ = (Real.exp ((servers : ℝ) * trafficIntensity) *
        Real.exp (-((servers : ℝ) * trafficIntensity))) *
          (((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ)) := by rw [hexp]
    _ = Real.exp ((servers : ℝ) * trafficIntensity) *
        (Real.exp (-((servers : ℝ) * trafficIntensity)) *
          ((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ)) := by ring

/-- The geometric-tail contribution is an exponential tilt of the Poisson
point probability divided by spare capacity. -/
theorem manyServerTailNormalizer_eq_exp_mul_poissonPoint_div
    (trafficIntensity : ℝ≥0) (servers : ℕ) :
    manyServerTailNormalizer (trafficIntensity : ℝ) servers =
      Real.exp ((servers : ℝ) * trafficIntensity) *
        poissonPointProbability (servers * trafficIntensity) servers /
          (1 - (trafficIntensity : ℝ)) := by
  rw [manyServerTailNormalizer, manyServerFullOccupancyWeight_eq_exp_mul_poissonPoint]

/-- In the stable regime, Erlang-C is the exact ratio of a Poisson point mass
to that point mass plus the spare-capacity-scaled lower tail. -/
theorem manyServerDelayProbability_eq_poissonRatio
    (trafficIntensity : ℝ≥0) (servers : ℕ)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerDelayProbability (trafficIntensity : ℝ) servers =
      poissonPointProbability (servers * trafficIntensity) servers /
        ((1 - (trafficIntensity : ℝ)) *
          poissonLowerTailProbability (servers * trafficIntensity) servers +
          poissonPointProbability (servers * trafficIntensity) servers) := by
  rw [manyServerDelayProbability_eq_tailNormalizer_div_normalizer,
    manyServerStationaryNormalizer_eq_head_add_tail,
    manyServerHeadNormalizer_eq_exp_mul_poissonLowerTail,
    manyServerTailNormalizer_eq_exp_mul_poissonPoint_div]
  have hgap_pos : 0 < 1 - (trafficIntensity : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast htraffic_lt_one)
  have hgap_ne : 1 - (trafficIntensity : ℝ) ≠ 0 := ne_of_gt hgap_pos
  have hexp_ne : Real.exp ((servers : ℝ) * trafficIntensity) ≠ 0 :=
    (Real.exp_pos _).ne'
  field_simp [hgap_ne, hexp_ne]

/-- The finite-state conditional mass below full occupancy, expressed through
the stationary factorial weights. -/
noncomputable def manyServerStationaryHeadConditionalPointMass
    (trafficIntensity : ℝ≥0) (servers state : ℕ) : ℝ :=
  manyServerStationaryMass (trafficIntensity : ℝ) servers state /
    (manyServerHeadNormalizer (trafficIntensity : ℝ) servers /
      manyServerStationaryNormalizer (trafficIntensity : ℝ) servers)

/-- Below full occupancy, conditioning the stationary factorial branch on
the finite head is exactly Poisson conditioning on the corresponding lower
tail. -/
theorem manyServerStationaryHeadConditionalPointMass_eq_poissonRatio
    (trafficIntensity : ℝ≥0) {servers state : ℕ}
    (hservers : 0 < servers) (hstate : state < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadConditionalPointMass trafficIntensity servers state =
      poissonPointProbability (servers * trafficIntensity) state /
        poissonLowerTailProbability (servers * trafficIntensity) servers := by
  have htraffic_nonneg : 0 ≤ (trafficIntensity : ℝ) := NNReal.zero_le_coe
  have htraffic_lt_one_real : (trafficIntensity : ℝ) < 1 := by
    exact_mod_cast htraffic_lt_one
  have hnormalizer_ne :
      manyServerStationaryNormalizer (trafficIntensity : ℝ) servers ≠ 0 :=
    (manyServerStationaryNormalizer_pos (trafficIntensity : ℝ) servers
      htraffic_nonneg htraffic_lt_one_real).ne'
  have hhead_pos : 0 < manyServerHeadNormalizer (trafficIntensity : ℝ) servers :=
    manyServerHeadNormalizer_pos (trafficIntensity : ℝ) hservers htraffic_nonneg
  have hlower_pos : 0 <
      poissonLowerTailProbability (servers * trafficIntensity) servers := by
    rw [manyServerHeadNormalizer_eq_exp_mul_poissonLowerTail] at hhead_pos
    exact pos_of_mul_pos_left (by simpa [mul_comm] using hhead_pos) (Real.exp_pos _).le
  have hlower_ne :
      poissonLowerTailProbability (servers * trafficIntensity) servers ≠ 0 :=
    ne_of_gt hlower_pos
  unfold manyServerStationaryHeadConditionalPointMass
  rw [manyServerStationaryMass_eq_head (trafficIntensity : ℝ) (Nat.le_of_lt hstate),
    manyServerHeadNormalizer_eq_exp_mul_poissonLowerTail,
    poissonPointProbability_eq]
  simp only [NNReal.coe_mul, NNReal.coe_natCast]
  have hexp : Real.exp ((servers : ℝ) * (trafficIntensity : ℝ)) *
      Real.exp (-((servers : ℝ) * (trafficIntensity : ℝ))) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  field_simp [hnormalizer_ne, hlower_ne, Real.exp_ne_zero]
  rw [mul_assoc, hexp]
  ring

/-- The finite cumulative mass below full occupancy, normalized by the
underloaded stationary head. -/
noncomputable def manyServerStationaryHeadConditionalCumulativeMass
    (trafficIntensity : ℝ≥0) (servers cutoff : ℕ) : ℝ :=
  ∑ state ∈ Finset.range cutoff,
    manyServerStationaryHeadConditionalPointMass trafficIntensity servers state

/-- Conditional stationary cumulative masses below full occupancy are exactly
the corresponding Poisson lower-tail ratios. -/
theorem manyServerStationaryHeadConditionalCumulativeMass_eq_poissonRatio
    (trafficIntensity : ℝ≥0) {servers cutoff : ℕ}
    (hservers : 0 < servers) (hcutoff : cutoff ≤ servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadConditionalCumulativeMass trafficIntensity servers cutoff =
      poissonLowerTailProbability (servers * trafficIntensity) cutoff /
        poissonLowerTailProbability (servers * trafficIntensity) servers := by
  unfold manyServerStationaryHeadConditionalCumulativeMass
  calc
    ∑ state ∈ Finset.range cutoff,
        manyServerStationaryHeadConditionalPointMass trafficIntensity servers state =
      ∑ state ∈ Finset.range cutoff,
        poissonPointProbability (servers * trafficIntensity) state /
          poissonLowerTailProbability (servers * trafficIntensity) servers := by
        apply Finset.sum_congr rfl
        intro state hstate
        apply manyServerStationaryHeadConditionalPointMass_eq_poissonRatio
        · exact hservers
        · exact lt_of_lt_of_le (Finset.mem_range.mp hstate) hcutoff
        · exact htraffic_lt_one
    _ = (∑ state ∈ Finset.range cutoff,
        poissonPointProbability (servers * trafficIntensity) state) /
          poissonLowerTailProbability (servers * trafficIntensity) servers := by
      rw [Finset.sum_div]
    _ = poissonLowerTailProbability (servers * trafficIntensity) cutoff /
        poissonLowerTailProbability (servers * trafficIntensity) servers := by
      rfl

end AppliedModelingLib.Probability.Queueing
