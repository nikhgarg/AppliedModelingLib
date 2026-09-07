import AppliedModelingLib.Queueing.MM1.Stationary
import Mathlib.Tactic

/-!
# Many-server birth--death queues

This module provides the source-neutral stationary algebra for a queue with a
constant arrival rate and a pool of identical exponential servers.  It is
stated at the generator-balance level: construction of a continuous-time
Markov process and identification of this law with a path-space stationary
distribution are separate results.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open scoped ENNReal NNReal

/-- Birth and death rates for a queue with `servers` identical servers.  At
state `q`, exactly `min q servers` servers are occupied. -/
def manyServerBirthDeathRates
    (arrivalRate serviceRate : ℝ) (servers : ℕ) : BirthDeathRates where
  birth := fun _ => arrivalRate
  death := fun state => serviceRate * (Nat.min state servers : ℝ)
  death_zero := by simp

/-- The unnormalized product-form mass of a many-server queue at offered load
`offeredLoad`.  Each factor is the arrival-to-total-service ratio across one
birth--death edge. -/
noncomputable def manyServerRelativeMass (offeredLoad : ℝ) (servers : ℕ) : ℕ → ℝ
  | 0 => 1
  | state + 1 =>
      manyServerRelativeMass offeredLoad servers state *
        (offeredLoad / (Nat.min (state + 1) servers : ℝ))

/-- Appending one state multiplies the relative mass by the corresponding
arrival-to-service ratio. -/
theorem manyServerRelativeMass_succ
    (offeredLoad : ℝ) (servers state : ℕ) :
    manyServerRelativeMass offeredLoad servers (state + 1) =
      manyServerRelativeMass offeredLoad servers state *
        (offeredLoad / (Nat.min (state + 1) servers : ℝ)) := by
  rfl

/-- The total service multiplicity on every positive edge is nonzero whenever
the server pool is nonempty. -/
theorem manyServer_min_succ_pos
    {servers state : ℕ} (hservers : 0 < servers) :
    0 < (Nat.min (state + 1) servers : ℝ) := by
  exact_mod_cast Nat.lt_min.mpr ⟨Nat.succ_pos state, hservers⟩

/-- The product-form masses satisfy detailed balance when the arrival rate is
`offeredLoad * serviceRate`. -/
theorem manyServerRelativeMass_detailedBalance
    (offeredLoad serviceRate : ℝ) {servers : ℕ} (hservers : 0 < servers) :
    DetailedBalance
      (manyServerBirthDeathRates (offeredLoad * serviceRate) serviceRate servers)
      (manyServerRelativeMass offeredLoad servers) := by
  intro state
  rw [manyServerRelativeMass_succ]
  have hmin : (Nat.min (state + 1) servers : ℝ) ≠ 0 :=
    ne_of_gt (manyServer_min_succ_pos hservers)
  simp only [manyServerBirthDeathRates]
  field_simp

/-- The product-form masses satisfy the global generator-balance equations. -/
theorem manyServerRelativeMass_stationaryGeneratorBalance
    (offeredLoad serviceRate : ℝ) {servers : ℕ} (hservers : 0 < servers) :
    StationaryGeneratorBalance
      (manyServerBirthDeathRates (offeredLoad * serviceRate) serviceRate servers)
      (manyServerRelativeMass offeredLoad servers) :=
  (manyServerRelativeMass_detailedBalance offeredLoad serviceRate hservers).stationaryGeneratorBalance

/-- The familiar factorial/geometric representation of the unnormalized
stationary masses.  The factorial branch describes states no larger than the
server pool; beyond it, every extra customer contributes one traffic-intensity
factor. -/
noncomputable def manyServerStationaryWeight
    (trafficIntensity : ℝ) (servers state : ℕ) : ℝ :=
  if state ≤ servers then
    ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)
  else
    ((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ) *
      trafficIntensity ^ (state - servers)

/-- The factorial expression applies through the last occupied-server state. -/
theorem manyServerStationaryWeight_eq_head
    (trafficIntensity : ℝ) {servers state : ℕ} (hstate : state ≤ servers) :
    manyServerStationaryWeight trafficIntensity servers state =
      ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
  simp [manyServerStationaryWeight, hstate]

/-- The geometric-tail expression also includes the boundary state at which
all servers are occupied. -/
theorem manyServerStationaryWeight_eq_tail
    (trafficIntensity : ℝ) {servers state : ℕ} (hstate : servers ≤ state) :
    manyServerStationaryWeight trafficIntensity servers state =
      ((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ) *
        trafficIntensity ^ (state - servers) := by
  rcases hstate.eq_or_lt with rfl | hlt
  · simp [manyServerStationaryWeight]
  · simp [manyServerStationaryWeight, Nat.not_le.mpr hlt]

/-- The explicit factorial/geometric weights satisfy the many-server detailed
balance equations. -/
theorem manyServerStationaryWeight_detailedBalance
    (trafficIntensity serviceRate : ℝ) (servers : ℕ) :
    DetailedBalance
      (manyServerBirthDeathRates
        ((servers : ℝ) * trafficIntensity * serviceRate) serviceRate servers)
      (manyServerStationaryWeight trafficIntensity servers) := by
  intro state
  have hcore :
      manyServerStationaryWeight trafficIntensity servers state *
          ((servers : ℝ) * trafficIntensity) =
        manyServerStationaryWeight trafficIntensity servers (state + 1) *
          (Nat.min (state + 1) servers : ℝ) := by
    by_cases hstate : state < servers
    · have hle : state ≤ servers := Nat.le_of_lt hstate
      have hsucc_le : state + 1 ≤ servers := Nat.succ_le_of_lt hstate
      have hmin : (Nat.min (state + 1) servers : ℝ) = state + 1 := by
        exact_mod_cast Nat.min_eq_left hsucc_le
      rw [manyServerStationaryWeight_eq_head trafficIntensity hle,
        manyServerStationaryWeight_eq_head trafficIntensity hsucc_le, hmin]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hfac : (state.factorial : ℝ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero state
      field_simp
      ring
    · have hservers_le : servers ≤ state := Nat.le_of_not_gt hstate
      have hservers_succ_le : servers ≤ state + 1 :=
        Nat.le_trans hservers_le (Nat.le_succ state)
      have hmin : (Nat.min (state + 1) servers : ℝ) = servers := by
        exact_mod_cast Nat.min_eq_right hservers_succ_le
      rw [manyServerStationaryWeight_eq_tail trafficIntensity hservers_le,
        manyServerStationaryWeight_eq_tail trafficIntensity hservers_succ_le,
        hmin, Nat.succ_sub hservers_le, pow_succ]
      ring
  simp only [manyServerBirthDeathRates]
  calc
    manyServerStationaryWeight trafficIntensity servers state *
        ((servers : ℝ) * trafficIntensity * serviceRate) =
      (manyServerStationaryWeight trafficIntensity servers state *
        ((servers : ℝ) * trafficIntensity)) * serviceRate := by ring
    _ = (manyServerStationaryWeight trafficIntensity servers (state + 1) *
        (Nat.min (state + 1) servers : ℝ)) * serviceRate := by rw [hcore]
    _ = manyServerStationaryWeight trafficIntensity servers (state + 1) *
        (serviceRate * (Nat.min (state + 1) servers : ℝ)) := by ring

/-- The explicit factorial/geometric weights satisfy global generator balance. -/
theorem manyServerStationaryWeight_stationaryGeneratorBalance
    (trafficIntensity serviceRate : ℝ) (servers : ℕ) :
    StationaryGeneratorBalance
      (manyServerBirthDeathRates
        ((servers : ℝ) * trafficIntensity * serviceRate) serviceRate servers)
      (manyServerStationaryWeight trafficIntensity servers) :=
  (manyServerStationaryWeight_detailedBalance trafficIntensity serviceRate servers).stationaryGeneratorBalance

/-- The reciprocal of the normalizing constant in the M/M/s stationary law is
the factor denoted by `η` in the classical Erlang-C formula.  The finite sum
contains states strictly below full occupancy; the final term sums the whole
geometric tail beginning at full occupancy. -/
noncomputable def manyServerStationaryNormalizer
    (trafficIntensity : ℝ) (servers : ℕ) : ℝ :=
  (∑ state ∈ Finset.range servers,
    ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)) +
    ((servers : ℝ) * trafficIntensity) ^ servers /
      ((servers.factorial : ℝ) * (1 - trafficIntensity))

/-- The unnormalized mass at full occupancy. -/
noncomputable def manyServerFullOccupancyWeight
    (trafficIntensity : ℝ) (servers : ℕ) : ℝ :=
  ((servers : ℝ) * trafficIntensity) ^ servers / (servers.factorial : ℝ)

/-- The finite part of the M/M/s stationary normalizer. -/
noncomputable def manyServerHeadNormalizer
    (trafficIntensity : ℝ) (servers : ℕ) : ℝ :=
  ∑ state ∈ Finset.range servers,
    ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ)

/-- The finite underloaded-state normalizer is strictly positive for a
nonempty server pool and a nonnegative traffic intensity. -/
theorem manyServerHeadNormalizer_pos
    (trafficIntensity : ℝ) {servers : ℕ} (hservers : 0 < servers)
    (htraffic_nonneg : 0 ≤ trafficIntensity) :
    0 < manyServerHeadNormalizer trafficIntensity servers := by
  have hsum_one : 1 ≤ ∑ state ∈ Finset.range servers,
      ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
    calc
      1 = ((servers : ℝ) * trafficIntensity) ^ 0 / ((0 : ℕ).factorial : ℝ) := by simp
      _ ≤ ∑ state ∈ Finset.range servers,
          ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
        exact Finset.single_le_sum
          (s := Finset.range servers)
          (f := fun state =>
            ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ))
          (fun state _ => div_nonneg
            (pow_nonneg (mul_nonneg (Nat.cast_nonneg servers) htraffic_nonneg) state)
            (by positivity))
          (a := 0) (Finset.mem_range.mpr hservers)
  exact lt_of_lt_of_le zero_lt_one hsum_one

/-- The geometric-tail contribution to the M/M/s stationary normalizer. -/
noncomputable def manyServerTailNormalizer
    (trafficIntensity : ℝ) (servers : ℕ) : ℝ :=
  manyServerFullOccupancyWeight trafficIntensity servers / (1 - trafficIntensity)

/-- The normalizer splits into its strictly-underloaded states and its full
occupancy geometric tail. -/
theorem manyServerStationaryNormalizer_eq_head_add_tail
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryNormalizer trafficIntensity servers =
      manyServerHeadNormalizer trafficIntensity servers +
        manyServerTailNormalizer trafficIntensity servers := by
  unfold manyServerStationaryNormalizer manyServerHeadNormalizer
    manyServerTailNormalizer manyServerFullOccupancyWeight
  rw [div_div]

/-- The Erlang-C delay probability: the stationary probability that every
server is occupied. -/
noncomputable def manyServerDelayProbability
    (trafficIntensity : ℝ) (servers : ℕ) : ℝ :=
  manyServerFullOccupancyWeight trafficIntensity servers /
    ((1 - trafficIntensity) * manyServerStationaryNormalizer trafficIntensity servers)

/-- Erlang-C is the geometric-tail normalizer divided by the full stationary
normalizer. -/
theorem manyServerDelayProbability_eq_tailNormalizer_div_normalizer
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerDelayProbability trafficIntensity servers =
      manyServerTailNormalizer trafficIntensity servers /
        manyServerStationaryNormalizer trafficIntensity servers := by
  unfold manyServerDelayProbability manyServerTailNormalizer
    manyServerFullOccupancyWeight
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The normalized stationary mass at a queue length. -/
noncomputable def manyServerStationaryMass
    (trafficIntensity : ℝ) (servers state : ℕ) : ℝ :=
  manyServerStationaryWeight trafficIntensity servers state /
    manyServerStationaryNormalizer trafficIntensity servers

/-- The shifted tail of the stationary weight is a scalar geometric series. -/
theorem manyServerStationaryWeight_tail
    (trafficIntensity : ℝ) (servers tail : ℕ) :
    manyServerStationaryWeight trafficIntensity servers (tail + servers) =
      manyServerFullOccupancyWeight trafficIntensity servers * trafficIntensity ^ tail := by
  rw [manyServerStationaryWeight_eq_tail trafficIntensity (Nat.le_add_left servers tail)]
  simp [manyServerFullOccupancyWeight]

/-- Under a stable nonnegative traffic intensity, the stationary weights sum
to the explicit finite-plus-geometric normalizer. -/
theorem hasSum_manyServerStationaryWeight
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    HasSum (manyServerStationaryWeight trafficIntensity servers)
      (manyServerStationaryNormalizer trafficIntensity servers) := by
  have hgeometric : HasSum
      (fun tail : ℕ =>
        manyServerFullOccupancyWeight trafficIntensity servers * trafficIntensity ^ tail)
      (manyServerFullOccupancyWeight trafficIntensity servers / (1 - trafficIntensity)) := by
    exact (hasSum_geometric_of_lt_one htraffic_nonneg htraffic_lt_one).mul_left
      (manyServerFullOccupancyWeight trafficIntensity servers)
  have htail : HasSum
      (fun tail : ℕ => manyServerStationaryWeight trafficIntensity servers (tail + servers))
      (manyServerFullOccupancyWeight trafficIntensity servers / (1 - trafficIntensity)) :=
    hgeometric.congr_fun (fun tail => by
      rw [manyServerStationaryWeight_tail])
  have hsum := (hasSum_nat_add_iff servers).mp htail
  convert hsum using 1
  simp only [manyServerStationaryNormalizer, manyServerFullOccupancyWeight]
  have hprefix : ∑ state ∈ Finset.range servers,
      manyServerStationaryWeight trafficIntensity servers state =
    ∑ state ∈ Finset.range servers,
      ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
    apply Finset.sum_congr rfl
    intro state hstate
    rw [manyServerStationaryWeight_eq_head trafficIntensity]
    exact Nat.le_of_lt (Finset.mem_range.mp hstate)
  rw [hprefix, div_div]
  ring

/-- The M/M/s normalizer is strictly positive in the stable regime. -/
theorem manyServerStationaryNormalizer_pos
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    0 < manyServerStationaryNormalizer trafficIntensity servers := by
  by_cases hservers : servers = 0
  · subst servers
    simp [manyServerStationaryNormalizer, sub_pos.mpr htraffic_lt_one]
  · have hservers_pos : 0 < servers := Nat.pos_of_ne_zero hservers
    have htail_nonneg : 0 ≤
        ((servers : ℝ) * trafficIntensity) ^ servers /
          ((servers.factorial : ℝ) * (1 - trafficIntensity)) := by
      exact div_nonneg
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg servers) htraffic_nonneg) servers)
        (mul_nonneg (by positivity) (sub_nonneg.mpr (le_of_lt htraffic_lt_one)))
    have hsum_one : 1 ≤ ∑ state ∈ Finset.range servers,
        ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
      calc
        1 = ((servers : ℝ) * trafficIntensity) ^ 0 / ((0 : ℕ).factorial : ℝ) := by simp
        _ ≤ ∑ state ∈ Finset.range servers,
            ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ) := by
          exact Finset.single_le_sum
            (s := Finset.range servers)
            (f := fun state =>
              ((servers : ℝ) * trafficIntensity) ^ state / (state.factorial : ℝ))
            (fun state _ => div_nonneg
              (pow_nonneg (mul_nonneg (Nat.cast_nonneg servers) htraffic_nonneg) state)
              (by positivity))
            (a := 0) (Finset.mem_range.mpr hservers_pos)
    unfold manyServerStationaryNormalizer
    linarith

/-- At a strictly positive traffic intensity, the full-occupancy weight is
strictly positive. -/
theorem manyServerFullOccupancyWeight_pos
    {trafficIntensity : ℝ} (servers : ℕ) (htraffic_pos : 0 < trafficIntensity) :
    0 < manyServerFullOccupancyWeight trafficIntensity servers := by
  unfold manyServerFullOccupancyWeight
  by_cases hservers : servers = 0
  · subst servers
    norm_num
  · have hservers_pos : 0 < servers := Nat.pos_of_ne_zero hservers
    have hbase_pos : 0 < (servers : ℝ) * trafficIntensity := by
      exact mul_pos (by exact_mod_cast hservers_pos) htraffic_pos
    exact div_pos (pow_pos hbase_pos _) (by positivity)

/-- At a strictly positive stable traffic intensity, the full-occupancy
stationary tail mass is strictly positive. -/
theorem manyServerDelayProbability_pos
    {trafficIntensity : ℝ} (servers : ℕ)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    0 < manyServerDelayProbability trafficIntensity servers := by
  have htraffic_nonneg : 0 ≤ trafficIntensity := htraffic_pos.le
  have hfull_pos : 0 < manyServerFullOccupancyWeight trafficIntensity servers :=
    manyServerFullOccupancyWeight_pos servers htraffic_pos
  have hdenominator_pos : 0 <
      (1 - trafficIntensity) * manyServerStationaryNormalizer trafficIntensity servers :=
    mul_pos (sub_pos.mpr htraffic_lt_one)
      (manyServerStationaryNormalizer_pos trafficIntensity servers
        htraffic_nonneg htraffic_lt_one)
  unfold manyServerDelayProbability
  exact div_pos hfull_pos hdenominator_pos

/-- The normalized M/M/s masses sum to one. -/
theorem hasSum_manyServerStationaryMass
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    HasSum (manyServerStationaryMass trafficIntensity servers) 1 := by
  have hsum := hasSum_manyServerStationaryWeight trafficIntensity servers
    htraffic_nonneg htraffic_lt_one
  have hnormalizer_ne : manyServerStationaryNormalizer trafficIntensity servers ≠ 0 :=
    ne_of_gt (manyServerStationaryNormalizer_pos trafficIntensity servers
      htraffic_nonneg htraffic_lt_one)
  convert hsum.div_const (manyServerStationaryNormalizer trafficIntensity servers) using 1
  exact (div_self hnormalizer_ne).symm

/-- The factorial/geometric stationary weights are nonnegative at a
nonnegative traffic intensity. -/
theorem manyServerStationaryWeight_nonneg
    {trafficIntensity : ℝ} (htraffic_nonneg : 0 ≤ trafficIntensity)
    (servers state : ℕ) :
    0 ≤ manyServerStationaryWeight trafficIntensity servers state := by
  unfold manyServerStationaryWeight
  split_ifs with hstate
  · exact div_nonneg
      (pow_nonneg (mul_nonneg (Nat.cast_nonneg servers) htraffic_nonneg) state)
      (by positivity)
  · exact mul_nonneg
      (div_nonneg
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg servers) htraffic_nonneg) servers)
        (by positivity))
      (pow_nonneg htraffic_nonneg (state - servers))

/-- The normalized M/M/s stationary mass is nonnegative. -/
theorem manyServerStationaryMass_nonneg
    {trafficIntensity : ℝ} (servers state : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    0 ≤ manyServerStationaryMass trafficIntensity servers state := by
  unfold manyServerStationaryMass
  exact div_nonneg
    (manyServerStationaryWeight_nonneg htraffic_nonneg servers state)
    (manyServerStationaryNormalizer_pos trafficIntensity servers
      htraffic_nonneg htraffic_lt_one).le

/-- The normalized M/M/s mass viewed in the nonnegative reals. -/
noncomputable def manyServerStationaryMassNN
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    ℕ → ℝ≥0 := fun state =>
  ⟨manyServerStationaryMass trafficIntensity servers state,
    manyServerStationaryMass_nonneg servers state htraffic_nonneg htraffic_lt_one⟩

/-- The nonnegative-real M/M/s masses sum to one. -/
theorem hasSum_manyServerStationaryMassNN
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (manyServerStationaryMassNN trafficIntensity servers
        htraffic_nonneg htraffic_lt_one) 1 := by
  exact NNReal.hasSum_coe.mp (by
    simpa [manyServerStationaryMassNN] using
      hasSum_manyServerStationaryMass trafficIntensity servers
        htraffic_nonneg htraffic_lt_one)

/-- The normalized M/M/s masses as a countable probability mass function. -/
noncomputable def manyServerStationaryPMF
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    PMF ℕ :=
  ⟨fun state => ↑(manyServerStationaryMassNN trafficIntensity servers
      htraffic_nonneg htraffic_lt_one state),
    ENNReal.hasSum_coe.mpr (hasSum_manyServerStationaryMassNN
      trafficIntensity servers htraffic_nonneg htraffic_lt_one)⟩

/-- The real mass of the countable M/M/s PMF is the normalized stationary
mass used in the generator calculations. -/
theorem manyServerStationaryPMF_toReal
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1)
    (state : ℕ) :
    (manyServerStationaryPMF trafficIntensity servers htraffic_nonneg htraffic_lt_one state).toReal =
      manyServerStationaryMass trafficIntensity servers state := by
  change (↑(manyServerStationaryMassNN trafficIntensity servers
    htraffic_nonneg htraffic_lt_one state) : ℝ≥0∞).toReal =
      manyServerStationaryMass trafficIntensity servers state
  rw [ENNReal.coe_toReal]
  rfl

/-- The normalized masses retain detailed balance. -/
theorem manyServerStationaryMass_detailedBalance
    (trafficIntensity serviceRate : ℝ) (servers : ℕ) :
    DetailedBalance
      (manyServerBirthDeathRates
        ((servers : ℝ) * trafficIntensity * serviceRate) serviceRate servers)
      (manyServerStationaryMass trafficIntensity servers) := by
  intro state
  have hbalance := manyServerStationaryWeight_detailedBalance
    trafficIntensity serviceRate servers state
  simp only [manyServerStationaryMass, manyServerBirthDeathRates] at hbalance ⊢
  calc
    (manyServerStationaryWeight trafficIntensity servers state /
        manyServerStationaryNormalizer trafficIntensity servers) *
        ((servers : ℝ) * trafficIntensity * serviceRate) =
      (manyServerStationaryWeight trafficIntensity servers state *
        ((servers : ℝ) * trafficIntensity * serviceRate)) /
        manyServerStationaryNormalizer trafficIntensity servers := by ring
    _ = (manyServerStationaryWeight trafficIntensity servers (state + 1) *
        (serviceRate * (Nat.min (state + 1) servers : ℝ))) /
        manyServerStationaryNormalizer trafficIntensity servers := by rw [hbalance]
    _ = (manyServerStationaryWeight trafficIntensity servers (state + 1) /
        manyServerStationaryNormalizer trafficIntensity servers) *
        (serviceRate * (Nat.min (state + 1) servers : ℝ)) := by ring

/-- The normalized M/M/s masses satisfy global generator balance. -/
theorem manyServerStationaryMass_stationaryGeneratorBalance
    (trafficIntensity serviceRate : ℝ) (servers : ℕ) :
    StationaryGeneratorBalance
      (manyServerBirthDeathRates
        ((servers : ℝ) * trafficIntensity * serviceRate) serviceRate servers)
      (manyServerStationaryMass trafficIntensity servers) :=
  (manyServerStationaryMass_detailedBalance trafficIntensity serviceRate servers).stationaryGeneratorBalance

/-- Stable traffic intensity constructs a normalized solution to the M/M/s
generator-balance equations. -/
noncomputable def manyServerStationaryGeneratorLaw
    (trafficIntensity serviceRate : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    GeneratorStationaryLaw
      (manyServerBirthDeathRates
        ((servers : ℝ) * trafficIntensity * serviceRate) serviceRate servers) where
  mass := manyServerStationaryMass trafficIntensity servers
  nonneg := fun state => manyServerStationaryMass_nonneg servers state
    htraffic_nonneg htraffic_lt_one
  hasSum_one := hasSum_manyServerStationaryMass trafficIntensity servers
    htraffic_nonneg htraffic_lt_one
  generator_balance := manyServerStationaryMass_stationaryGeneratorBalance
    trafficIntensity serviceRate servers

/-- The stationary mass below the server threshold is its factorial term times
the reciprocal normalizer. -/
theorem manyServerStationaryMass_eq_head
    (trafficIntensity : ℝ) {servers state : ℕ} (hstate : state ≤ servers) :
    manyServerStationaryMass trafficIntensity servers state =
      ((servers : ℝ) * trafficIntensity) ^ state /
        ((state.factorial : ℝ) * manyServerStationaryNormalizer trafficIntensity servers) := by
  rw [manyServerStationaryMass, manyServerStationaryWeight_eq_head trafficIntensity hstate,
    div_div]

/-- The stationary mass at and above full occupancy is its geometric-tail term
times the reciprocal normalizer. -/
theorem manyServerStationaryMass_eq_tail
    (trafficIntensity : ℝ) {servers state : ℕ} (hstate : servers ≤ state) :
    manyServerStationaryMass trafficIntensity servers state =
      manyServerFullOccupancyWeight trafficIntensity servers *
        trafficIntensity ^ (state - servers) /
          manyServerStationaryNormalizer trafficIntensity servers := by
  rw [manyServerStationaryMass, manyServerStationaryWeight_eq_tail trafficIntensity hstate,
    manyServerFullOccupancyWeight]

/-- Below full occupancy, consecutive normalized M/M/s masses obey the
factorial recurrence. -/
theorem manyServerStationaryMass_head_recurrence
    (trafficIntensity : ℝ) (servers state : ℕ) (hstate : state < servers) :
    ((state + 1 : ℕ) : ℝ) *
        manyServerStationaryMass trafficIntensity servers (state + 1) =
      ((servers : ℕ) : ℝ) * trafficIntensity *
        manyServerStationaryMass trafficIntensity servers state := by
  have hbalance := manyServerStationaryMass_detailedBalance
    trafficIntensity (1 : ℝ) servers state
  have hmin : (Nat.min (state + 1) servers : ℝ) = state + 1 := by
    exact_mod_cast Nat.min_eq_left (Nat.succ_le_of_lt hstate)
  simp only [manyServerBirthDeathRates] at hbalance
  rw [hmin] at hbalance
  have hbalance' :
      manyServerStationaryMass trafficIntensity servers (state + 1) *
          ((state + 1 : ℕ) : ℝ) =
        manyServerStationaryMass trafficIntensity servers state *
          ((servers : ℝ) * trafficIntensity) := by
    simpa [Nat.cast_add, Nat.cast_one] using hbalance.symm
  calc
    ((state + 1 : ℕ) : ℝ) *
        manyServerStationaryMass trafficIntensity servers (state + 1) =
      manyServerStationaryMass trafficIntensity servers (state + 1) *
        ((state + 1 : ℕ) : ℝ) := by ring
    _ = manyServerStationaryMass trafficIntensity servers state *
        ((servers : ℝ) * trafficIntensity) := hbalance'
    _ = ((servers : ℕ) : ℝ) * trafficIntensity *
        manyServerStationaryMass trafficIntensity servers state := by ring

/-- Once all servers are occupied, consecutive normalized M/M/s masses have
the constant traffic-intensity ratio. -/
theorem manyServerStationaryMass_tail_recurrence
    (trafficIntensity : ℝ) {servers state : ℕ}
    (hservers : 0 < servers) (hstate : servers ≤ state) :
    manyServerStationaryMass trafficIntensity servers (state + 1) =
      trafficIntensity * manyServerStationaryMass trafficIntensity servers state := by
  have hbalance := manyServerStationaryMass_detailedBalance
    trafficIntensity (1 : ℝ) servers state
  have hmin : (Nat.min (state + 1) servers : ℝ) = servers := by
    exact_mod_cast Nat.min_eq_right
      (Nat.le_trans hstate (Nat.le_succ state))
  simp only [manyServerBirthDeathRates] at hbalance
  rw [hmin] at hbalance
  have hservers_ne : (servers : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hservers
  apply (mul_left_cancel₀ hservers_ne)
  linarith

/-- The delayed tail of the normalized M/M/s stationary law has the Erlang-C
mass. -/
theorem hasSum_manyServerStationaryMass_delayedTail
    (trafficIntensity : ℝ) (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun tail : ℕ => manyServerStationaryMass trafficIntensity servers (tail + servers))
      (manyServerDelayProbability trafficIntensity servers) := by
  have hgeometric : HasSum
      (fun tail : ℕ =>
        manyServerFullOccupancyWeight trafficIntensity servers * trafficIntensity ^ tail)
      (manyServerFullOccupancyWeight trafficIntensity servers / (1 - trafficIntensity)) :=
    (hasSum_geometric_of_lt_one htraffic_nonneg htraffic_lt_one).mul_left
      (manyServerFullOccupancyWeight trafficIntensity servers)
  have htail : HasSum
      (fun tail : ℕ => manyServerStationaryWeight trafficIntensity servers (tail + servers))
      (manyServerFullOccupancyWeight trafficIntensity servers / (1 - trafficIntensity)) :=
    hgeometric.congr_fun (fun tail => by rw [manyServerStationaryWeight_tail])
  convert htail.div_const (manyServerStationaryNormalizer trafficIntensity servers) using 1
  rw [manyServerDelayProbability, div_div]

/-- Moving the start of the delayed geometric tail by `tail` customers
multiplies every stationary mass by `trafficIntensity ^ tail`. -/
theorem manyServerStationaryMass_delayedTail_shift
    (trafficIntensity : ℝ) (servers tail offset : ℕ) :
    manyServerStationaryMass trafficIntensity servers (tail + servers + offset) =
      trafficIntensity ^ tail *
        manyServerStationaryMass trafficIntensity servers (offset + servers) := by
  rw [manyServerStationaryMass_eq_tail trafficIntensity (by omega),
    manyServerStationaryMass_eq_tail trafficIntensity (by omega)]
  have hleft : tail + servers + offset - servers = tail + offset := by omega
  have hright : offset + servers - servers = offset := by omega
  rw [hleft, hright, pow_add]
  ring

/-- The stationary mass in a delayed tail after an additional offset `tail`
is its Erlang-C mass multiplied by the corresponding geometric factor. -/
theorem hasSum_manyServerStationaryMass_delayedTail_shift
    (trafficIntensity : ℝ) (servers tail : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun offset : ℕ =>
        manyServerStationaryMass trafficIntensity servers (tail + servers + offset))
      (trafficIntensity ^ tail * manyServerDelayProbability trafficIntensity servers) := by
  have htail := hasSum_manyServerStationaryMass_delayedTail
    trafficIntensity servers htraffic_nonneg htraffic_lt_one
  convert htail.mul_left (trafficIntensity ^ tail) using 1
  · ext offset
    exact manyServerStationaryMass_delayedTail_shift trafficIntensity servers tail offset

/-- The normalized stationary mass at and beyond a specified offset above the
full-occupancy threshold. -/
noncomputable def manyServerStationaryDelayedTailMass
    (trafficIntensity : ℝ) (servers tail : ℕ) : ℝ :=
  ∑' offset : ℕ,
    manyServerStationaryMass trafficIntensity servers (tail + servers + offset)

/-- The delayed stationary tail is an exact geometric multiple of the
full-occupancy tail mass. -/
theorem manyServerStationaryDelayedTailMass_eq
    (trafficIntensity : ℝ) (servers tail : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedTailMass trafficIntensity servers tail =
      trafficIntensity ^ tail * manyServerDelayProbability trafficIntensity servers := by
  unfold manyServerStationaryDelayedTailMass
  exact (hasSum_manyServerStationaryMass_delayedTail_shift
    trafficIntensity servers tail htraffic_nonneg htraffic_lt_one).tsum_eq

/-- The stationary tail beyond a given offset, conditional on full occupancy. -/
noncomputable def manyServerStationaryDelayedTailConditionalMass
    (trafficIntensity : ℝ) (servers tail : ℕ) : ℝ :=
  manyServerStationaryDelayedTailMass trafficIntensity servers tail /
    manyServerDelayProbability trafficIntensity servers

/-- The conditional delayed tail has its exact geometric form. -/
theorem manyServerStationaryDelayedTailConditionalMass_eq
    {trafficIntensity : ℝ} (servers tail : ℕ)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedTailConditionalMass trafficIntensity servers tail =
      trafficIntensity ^ tail := by
  unfold manyServerStationaryDelayedTailConditionalMass
  rw [manyServerStationaryDelayedTailMass_eq]
  · field_simp [ne_of_gt (manyServerDelayProbability_pos servers htraffic_pos htraffic_lt_one)]
  · exact htraffic_pos.le
  · exact htraffic_lt_one

/-- The stationary mass at an exact delayed offset, conditional on full
occupancy. -/
noncomputable def manyServerStationaryDelayedPointConditionalMass
    (trafficIntensity : ℝ) (servers tail : ℕ) : ℝ :=
  manyServerStationaryMass trafficIntensity servers (tail + servers) /
    manyServerDelayProbability trafficIntensity servers

/-- Conditional delayed point masses have the geometric probability-mass
form. -/
theorem manyServerStationaryDelayedPointConditionalMass_eq
    {trafficIntensity : ℝ} (servers tail : ℕ)
    (htraffic_pos : 0 < trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedPointConditionalMass trafficIntensity servers tail =
      (1 - trafficIntensity) * trafficIntensity ^ tail := by
  have htraffic_nonneg : 0 ≤ trafficIntensity := htraffic_pos.le
  have hnormalizer_ne : manyServerStationaryNormalizer trafficIntensity servers ≠ 0 :=
    (manyServerStationaryNormalizer_pos trafficIntensity servers
      htraffic_nonneg htraffic_lt_one).ne'
  have hfull_ne : manyServerFullOccupancyWeight trafficIntensity servers ≠ 0 :=
    (manyServerFullOccupancyWeight_pos servers htraffic_pos).ne'
  unfold manyServerStationaryDelayedPointConditionalMass
  rw [manyServerStationaryMass_eq_tail trafficIntensity (by omega)]
  unfold manyServerDelayProbability
  field_simp [manyServerFullOccupancyWeight, hnormalizer_ne, hfull_ne]
  rw [show tail + servers - servers = tail by omega]
  ring

end Queueing
end Probability
end AppliedModelingLib
