import AppliedModelingLib.Queueing.ManyServerStationaryConditionalLaw
import AppliedModelingLib.Queueing.GeometricTailMoments
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Delayed-offset moments in a many-server stationary queue

The stationary mass above full occupancy is a geometric tail.  This module
packages its first four raw offset moments in a form that can be combined with
separate finite-head calculations.
-/

namespace AppliedModelingLib.Probability.Queueing

/-- At a fixed offset above full occupancy, the invariant mass is the
all-servers-busy mass times a normalized geometric point probability. -/
theorem manyServerStationaryMass_delayedOffset_eq_geometric
    {trafficIntensity : ℝ} (servers tail : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryMass trafficIntensity servers (tail + servers) =
      manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity) *
        trafficIntensity ^ tail := by
  have hconditional := manyServerStationaryDelayedPointConditionalMass_eq
    (trafficIntensity := trafficIntensity) servers tail htraffic_pos htraffic_lt_one
  have hdelay_ne : manyServerDelayProbability trafficIntensity servers ≠ 0 :=
    (manyServerDelayProbability_pos servers htraffic_pos htraffic_lt_one).ne'
  unfold manyServerStationaryDelayedPointConditionalMass at hconditional
  calc
    manyServerStationaryMass trafficIntensity servers (tail + servers) =
        (manyServerStationaryMass trafficIntensity servers (tail + servers) /
          manyServerDelayProbability trafficIntensity servers) *
            manyServerDelayProbability trafficIntensity servers := by
              field_simp [hdelay_ne]
    _ = ((1 - trafficIntensity) * trafficIntensity ^ tail) *
          manyServerDelayProbability trafficIntensity servers := by rw [hconditional]
    _ = manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity) *
          trafficIntensity ^ tail := by ring

/-- The first raw delayed-offset stationary moment. -/
theorem hasSum_manyServerStationaryDelayedOffset_pow_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun tail : ℕ => (tail : ℝ) *
        manyServerStationaryMass trafficIntensity servers (tail + servers))
      (manyServerDelayProbability trafficIntensity servers * trafficIntensity /
        (1 - trafficIntensity)) := by
  have hgeometric := hasSum_geometric_tail_pow_one htraffic_pos.le htraffic_lt_one
  have hscaled := hgeometric.mul_left
    (manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity))
  convert hscaled using 1
  · ext tail
    rw [manyServerStationaryMass_delayedOffset_eq_geometric
      servers tail hservers htraffic_pos htraffic_lt_one]
    ring
  · have hgap : 1 - trafficIntensity ≠ 0 := by linarith
    field_simp [hgap]

/-- The second raw delayed-offset stationary moment. -/
theorem hasSum_manyServerStationaryDelayedOffset_pow_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun tail : ℕ => (tail : ℝ) ^ 2 *
        manyServerStationaryMass trafficIntensity servers (tail + servers))
      (manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + trafficIntensity) / (1 - trafficIntensity) ^ 2) := by
  have hgeometric := hasSum_geometric_tail_pow_two htraffic_pos.le htraffic_lt_one
  have hscaled := hgeometric.mul_left
    (manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity))
  convert hscaled using 1
  · ext tail
    rw [manyServerStationaryMass_delayedOffset_eq_geometric
      servers tail hservers htraffic_pos htraffic_lt_one]
    ring
  · have hgap : 1 - trafficIntensity ≠ 0 := by linarith
    field_simp [hgap]

/-- The third raw delayed-offset stationary moment. -/
theorem hasSum_manyServerStationaryDelayedOffset_pow_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun tail : ℕ => (tail : ℝ) ^ 3 *
        manyServerStationaryMass trafficIntensity servers (tail + servers))
      (manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + 4 * trafficIntensity + trafficIntensity ^ 2) /
          (1 - trafficIntensity) ^ 3) := by
  have hgeometric := hasSum_geometric_tail_pow_three htraffic_pos.le htraffic_lt_one
  have hscaled := hgeometric.mul_left
    (manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity))
  convert hscaled using 1
  · ext tail
    rw [manyServerStationaryMass_delayedOffset_eq_geometric
      servers tail hservers htraffic_pos htraffic_lt_one]
    ring
  · have hgap : 1 - trafficIntensity ≠ 0 := by linarith
    field_simp [hgap]

/-- The fourth raw delayed-offset stationary moment. -/
theorem hasSum_manyServerStationaryDelayedOffset_pow_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun tail : ℕ => (tail : ℝ) ^ 4 *
        manyServerStationaryMass trafficIntensity servers (tail + servers))
      (manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + 11 * trafficIntensity + 11 * trafficIntensity ^ 2 + trafficIntensity ^ 3) /
          (1 - trafficIntensity) ^ 4) := by
  have hgeometric := hasSum_geometric_tail_pow_four htraffic_pos.le htraffic_lt_one
  have hscaled := hgeometric.mul_left
    (manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity))
  convert hscaled using 1
  · ext tail
    rw [manyServerStationaryMass_delayedOffset_eq_geometric
      servers tail hservers htraffic_pos htraffic_lt_one]
    ring
  · have hgap : 1 - trafficIntensity ≠ 0 := by linarith
    field_simp [hgap]

/-- The mass immediately below full occupancy is determined by the geometric
tail mass and the final factorial-branch balance equation. -/
theorem manyServerStationaryMass_before_full_eq_delay_mul
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryMass trafficIntensity servers (servers - 1) =
      manyServerDelayProbability trafficIntensity servers * (1 - trafficIntensity) /
        trafficIntensity := by
  obtain ⟨predecessor, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hservers)
  have htail := manyServerStationaryMass_delayedOffset_eq_geometric
    (trafficIntensity := trafficIntensity) (predecessor + 1) 0 (by omega)
      htraffic_pos htraffic_lt_one
  have htail' : manyServerStationaryMass trafficIntensity (predecessor + 1)
      (predecessor + 1) =
      manyServerDelayProbability trafficIntensity (predecessor + 1) *
        (1 - trafficIntensity) := by
    simpa using htail
  have hrec := manyServerStationaryMass_head_recurrence trafficIntensity
    (predecessor + 1) predecessor (by omega)
  simp only [Nat.cast_add, Nat.cast_one] at hrec
  have hservers_ne : (predecessor : ℝ) + 1 ≠ 0 := by positivity
  have hrec' : manyServerStationaryMass trafficIntensity (predecessor + 1)
      (predecessor + 1) =
      trafficIntensity *
        manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor := by
    apply (mul_left_cancel₀ hservers_ne)
    nlinarith [hrec]
  have hproduct : manyServerStationaryMass trafficIntensity (predecessor + 1)
      predecessor * trafficIntensity =
      manyServerDelayProbability trafficIntensity (predecessor + 1) *
        (1 - trafficIntensity) := by
    calc
      manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor *
          trafficIntensity =
          trafficIntensity *
            manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor := by ring
      _ = manyServerStationaryMass trafficIntensity (predecessor + 1)
            (predecessor + 1) := hrec'.symm
      _ = manyServerDelayProbability trafficIntensity (predecessor + 1) *
            (1 - trafficIntensity) := htail'
  exact (eq_div_iff htraffic_pos.ne').2 hproduct

/-- The raw stationary moment on the strictly underloaded branch. -/
noncomputable def manyServerStationaryHeadRawMoment
    (trafficIntensity : ℝ) (servers moment : ℕ) : ℝ :=
  ∑ state ∈ Finset.range servers,
    (state : ℝ) ^ moment * manyServerStationaryMass trafficIntensity servers state

/-- The zeroth finite-head raw moment is the probability of having an idle
server. -/
theorem manyServerStationaryHeadRawMoment_zero
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadRawMoment trafficIntensity servers 0 =
      1 - manyServerDelayProbability trafficIntensity servers := by
  unfold manyServerStationaryHeadRawMoment
  simp only [pow_zero, one_mul]
  rw [← manyServerStationaryLaw_range_toReal_eq_sum]
  exact manyServerStationaryLaw_range_servers_toReal_eq_one_sub_delayProbability
    trafficIntensity hservers htraffic_pos htraffic_lt_one

/-- The first finite-head raw moment follows by shifting the factorial-branch
balance equations one state at a time. -/
theorem manyServerStationaryHeadRawMoment_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadRawMoment trafficIntensity servers 1 =
      trafficIntensity * (servers : ℝ) *
        (1 - manyServerDelayProbability trafficIntensity servers) -
      (servers : ℝ) * manyServerDelayProbability trafficIntensity servers *
        (1 - trafficIntensity) := by
  obtain ⟨predecessor, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hservers)
  have hhead_zero := manyServerStationaryHeadRawMoment_zero
    (trafficIntensity := trafficIntensity) (predecessor + 1) (by omega)
      htraffic_pos htraffic_lt_one
  have hlast := manyServerStationaryMass_before_full_eq_delay_mul
    (trafficIntensity := trafficIntensity) (predecessor + 1) (by omega)
      htraffic_pos htraffic_lt_one
  have hlast' : manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor =
      manyServerDelayProbability trafficIntensity (predecessor + 1) *
        (1 - trafficIntensity) / trafficIntensity := by
    simpa using hlast
  have hshift :
      ∑ state ∈ Finset.range (predecessor + 1), (state : ℝ) *
        manyServerStationaryMass trafficIntensity (predecessor + 1) state =
      trafficIntensity * (predecessor + 1 : ℝ) *
        (∑ state ∈ Finset.range predecessor,
          manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero]
    calc
      ∑ state ∈ Finset.range predecessor, ((state : ℝ) + 1) *
          manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
          ∑ state ∈ Finset.range predecessor,
            trafficIntensity * (predecessor + 1 : ℝ) *
              manyServerStationaryMass trafficIntensity (predecessor + 1) state := by
              apply Finset.sum_congr rfl
              intro state hstate
              have hrec := manyServerStationaryMass_head_recurrence trafficIntensity
                (predecessor + 1) state
                (lt_trans (Finset.mem_range.mp hstate) (Nat.lt_succ_self predecessor))
              norm_num [Nat.cast_add, Nat.cast_one] at hrec
              calc
                ((state : ℝ) + 1) *
                    manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
                    (predecessor + 1 : ℝ) * trafficIntensity *
                      manyServerStationaryMass trafficIntensity (predecessor + 1) state := hrec
                _ = trafficIntensity * (predecessor + 1 : ℝ) *
                      manyServerStationaryMass trafficIntensity (predecessor + 1) state := by ring
      _ = trafficIntensity * (predecessor + 1 : ℝ) *
          (∑ state ∈ Finset.range predecessor,
            manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
            rw [Finset.mul_sum]
  unfold manyServerStationaryHeadRawMoment at hhead_zero ⊢
  simp only [pow_zero, one_mul] at hhead_zero
  simp only [pow_one]
  have hprefix :
      (∑ state ∈ Finset.range predecessor,
        manyServerStationaryMass trafficIntensity (predecessor + 1) state) =
      (∑ state ∈ Finset.range (predecessor + 1),
        manyServerStationaryMass trafficIntensity (predecessor + 1) state) -
        manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor := by
    rw [Finset.sum_range_succ]
    ring
  rw [hshift, hprefix, hhead_zero, hlast']
  simp only [Nat.cast_succ]
  field_simp [htraffic_pos.ne']

/-- The stationary mean number of idle servers is exactly the spare capacity.
This is the finite-state flow-balance identity behind the QED estimate for
unrealized potential service. -/
theorem manyServerStationary_idleCapacity_expectation
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (∑ state ∈ Finset.range servers,
      ((servers - state : ℕ) : ℝ) *
        manyServerStationaryMass trafficIntensity servers state) =
      (servers : ℝ) * (1 - trafficIntensity) := by
  calc
    (∑ state ∈ Finset.range servers,
      ((servers - state : ℕ) : ℝ) *
        manyServerStationaryMass trafficIntensity servers state) =
        ∑ state ∈ Finset.range servers,
          ((servers : ℝ) * manyServerStationaryMass trafficIntensity servers state -
            (state : ℝ) * manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          rw [Nat.cast_sub (Nat.le_of_lt (Finset.mem_range.mp hstate))]
          ring
    _ = (servers : ℝ) *
          manyServerStationaryHeadRawMoment trafficIntensity servers 0 -
        manyServerStationaryHeadRawMoment trafficIntensity servers 1 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp [manyServerStationaryHeadRawMoment]
    _ = (servers : ℝ) * (1 - trafficIntensity) := by
          rw [manyServerStationaryHeadRawMoment_zero servers hservers htraffic_pos htraffic_lt_one,
            manyServerStationaryHeadRawMoment_one servers hservers htraffic_pos htraffic_lt_one]
          ring

/-- Equivalently, the stationary mean idle fraction is `1 - ρ`.  The sum may
be restricted to states below capacity because the idle fraction is zero on
the geometric tail. -/
theorem manyServerStationary_idleFraction_head_sum
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (∑ state ∈ Finset.range servers,
      (1 - (manyServerBusyFraction servers state : ℝ)) *
        manyServerStationaryMass trafficIntensity servers state) =
      1 - trafficIntensity := by
  have hservers_ne : (servers : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hservers
  calc
    (∑ state ∈ Finset.range servers,
      (1 - (manyServerBusyFraction servers state : ℝ)) *
        manyServerStationaryMass trafficIntensity servers state) =
        (∑ state ∈ Finset.range servers,
          ((servers - state : ℕ) : ℝ) *
            manyServerStationaryMass trafficIntensity servers state) /
          (servers : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro state _
          rw [one_sub_manyServerBusyFraction_eq_unusedFraction servers state hservers]
          ring
    _ = 1 - trafficIntensity := by
          rw [manyServerStationary_idleCapacity_expectation servers
            hservers htraffic_pos htraffic_lt_one]
          field_simp [hservers_ne]

/-- The stationary-law formulation of the idle-fraction identity.  This makes
the finite-head calculation available directly to canonical-clock and marked
trajectory arguments. -/
theorem integral_manyServerStationary_idleFraction
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    (∫ state : ℕ, 1 - (manyServerBusyFraction servers state : ℝ) ∂
      (manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one).toMeasure) =
      1 - trafficIntensity := by
  have hintegrable : MeasureTheory.Integrable
      (fun state : ℕ => 1 - (manyServerBusyFraction servers state : ℝ))
      (manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one).toMeasure := by
    apply MeasureTheory.Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    filter_upwards [] with state
    have hbusy_nonneg : 0 ≤ (manyServerBusyFraction servers state : ℝ) := by positivity
    have hbusy_le : (manyServerBusyFraction servers state : ℝ) ≤ 1 := by
      exact_mod_cast manyServerBusyFraction_le_one servers state hservers
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmass (state : ℕ) :
      (manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one).toMeasure.real
        {state} = manyServerStationaryMass trafficIntensity servers state := by
    rw [MeasureTheory.measureReal_def,
      (manyServerStationaryPMF trafficIntensity servers htraffic_pos.le htraffic_lt_one).toMeasure_apply_singleton
        state (measurableSet_singleton _),
      manyServerStationaryPMF_toReal]
  rw [MeasureTheory.integral_countable hintegrable]
  rw [tsum_eq_sum (s := Finset.range servers)]
  · simpa [hmass, smul_eq_mul, mul_comm] using
      manyServerStationary_idleFraction_head_sum servers hservers htraffic_pos htraffic_lt_one
  · intro state hstate
    have hservers_le : servers ≤ state := by
      apply Nat.le_of_not_gt
      simpa only [Finset.mem_range] using hstate
    rw [hmass,
      one_sub_manyServerBusyFraction_eq_unusedFraction servers state hservers,
      Nat.sub_eq_zero_of_le hservers_le]
    simp

/-- The finite-head moment obtained after adding one to each queue length. -/
noncomputable def manyServerStationaryHeadShiftedRawMoment
    (trafficIntensity : ℝ) (servers moment : ℕ) : ℝ :=
  ∑ state ∈ Finset.range servers,
    ((state : ℝ) + 1) ^ moment *
      manyServerStationaryMass trafficIntensity servers state

/-- The factorial-branch balance equations express each positive head moment
through the preceding shifted head moment and its final boundary term. -/
theorem manyServerStationaryHeadRawMoment_succ
    {trafficIntensity : ℝ} (servers moment : ℕ)
    (hservers : 0 < servers) :
    manyServerStationaryHeadRawMoment trafficIntensity servers (moment + 1) =
      trafficIntensity * (servers : ℝ) *
        (manyServerStationaryHeadShiftedRawMoment trafficIntensity servers moment -
          (servers : ℝ) ^ moment *
            manyServerStationaryMass trafficIntensity servers (servers - 1)) := by
  obtain ⟨predecessor, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hservers)
  unfold manyServerStationaryHeadRawMoment
    manyServerStationaryHeadShiftedRawMoment
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero,
    zero_pow (Nat.succ_ne_zero moment), zero_mul, add_zero]
  have hshift :
      ∑ state ∈ Finset.range predecessor,
        ((state : ℝ) + 1) ^ (moment + 1) *
          manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
      trafficIntensity * (predecessor + 1 : ℝ) *
        (∑ state ∈ Finset.range predecessor,
          ((state : ℝ) + 1) ^ moment *
            manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
    calc
      ∑ state ∈ Finset.range predecessor,
          ((state : ℝ) + 1) ^ (moment + 1) *
            manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
          ∑ state ∈ Finset.range predecessor,
            trafficIntensity * (predecessor + 1 : ℝ) *
              (((state : ℝ) + 1) ^ moment *
                manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
              apply Finset.sum_congr rfl
              intro state hstate
              have hrec := manyServerStationaryMass_head_recurrence trafficIntensity
                (predecessor + 1) state
                (lt_trans (Finset.mem_range.mp hstate) (Nat.lt_succ_self predecessor))
              norm_num [Nat.cast_add, Nat.cast_one] at hrec
              calc
                ((state : ℝ) + 1) ^ (moment + 1) *
                    manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
                    ((state : ℝ) + 1) ^ moment *
                      (((state : ℝ) + 1) *
                        manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1)) := by
                      rw [pow_succ]
                      ring
                _ = ((state : ℝ) + 1) ^ moment *
                      ((predecessor + 1 : ℝ) * trafficIntensity *
                        manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
                      rw [show ((state : ℝ) + 1) *
                        manyServerStationaryMass trafficIntensity (predecessor + 1) (state + 1) =
                        (predecessor + 1 : ℝ) * trafficIntensity *
                          manyServerStationaryMass trafficIntensity (predecessor + 1) state by
                          exact hrec]
                _ = trafficIntensity * (predecessor + 1 : ℝ) *
                      (((state : ℝ) + 1) ^ moment *
                        manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
                      ring
      _ = trafficIntensity * (predecessor + 1 : ℝ) *
        (∑ state ∈ Finset.range predecessor,
          ((state : ℝ) + 1) ^ moment *
            manyServerStationaryMass trafficIntensity (predecessor + 1) state) := by
          rw [Finset.mul_sum]
  rw [hshift]
  have hprefix :
      (∑ state ∈ Finset.range predecessor,
        ((state : ℝ) + 1) ^ moment *
          manyServerStationaryMass trafficIntensity (predecessor + 1) state) =
      (∑ state ∈ Finset.range (predecessor + 1),
        ((state : ℝ) + 1) ^ moment *
          manyServerStationaryMass trafficIntensity (predecessor + 1) state) -
        ((predecessor : ℝ) + 1) ^ moment *
          manyServerStationaryMass trafficIntensity (predecessor + 1) predecessor := by
    rw [Finset.sum_range_succ]
    ring
  rw [hprefix]
  simp only [Nat.cast_succ, Nat.succ_sub_one]

/-- Adding one inside the first head raw moment expands into the first and
zeroth moments. -/
theorem manyServerStationaryHeadShiftedRawMoment_one
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadShiftedRawMoment trafficIntensity servers 1 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadShiftedRawMoment manyServerStationaryHeadRawMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state hstate
  simp only [pow_one]
  ring

/-- The second finite-head raw moment in closed form. -/
theorem manyServerStationaryHeadRawMoment_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadRawMoment trafficIntensity servers 2 =
      (trafficIntensity * (servers : ℝ)) ^ 2 -
        (servers : ℝ) ^ 2 * manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) := by
  rw [manyServerStationaryHeadRawMoment_succ (trafficIntensity := trafficIntensity)
      servers 1 hservers,
    manyServerStationaryHeadShiftedRawMoment_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos
      htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos
      htraffic_lt_one,
    manyServerStationaryMass_before_full_eq_delay_mul (trafficIntensity := trafficIntensity)
      servers hservers
      htraffic_pos htraffic_lt_one]
  have htraffic_ne : trafficIntensity ≠ 0 := htraffic_pos.ne'
  field_simp [htraffic_ne]
  ring

/-- Adding one inside the second head raw moment expands by the quadratic
binomial formula. -/
theorem manyServerStationaryHeadShiftedRawMoment_two
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadShiftedRawMoment trafficIntensity servers 2 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 2 +
        2 * manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadShiftedRawMoment manyServerStationaryHeadRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) + 1) ^ 2 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state +
          2 * ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state) +
          manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) +
        (∑ state ∈ Finset.range servers,
          2 * ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state)) +
        (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) +
        2 * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 1 * manyServerStationaryMass trafficIntensity servers state) +
        (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 0 * manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.mul_sum]
          simp only [pow_one, pow_zero, one_mul]

/-- The third finite-head raw moment in closed form. -/
theorem manyServerStationaryHeadRawMoment_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadRawMoment trafficIntensity servers 3 =
      (trafficIntensity * (servers : ℝ)) ^ 3 -
        (servers : ℝ) ^ 3 * manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) ^ 2 *
          (2 * trafficIntensity -
            2 * manyServerDelayProbability trafficIntensity servers +
            trafficIntensity * (1 - manyServerDelayProbability trafficIntensity servers)) +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) := by
  rw [manyServerStationaryHeadRawMoment_succ (trafficIntensity := trafficIntensity)
      servers 2 hservers,
    manyServerStationaryHeadShiftedRawMoment_two,
    manyServerStationaryHeadRawMoment_two (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryMass_before_full_eq_delay_mul (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one]
  have htraffic_ne : trafficIntensity ≠ 0 := htraffic_pos.ne'
  field_simp [htraffic_ne]
  ring

/-- Adding one inside the third head raw moment expands by the cubic binomial
formula. -/
theorem manyServerStationaryHeadShiftedRawMoment_three
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadShiftedRawMoment trafficIntensity servers 3 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 3 +
        3 * manyServerStationaryHeadRawMoment trafficIntensity servers 2 +
        3 * manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadShiftedRawMoment manyServerStationaryHeadRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) + 1) ^ 3 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        ((state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state +
          3 * ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) +
          3 * ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state) +
          manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) +
        (∑ state ∈ Finset.range servers,
          3 * ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state)) +
        (∑ state ∈ Finset.range servers,
          3 * ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state)) +
        (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.sum_add_distrib]
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) +
        3 * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) +
        3 * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 1 * manyServerStationaryMass trafficIntensity servers state) +
        (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 0 * manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          simp only [pow_one, pow_zero, one_mul]

/-- The fourth finite-head raw moment in closed form. -/
theorem manyServerStationaryHeadRawMoment_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryHeadRawMoment trafficIntensity servers 4 =
      (trafficIntensity * (servers : ℝ)) ^ 4 -
        (servers : ℝ) ^ 4 * manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) ^ 3 *
          (6 * trafficIntensity ^ 2 -
            trafficIntensity ^ 2 * manyServerDelayProbability trafficIntensity servers -
            2 * trafficIntensity * manyServerDelayProbability trafficIntensity servers -
            3 * manyServerDelayProbability trafficIntensity servers) +
        trafficIntensity * (servers : ℝ) ^ 2 *
          (7 * trafficIntensity -
            4 * trafficIntensity * manyServerDelayProbability trafficIntensity servers -
            3 * manyServerDelayProbability trafficIntensity servers) +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) := by
  rw [manyServerStationaryHeadRawMoment_succ (trafficIntensity := trafficIntensity)
      servers 3 hservers,
    manyServerStationaryHeadShiftedRawMoment_three,
    manyServerStationaryHeadRawMoment_three (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_two (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryMass_before_full_eq_delay_mul (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one]
  have htraffic_ne : trafficIntensity ≠ 0 := htraffic_pos.ne'
  field_simp [htraffic_ne]
  ring

/-- The raw moment of the stationary offset above full occupancy. -/
noncomputable def manyServerStationaryDelayedOffsetRawMoment
    (trafficIntensity : ℝ) (servers moment : ℕ) : ℝ :=
  ∑' tail : ℕ, (tail : ℝ) ^ moment *
    manyServerStationaryMass trafficIntensity servers (tail + servers)

/-- The zeroth delayed-offset raw moment is the all-servers-busy
probability. -/
theorem manyServerStationaryDelayedOffsetRawMoment_zero
    {trafficIntensity : ℝ} (servers : ℕ)
    (htraffic_nonneg : 0 ≤ trafficIntensity) (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers 0 =
      manyServerDelayProbability trafficIntensity servers := by
  unfold manyServerStationaryDelayedOffsetRawMoment
  simpa only [pow_zero, one_mul] using
    (hasSum_manyServerStationaryMass_delayedTail trafficIntensity servers
      htraffic_nonneg htraffic_lt_one).tsum_eq

/-- The first delayed-offset raw moment in closed form. -/
theorem manyServerStationaryDelayedOffsetRawMoment_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers 1 =
      manyServerDelayProbability trafficIntensity servers * trafficIntensity /
        (1 - trafficIntensity) := by
  unfold manyServerStationaryDelayedOffsetRawMoment
  simpa only [pow_one] using
    (hasSum_manyServerStationaryDelayedOffset_pow_one servers hservers htraffic_pos
      htraffic_lt_one).tsum_eq

/-- The second delayed-offset raw moment in closed form. -/
theorem manyServerStationaryDelayedOffsetRawMoment_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers 2 =
      manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + trafficIntensity) / (1 - trafficIntensity) ^ 2 := by
  unfold manyServerStationaryDelayedOffsetRawMoment
  exact (hasSum_manyServerStationaryDelayedOffset_pow_two servers hservers htraffic_pos
    htraffic_lt_one).tsum_eq

/-- The third delayed-offset raw moment in closed form. -/
theorem manyServerStationaryDelayedOffsetRawMoment_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers 3 =
      manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + 4 * trafficIntensity + trafficIntensity ^ 2) /
          (1 - trafficIntensity) ^ 3 := by
  unfold manyServerStationaryDelayedOffsetRawMoment
  exact (hasSum_manyServerStationaryDelayedOffset_pow_three servers hservers htraffic_pos
    htraffic_lt_one).tsum_eq

/-- The fourth delayed-offset raw moment in closed form. -/
theorem manyServerStationaryDelayedOffsetRawMoment_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers 4 =
      manyServerDelayProbability trafficIntensity servers * trafficIntensity *
        (1 + 11 * trafficIntensity + 11 * trafficIntensity ^ 2 + trafficIntensity ^ 3) /
          (1 - trafficIntensity) ^ 4 := by
  unfold manyServerStationaryDelayedOffsetRawMoment
  exact (hasSum_manyServerStationaryDelayedOffset_pow_four servers hservers htraffic_pos
    htraffic_lt_one).tsum_eq

/-- The raw moment of the centered stationary queue length on the finite
strictly-underloaded branch. -/
noncomputable def manyServerStationaryHeadCenteredRawMoment
    (trafficIntensity : ℝ) (servers moment : ℕ) : ℝ :=
  ∑ state ∈ Finset.range servers,
    ((state : ℝ) - servers) ^ moment *
      manyServerStationaryMass trafficIntensity servers state

/-- The first centered head moment is its raw first moment minus the
threshold times the finite-head mass. -/
theorem manyServerStationaryHeadCenteredRawMoment_one
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadCenteredRawMoment trafficIntensity servers 1 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 1 -
        (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadCenteredRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) - servers) ^ 1 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state -
          (servers : ℝ) * manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) * manyServerStationaryMass trafficIntensity servers state) -
        (servers : ℝ) * (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = manyServerStationaryHeadRawMoment trafficIntensity servers 1 -
        (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
          unfold manyServerStationaryHeadRawMoment
          simp only [pow_one, pow_zero, one_mul]

/-- The second centered head moment is the corresponding quadratic expansion. -/
theorem manyServerStationaryHeadCenteredRawMoment_two
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadCenteredRawMoment trafficIntensity servers 2 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 2 -
        2 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        (servers : ℝ) ^ 2 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadCenteredRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) - servers) ^ 2 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state -
          2 * (servers : ℝ) *
            ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state) +
          (servers : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) -
        2 * (servers : ℝ) * (∑ state ∈ Finset.range servers,
          (state : ℝ) * manyServerStationaryMass trafficIntensity servers state) +
        (servers : ℝ) ^ 2 * (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum]
    _ = manyServerStationaryHeadRawMoment trafficIntensity servers 2 -
        2 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        (servers : ℝ) ^ 2 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
          unfold manyServerStationaryHeadRawMoment
          simp only [pow_one, pow_zero, one_mul]

/-- The third centered head moment is the corresponding cubic expansion. -/
theorem manyServerStationaryHeadCenteredRawMoment_three
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadCenteredRawMoment trafficIntensity servers 3 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 3 -
        3 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 2 +
        3 * (servers : ℝ) ^ 2 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 1 -
        (servers : ℝ) ^ 3 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadCenteredRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) - servers) ^ 3 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        (((state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state -
          3 * (servers : ℝ) *
            ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state)) +
          3 * (servers : ℝ) ^ 2 *
            ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state) -
          (servers : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = ((∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) -
        3 * (servers : ℝ) * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) +
        3 * (servers : ℝ) ^ 2 * (∑ state ∈ Finset.range servers,
          (state : ℝ) * manyServerStationaryMass trafficIntensity servers state)) -
        (servers : ℝ) ^ 3 * (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
    _ = manyServerStationaryHeadRawMoment trafficIntensity servers 3 -
        3 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 2 +
        3 * (servers : ℝ) ^ 2 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 1 -
        (servers : ℝ) ^ 3 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
          unfold manyServerStationaryHeadRawMoment
          simp only [pow_one, pow_zero, one_mul]

/-- The fourth centered head moment is the corresponding quartic expansion. -/
theorem manyServerStationaryHeadCenteredRawMoment_four
    (trafficIntensity : ℝ) (servers : ℕ) :
    manyServerStationaryHeadCenteredRawMoment trafficIntensity servers 4 =
      manyServerStationaryHeadRawMoment trafficIntensity servers 4 -
        4 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 3 +
        6 * (servers : ℝ) ^ 2 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 2 -
        4 * (servers : ℝ) ^ 3 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        (servers : ℝ) ^ 4 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
  unfold manyServerStationaryHeadCenteredRawMoment
  calc
    ∑ state ∈ Finset.range servers, ((state : ℝ) - servers) ^ 4 *
        manyServerStationaryMass trafficIntensity servers state =
      ∑ state ∈ Finset.range servers,
        ((state : ℝ) ^ 4 * manyServerStationaryMass trafficIntensity servers state -
          4 * (servers : ℝ) *
            ((state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) +
          6 * (servers : ℝ) ^ 2 *
            ((state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state) -
          4 * (servers : ℝ) ^ 3 *
            ((state : ℝ) * manyServerStationaryMass trafficIntensity servers state) +
          (servers : ℝ) ^ 4 * manyServerStationaryMass trafficIntensity servers state) := by
          apply Finset.sum_congr rfl
          intro state hstate
          ring
    _ = (((∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 4 * manyServerStationaryMass trafficIntensity servers state) -
        4 * (servers : ℝ) * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 3 * manyServerStationaryMass trafficIntensity servers state) +
        6 * (servers : ℝ) ^ 2 * (∑ state ∈ Finset.range servers,
          (state : ℝ) ^ 2 * manyServerStationaryMass trafficIntensity servers state)) -
        4 * (servers : ℝ) ^ 3 * (∑ state ∈ Finset.range servers,
          (state : ℝ) * manyServerStationaryMass trafficIntensity servers state)) +
        (servers : ℝ) ^ 4 * (∑ state ∈ Finset.range servers,
          manyServerStationaryMass trafficIntensity servers state) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    _ = manyServerStationaryHeadRawMoment trafficIntensity servers 4 -
        4 * (servers : ℝ) * manyServerStationaryHeadRawMoment trafficIntensity servers 3 +
        6 * (servers : ℝ) ^ 2 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 2 -
        4 * (servers : ℝ) ^ 3 *
          manyServerStationaryHeadRawMoment trafficIntensity servers 1 +
        (servers : ℝ) ^ 4 * manyServerStationaryHeadRawMoment trafficIntensity servers 0 := by
          unfold manyServerStationaryHeadRawMoment
          simp only [pow_one, pow_zero, one_mul]

/-- The raw centered stationary queue-length moment, split at full
occupancy. -/
noncomputable def manyServerCenteredStationaryRawMoment
    (trafficIntensity : ℝ) (servers moment : ℕ) : ℝ :=
  manyServerStationaryHeadCenteredRawMoment trafficIntensity servers moment +
    manyServerStationaryDelayedOffsetRawMoment trafficIntensity servers moment

/-- The first centered stationary mass series is summable, and its sum is the
head/tail moment decomposition. -/
theorem hasSum_manyServerCenteredStationaryRawMoment_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun state : ℕ => ((state : ℝ) - servers) ^ 1 *
        manyServerStationaryMass trafficIntensity servers state)
      (manyServerCenteredStationaryRawMoment trafficIntensity servers 1) := by
  unfold manyServerCenteredStationaryRawMoment
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_one
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ((state : ℝ) - servers) ^ 1 *
      manyServerStationaryMass trafficIntensity servers state) servers).mp (by
      convert htail using 1
      ext tail
      norm_num)
  convert hfull using 1
  rw [manyServerStationaryDelayedOffsetRawMoment_one servers hservers htraffic_pos
    htraffic_lt_one]
  unfold manyServerStationaryHeadCenteredRawMoment
  ring

/-- The second centered stationary mass series is summable, and its sum is the
head/tail moment decomposition. -/
theorem hasSum_manyServerCenteredStationaryRawMoment_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun state : ℕ => ((state : ℝ) - servers) ^ 2 *
        manyServerStationaryMass trafficIntensity servers state)
      (manyServerCenteredStationaryRawMoment trafficIntensity servers 2) := by
  unfold manyServerCenteredStationaryRawMoment
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_two
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ((state : ℝ) - servers) ^ 2 *
      manyServerStationaryMass trafficIntensity servers state) servers).mp (by
      convert htail using 1
      ext tail
      norm_num)
  convert hfull using 1
  rw [manyServerStationaryDelayedOffsetRawMoment_two servers hservers htraffic_pos
    htraffic_lt_one]
  unfold manyServerStationaryHeadCenteredRawMoment
  ring

/-- The third centered stationary mass series is summable, and its sum is the
head/tail moment decomposition. -/
theorem hasSum_manyServerCenteredStationaryRawMoment_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun state : ℕ => ((state : ℝ) - servers) ^ 3 *
        manyServerStationaryMass trafficIntensity servers state)
      (manyServerCenteredStationaryRawMoment trafficIntensity servers 3) := by
  unfold manyServerCenteredStationaryRawMoment
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_three
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ((state : ℝ) - servers) ^ 3 *
      manyServerStationaryMass trafficIntensity servers state) servers).mp (by
      convert htail using 1
      ext tail
      norm_num)
  convert hfull using 1
  rw [manyServerStationaryDelayedOffsetRawMoment_three servers hservers htraffic_pos
    htraffic_lt_one]
  unfold manyServerStationaryHeadCenteredRawMoment
  ring

/-- The fourth centered stationary mass series is summable, and its sum is the
head/tail moment decomposition. -/
theorem hasSum_manyServerCenteredStationaryRawMoment_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    HasSum
      (fun state : ℕ => ((state : ℝ) - servers) ^ 4 *
        manyServerStationaryMass trafficIntensity servers state)
      (manyServerCenteredStationaryRawMoment trafficIntensity servers 4) := by
  unfold manyServerCenteredStationaryRawMoment
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_four
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ((state : ℝ) - servers) ^ 4 *
      manyServerStationaryMass trafficIntensity servers state) servers).mp (by
      convert htail using 1
      ext tail
      norm_num)
  convert hfull using 1
  rw [manyServerStationaryDelayedOffsetRawMoment_four servers hservers htraffic_pos
    htraffic_lt_one]
  unfold manyServerStationaryHeadCenteredRawMoment
  ring

/-- The absolute first centered stationary mass series is summable. -/
theorem summable_norm_manyServerCenteredStationaryRawMoment_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    Summable
      (fun state : ℕ => ‖((state : ℝ) - servers) ^ 1 *
        manyServerStationaryMass trafficIntensity servers state‖) := by
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_one
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ‖((state : ℝ) - servers) ^ 1 *
      manyServerStationaryMass trafficIntensity servers state‖) servers).mp
    (htail.congr_fun fun tail => by
      have hcoordinate :
          (((tail + servers : ℕ) : ℝ) - servers) ^ 1 = (tail : ℝ) := by
        norm_num
      rw [hcoordinate]
      exact Real.norm_of_nonneg (mul_nonneg (by positivity)
        (manyServerStationaryMass_nonneg servers (tail + servers)
          htraffic_pos.le htraffic_lt_one)))
  exact hfull.summable

/-- The absolute second centered stationary mass series is summable. -/
theorem summable_norm_manyServerCenteredStationaryRawMoment_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    Summable
      (fun state : ℕ => ‖((state : ℝ) - servers) ^ 2 *
        manyServerStationaryMass trafficIntensity servers state‖) := by
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_two
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ‖((state : ℝ) - servers) ^ 2 *
      manyServerStationaryMass trafficIntensity servers state‖) servers).mp
    (htail.congr_fun fun tail => by
      have hcoordinate :
          (((tail + servers : ℕ) : ℝ) - servers) ^ 2 = (tail : ℝ) ^ 2 := by
        norm_num
      rw [hcoordinate]
      exact Real.norm_of_nonneg (mul_nonneg (by positivity)
        (manyServerStationaryMass_nonneg servers (tail + servers)
          htraffic_pos.le htraffic_lt_one)))
  exact hfull.summable

/-- The absolute third centered stationary mass series is summable. -/
theorem summable_norm_manyServerCenteredStationaryRawMoment_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    Summable
      (fun state : ℕ => ‖((state : ℝ) - servers) ^ 3 *
        manyServerStationaryMass trafficIntensity servers state‖) := by
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_three
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ‖((state : ℝ) - servers) ^ 3 *
      manyServerStationaryMass trafficIntensity servers state‖) servers).mp
    (htail.congr_fun fun tail => by
      have hcoordinate :
          (((tail + servers : ℕ) : ℝ) - servers) ^ 3 = (tail : ℝ) ^ 3 := by
        norm_num
      rw [hcoordinate]
      exact Real.norm_of_nonneg (mul_nonneg (by positivity)
        (manyServerStationaryMass_nonneg servers (tail + servers)
          htraffic_pos.le htraffic_lt_one)))
  exact hfull.summable

/-- The absolute fourth centered stationary mass series is summable. -/
theorem summable_norm_manyServerCenteredStationaryRawMoment_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    Summable
      (fun state : ℕ => ‖((state : ℝ) - servers) ^ 4 *
        manyServerStationaryMass trafficIntensity servers state‖) := by
  have htail := hasSum_manyServerStationaryDelayedOffset_pow_four
    servers hservers htraffic_pos htraffic_lt_one
  have hfull := (hasSum_nat_add_iff
    (f := fun state : ℕ => ‖((state : ℝ) - servers) ^ 4 *
      manyServerStationaryMass trafficIntensity servers state‖) servers).mp
    (htail.congr_fun fun tail => by
      have hcoordinate :
          (((tail + servers : ℕ) : ℝ) - servers) ^ 4 = (tail : ℝ) ^ 4 := by
        norm_num
      rw [hcoordinate]
      exact Real.norm_of_nonneg (mul_nonneg (by positivity)
        (manyServerStationaryMass_nonneg servers (tail + servers)
          htraffic_pos.le htraffic_lt_one)))
  exact hfull.summable

/-- The first centered stationary raw moment. -/
theorem manyServerCenteredStationaryRawMoment_one
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerCenteredStationaryRawMoment trafficIntensity servers 1 =
      -(servers : ℝ) * (1 - trafficIntensity) +
        trafficIntensity / (1 - trafficIntensity) *
          manyServerDelayProbability trafficIntensity servers := by
  unfold manyServerCenteredStationaryRawMoment
  rw [manyServerStationaryHeadCenteredRawMoment_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryDelayedOffsetRawMoment_one servers hservers htraffic_pos
      htraffic_lt_one]
  have hgap_ne : 1 - trafficIntensity ≠ 0 := by linarith
  field_simp [hgap_ne]
  ring

/-- The second centered stationary raw moment. -/
theorem manyServerCenteredStationaryRawMoment_two
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerCenteredStationaryRawMoment trafficIntensity servers 2 =
      (servers : ℝ) ^ 2 * (1 - trafficIntensity) ^ 2 +
        2 * trafficIntensity ^ 2 / (1 - trafficIntensity) ^ 2 *
          manyServerDelayProbability trafficIntensity servers +
        trafficIntensity / (1 - trafficIntensity) *
          manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) := by
  unfold manyServerCenteredStationaryRawMoment
  rw [manyServerStationaryHeadCenteredRawMoment_two,
    manyServerStationaryHeadRawMoment_two (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryDelayedOffsetRawMoment_two servers hservers htraffic_pos
      htraffic_lt_one]
  have hgap_ne : 1 - trafficIntensity ≠ 0 := by linarith
  field_simp [hgap_ne]
  ring

/-- The third centered stationary raw moment. -/
theorem manyServerCenteredStationaryRawMoment_three
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerCenteredStationaryRawMoment trafficIntensity servers 3 =
      -(servers : ℝ) ^ 3 * (1 - trafficIntensity) ^ 3 -
        (servers : ℝ) ^ 2 * trafficIntensity * (1 - trafficIntensity) *
          (3 - manyServerDelayProbability trafficIntensity servers) +
        6 * trafficIntensity ^ 3 / (1 - trafficIntensity) ^ 3 *
          manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) +
        6 * manyServerDelayProbability trafficIntensity servers * trafficIntensity ^ 2 /
          (1 - trafficIntensity) ^ 2 +
        manyServerDelayProbability trafficIntensity servers * trafficIntensity /
          (1 - trafficIntensity) := by
  unfold manyServerCenteredStationaryRawMoment
  rw [manyServerStationaryHeadCenteredRawMoment_three,
    manyServerStationaryHeadRawMoment_three (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_two (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryDelayedOffsetRawMoment_three servers hservers htraffic_pos
      htraffic_lt_one]
  have hgap_ne : 1 - trafficIntensity ≠ 0 := by linarith
  field_simp [hgap_ne]
  ring

/-- The fourth centered stationary raw moment. -/
theorem manyServerCenteredStationaryRawMoment_four
    {trafficIntensity : ℝ} (servers : ℕ)
    (hservers : 0 < servers) (htraffic_pos : 0 < trafficIntensity)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerCenteredStationaryRawMoment trafficIntensity servers 4 =
      (servers : ℝ) ^ 4 * (1 - trafficIntensity) ^ 4 +
        (servers : ℝ) ^ 3 *
          (6 * trafficIntensity * (1 - trafficIntensity) ^ 2 -
            manyServerDelayProbability trafficIntensity servers * trafficIntensity *
              (1 - trafficIntensity) ^ 2) +
        (servers : ℝ) ^ 2 * trafficIntensity *
          (7 * trafficIntensity -
            4 * trafficIntensity * manyServerDelayProbability trafficIntensity servers +
            manyServerDelayProbability trafficIntensity servers - 4) +
        24 * trafficIntensity ^ 4 / (1 - trafficIntensity) ^ 4 *
          manyServerDelayProbability trafficIntensity servers +
        trafficIntensity * (servers : ℝ) *
          (1 - manyServerDelayProbability trafficIntensity servers) +
        36 * trafficIntensity ^ 3 / (1 - trafficIntensity) ^ 3 *
          manyServerDelayProbability trafficIntensity servers +
        14 * trafficIntensity ^ 2 / (1 - trafficIntensity) ^ 2 *
          manyServerDelayProbability trafficIntensity servers +
        trafficIntensity / (1 - trafficIntensity) *
          manyServerDelayProbability trafficIntensity servers := by
  unfold manyServerCenteredStationaryRawMoment
  rw [manyServerStationaryHeadCenteredRawMoment_four,
    manyServerStationaryHeadRawMoment_four (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_three (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_two (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_one (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryHeadRawMoment_zero (trafficIntensity := trafficIntensity)
      servers hservers htraffic_pos htraffic_lt_one,
    manyServerStationaryDelayedOffsetRawMoment_four servers hservers htraffic_pos
      htraffic_lt_one]
  have hgap_ne : 1 - trafficIntensity ≠ 0 := by linarith
  field_simp [hgap_ne]
  ring

end AppliedModelingLib.Probability.Queueing
