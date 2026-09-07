import AppliedModelingLib.Queueing.ManyServerBirthDeath
import AppliedModelingLib.Queueing.MM1.Uniformization
import Mathlib.Tactic

/-!
# Uniformized many-server birth--death queues

This module constructs the discrete potential-event jump kernel for a queue
with a constant arrival stream and finitely many identical exponential-service
clocks.  It proves that the normalized factorial/geometric mass from
`ManyServerBirthDeath` is reversible for that kernel.  A continuous-time
Poisson-clock construction is a further, separate path-space result.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped ENNReal NNReal

/-- The fraction of a finite server pool that is busy at a queue length. -/
noncomputable def manyServerBusyFraction (servers state : ℕ) : ℝ≥0 :=
  (Nat.min state servers : ℝ≥0) / (servers : ℝ≥0)

/-- Increasing the queue length cannot decrease the fraction of a fixed
server pool that is busy. -/
theorem monotone_manyServerBusyFraction (servers : ℕ) :
    Monotone (manyServerBusyFraction servers) := by
  intro first second hfirstSecond
  unfold manyServerBusyFraction
  apply div_le_div_of_nonneg_right
  · exact_mod_cast min_le_min hfirstSecond le_rfl
  · positivity

/-- The idle fraction of a fixed nonempty server pool is antitone in the
queue length. -/
theorem antitone_one_sub_manyServerBusyFraction (servers : ℕ) :
    Antitone (fun state : ℕ => 1 - (manyServerBusyFraction servers state : ℝ)) := by
  intro first second hfirstSecond
  exact sub_le_sub_left
    (by exact_mod_cast monotone_manyServerBusyFraction servers hfirstSecond) 1

/-- A busy fraction cannot exceed one when the server pool is nonempty. -/
theorem manyServerBusyFraction_le_one (servers state : ℕ) (hservers : 0 < servers) :
    manyServerBusyFraction servers state ≤ 1 := by
  unfold manyServerBusyFraction
  apply (div_le_one₀ (by exact_mod_cast hservers)).mpr
  exact_mod_cast Nat.min_le_right state servers

/-- The idle fraction of a nonempty server pool is exactly the unused-server
count divided by the pool size. -/
theorem one_sub_manyServerBusyFraction_eq_unusedFraction
    (servers state : ℕ) (hservers : 0 < servers) :
    1 - (manyServerBusyFraction servers state : ℝ) =
      ((servers - state : ℕ) : ℝ) / (servers : ℝ) := by
  have hservers_ne : (servers : ℝ) ≠ 0 := by
    exact_mod_cast ne_of_gt hservers
  change 1 - ((Nat.min state servers : ℝ) / (servers : ℝ)) =
    ((servers - state : ℕ) : ℝ) / (servers : ℝ)
  by_cases hstate : state ≤ servers
  · simp only [Nat.min_eq_left hstate]
    rw [Nat.cast_sub hstate]
    field_simp [hservers_ne]
  · have hservers_le : servers ≤ state := Nat.le_of_not_ge hstate
    simp only [Nat.min_eq_right hservers_le]
    rw [Nat.sub_eq_zero_of_le hservers_le]
    simp [hservers_ne]

/-- Raising a queue length by one changes the busy fraction of a nonempty
server pool by at most one server's share. -/
theorem manyServerBusyFraction_succ_sub_nonneg_le_one_div
    (servers state : ℕ) (hservers : 0 < servers) :
    0 ≤ (manyServerBusyFraction servers (state + 1) : ℝ) -
        manyServerBusyFraction servers state ∧
      (manyServerBusyFraction servers (state + 1) : ℝ) -
        manyServerBusyFraction servers state ≤ 1 / (servers : ℝ) := by
  have hservers_real : 0 < (servers : ℝ) := by exact_mod_cast hservers
  have hservers_ne : (servers : ℝ) ≠ 0 := hservers_real.ne'
  change 0 ≤ ((Nat.min (state + 1) servers : ℝ) / (servers : ℝ)) -
        ((Nat.min state servers : ℝ) / (servers : ℝ)) ∧
      ((Nat.min (state + 1) servers : ℝ) / (servers : ℝ)) -
        ((Nat.min state servers : ℝ) / (servers : ℝ)) ≤ 1 / (servers : ℝ)
  by_cases hstate : state < servers
  · have hstate_le : state ≤ servers := Nat.le_of_lt hstate
    have hsucc_le : state + 1 ≤ servers := by omega
    simp only [Nat.min_eq_left hsucc_le, Nat.min_eq_left hstate_le,
      Nat.cast_add, Nat.cast_one]
    have heq : ((state : ℝ) + 1) / (servers : ℝ) - (state : ℝ) / (servers : ℝ) =
        1 / (servers : ℝ) := by
      field_simp [hservers_ne]
      ring
    rw [heq]
    constructor
    · exact one_div_nonneg.mpr hservers_real.le
    · exact le_rfl
  · have hservers_le : servers ≤ state := Nat.le_of_not_gt hstate
    have hservers_le_succ : servers ≤ state + 1 := by omega
    simp only [Nat.min_eq_right hservers_le_succ, Nat.min_eq_right hservers_le]
    constructor <;> simp [hservers_ne]

/-- Along one nearest-neighbour queue transition, the idle fraction changes by
at most one server's share. -/
theorem abs_one_sub_manyServerBusyFraction_sub_le_one_div
    (servers current next : ℕ) (hservers : 0 < servers)
    (hstep : next = current + 1 ∨ next = current ∨ next = current - 1) :
    |(1 - (manyServerBusyFraction servers next : ℝ)) -
        (1 - (manyServerBusyFraction servers current : ℝ))| ≤ 1 / (servers : ℝ) := by
  rcases hstep with hnext | hnext | hnext
  · subst next
    rw [show (1 - (manyServerBusyFraction servers (current + 1) : ℝ)) -
          (1 - (manyServerBusyFraction servers current : ℝ)) =
        -((manyServerBusyFraction servers (current + 1) : ℝ) -
          manyServerBusyFraction servers current) by ring]
    rw [abs_neg]
    rw [abs_of_nonneg
      (manyServerBusyFraction_succ_sub_nonneg_le_one_div
        servers current hservers).1]
    exact (manyServerBusyFraction_succ_sub_nonneg_le_one_div
      servers current hservers).2
  · subst next
    simp
  · cases current with
    | zero =>
        subst next
        simp
    | succ previous =>
        have hnext_eq : next = previous := by omega
        subst next
        rw [hnext_eq]
        rw [show (1 - (manyServerBusyFraction servers previous : ℝ)) -
              (1 - (manyServerBusyFraction servers (previous + 1) : ℝ)) =
            (manyServerBusyFraction servers (previous + 1) : ℝ) -
              manyServerBusyFraction servers previous by ring]
        rw [abs_of_nonneg
          (manyServerBusyFraction_succ_sub_nonneg_le_one_div
            servers previous hservers).1]
        exact (manyServerBusyFraction_succ_sub_nonneg_le_one_div
          servers previous hservers).2

/-- The potential-event uniformization of a many-server birth--death queue.
A birth is selected with probability `ρ / (1 + ρ)`.  Otherwise a potential
service completion is selected; it changes the state exactly when that clock
belongs to a busy server, and is a self-loop otherwise. -/
noncomputable def manyServerUniformizedKernel
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) :
    CountableMarkovKernel ℕ :=
  fun state => (PMF.bernoulli (uniformizedBirthProbability trafficIntensity)
    (uniformizedBirthProbability_le_one trafficIntensity)).bind fun birth =>
      if birth then PMF.pure (state + 1) else
        (PMF.bernoulli (manyServerBusyFraction servers state)
          (manyServerBusyFraction_le_one servers state hservers)).map
          (fun service => if service then state - 1 else state)

/-- The zero-state row has only a birth transition and a reflected
non-birth self-loop. -/
lemma manyServerUniformizedKernel_apply_zero
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers) (y : ℕ) :
    manyServerUniformizedKernel trafficIntensity servers hservers 0 y =
      if y = 1 then (uniformizedBirthProbability trafficIntensity : ℝ≥0∞) else
        if y = 0 then (1 - uniformizedBirthProbability trafficIntensity : ℝ≥0) else 0 := by
  rw [manyServerUniformizedKernel, PMF.bind_apply, tsum_bool]
  simp [PMF.bernoulli_apply, PMF.map_apply]
  have hbusy : manyServerBusyFraction servers 0 ≤ 1 :=
    manyServerBusyFraction_le_one servers 0 hservers
  have hsplit :
      (↑(manyServerBusyFraction servers 0) : ℝ≥0∞) +
        (1 - ↑(manyServerBusyFraction servers 0)) = 1 := by
    exact add_tsub_cancel_of_le (by exact_mod_cast hbusy)
  by_cases hy0 : y = 0
  · subst y
    simp only [ite_true]
    rw [hsplit]
    simp
  by_cases hy1 : y = 1
  · subst y
    simp
  · simp [hy0, hy1]

/-- Away from zero, a row has a birth probability, a busy-service death
probability, and the remaining probability as a self-loop. -/
lemma manyServerUniformizedKernel_apply_succ
    (trafficIntensity : ℝ≥0) (servers n : ℕ) (hservers : 0 < servers) (y : ℕ) :
    manyServerUniformizedKernel trafficIntensity servers hservers (n + 1) y =
      if y = n + 2 then (uniformizedBirthProbability trafficIntensity : ℝ≥0∞) else
        if y = n then
          ((1 - uniformizedBirthProbability trafficIntensity) *
            manyServerBusyFraction servers (n + 1) : ℝ≥0) else
        if y = n + 1 then
          ((1 - uniformizedBirthProbability trafficIntensity) *
            (1 - manyServerBusyFraction servers (n + 1)) : ℝ≥0) else 0 := by
  rw [manyServerUniformizedKernel, PMF.bind_apply, tsum_bool]
  simp [PMF.bernoulli_apply, PMF.map_apply]
  by_cases hy0 : y = n + 2
  · subst y
    simp
  by_cases hy1 : y = n
  · subst y
    simp [hy0]
  by_cases hy2 : y = n + 1
  · subst y
    simp
  · simp [hy0, hy1, hy2]

/-- The real-valued stationary mass obeys the edge balance relation after
uniformizing the total potential-event rate. -/
theorem manyServerStationaryMass_edge_balance_real
    (trafficIntensity : ℝ) (servers n : ℕ) (hservers : 0 < servers)
    (htraffic_nonneg : 0 ≤ trafficIntensity) :
    manyServerStationaryMass trafficIntensity servers n *
      (trafficIntensity / (1 + trafficIntensity)) =
    manyServerStationaryMass trafficIntensity servers (n + 1) *
      ((1 / (1 + trafficIntensity)) *
        ((Nat.min (n + 1) servers : ℝ) / servers)) := by
  have hbalance := manyServerStationaryMass_detailedBalance
    trafficIntensity (1 : ℝ) servers n
  simp only [manyServerBirthDeathRates] at hbalance
  have hservers_ne : (servers : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hservers
  have hdenom_ne : 1 + trafficIntensity ≠ 0 := by linarith
  field_simp [hservers_ne, hdenom_ne]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbalance

/-- The normalized nonnegative-real stationary mass has the same adjacent-edge
balance identity as the potential-event kernel. -/
theorem manyServerStationaryMassNN_edge_balance
    (trafficIntensity : ℝ≥0) (servers n : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryMassNN (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one) n *
        uniformizedBirthProbability trafficIntensity =
      manyServerStationaryMassNN (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one) (n + 1) *
        ((1 - uniformizedBirthProbability trafficIntensity) *
          manyServerBusyFraction servers (n + 1)) := by
  apply NNReal.eq
  rw [uniformizedDeathProbability_eq]
  change manyServerStationaryMass (trafficIntensity : ℝ) servers n *
      ((trafficIntensity : ℝ) / (1 + trafficIntensity)) =
    manyServerStationaryMass (trafficIntensity : ℝ) servers (n + 1) *
      ((1 / (1 + trafficIntensity)) *
        ((Nat.min (n + 1) servers : ℝ) / servers))
  exact manyServerStationaryMass_edge_balance_real
    (trafficIntensity : ℝ) servers n hservers (by positivity)

/-- Every state has the uniformized birth probability for its upward edge. -/
lemma manyServerUniformizedKernel_birth
    (trafficIntensity : ℝ≥0) (servers state : ℕ) (hservers : 0 < servers) :
    manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1) =
      (uniformizedBirthProbability trafficIntensity : ℝ≥0∞) := by
  cases state with
  | zero =>
      rw [manyServerUniformizedKernel_apply_zero]
      simp
  | succ state =>
      rw [manyServerUniformizedKernel_apply_succ]
      simp

/-- The downward edge from a positive state is selected exactly when a
potential service clock belongs to a busy server. -/
lemma manyServerUniformizedKernel_death
    (trafficIntensity : ℝ≥0) (servers state : ℕ) (hservers : 0 < servers) :
    manyServerUniformizedKernel trafficIntensity servers hservers (state + 1) state =
      ((1 - uniformizedBirthProbability trafficIntensity) *
        manyServerBusyFraction servers (state + 1) : ℝ≥0) := by
  rw [manyServerUniformizedKernel_apply_succ]
  simp

/-- The stationary PMF balances each pair of adjacent transitions in the
potential-event kernel. -/
theorem manyServerStationaryPMF_edge_balance
    (trafficIntensity : ℝ≥0) (servers state : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one) state *
      manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1) =
    manyServerStationaryPMF (trafficIntensity : ℝ) servers
      (by positivity) (by exact_mod_cast htraffic_lt_one) (state + 1) *
      manyServerUniformizedKernel trafficIntensity servers hservers (state + 1) state := by
  rw [manyServerUniformizedKernel_birth, manyServerUniformizedKernel_death]
  change (↑(manyServerStationaryMassNN (trafficIntensity : ℝ) servers _ _ state) : ℝ≥0∞) *
      ↑(uniformizedBirthProbability trafficIntensity) =
    (↑(manyServerStationaryMassNN (trafficIntensity : ℝ) servers _ _ (state + 1)) : ℝ≥0∞) *
      ↑((1 - uniformizedBirthProbability trafficIntensity) *
        manyServerBusyFraction servers (state + 1))
  exact_mod_cast manyServerStationaryMassNN_edge_balance
    trafficIntensity servers state hservers htraffic_lt_one

/-- The exact factorial/geometric stationary PMF is reversible for the
potential-event many-server kernel. -/
theorem manyServerStationaryPMF_uniformized_detailedBalance
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    PMFDetailedBalance
      (manyServerUniformizedKernel trafficIntensity servers hservers)
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)) := by
  intro x y
  cases x with
  | zero =>
      cases y with
      | zero => rfl
      | succ y =>
          cases y with
          | zero =>
              exact manyServerStationaryPMF_edge_balance
                trafficIntensity servers 0 hservers htraffic_lt_one
          | succ y =>
              have hy_one : y + 2 ≠ 1 := by omega
              have hy_zero : y + 2 ≠ 0 := by omega
              have hrev_birth : 0 ≠ (y + 1) + 2 := by omega
              have hrev_death : 0 ≠ y + 1 := by omega
              have hrev_stay : 0 ≠ (y + 1) + 1 := by omega
              rw [manyServerUniformizedKernel_apply_zero,
                manyServerUniformizedKernel_apply_succ]
              simp
  | succ x =>
      by_cases hbirth : y = x + 2
      · subst y
        exact manyServerStationaryPMF_edge_balance
          trafficIntensity servers (x + 1) hservers htraffic_lt_one
      by_cases hdeath : y = x
      · subst y
        exact (manyServerStationaryPMF_edge_balance
          trafficIntensity servers x hservers htraffic_lt_one).symm
      by_cases hstay : y = x + 1
      · subst y
        rfl
      cases y with
      | zero =>
          have hx_ne_zero : x ≠ 0 := by
            intro hx
            subst x
            exact hdeath rfl
          have hx_one_ne : x + 1 ≠ 1 := by omega
          rw [manyServerUniformizedKernel_apply_succ,
            manyServerUniformizedKernel_apply_zero]
          simp [hdeath, hx_ne_zero]
      | succ y =>
          have hforward_birth : y + 1 ≠ x + 2 := by
            intro h
            apply hbirth
            omega
          have hforward_death : y + 1 ≠ x := by
            intro h
            apply hdeath
            omega
          have hforward_stay : y + 1 ≠ x + 1 := by
            intro h
            apply hstay
            omega
          have hreverse_birth : x + 1 ≠ y + 2 := by
            intro h
            apply hdeath
            omega
          have hreverse_death : x + 1 ≠ y := by
            intro h
            apply hbirth
            omega
          have hreverse_stay : x + 1 ≠ y + 1 := by
            intro h
            apply hstay
            omega
          have hleft_birth_short : y ≠ x + 1 := by
            intro h
            apply hbirth
            omega
          have hleft_stay_short : y ≠ x := by
            intro h
            apply hstay
            omega
          have hright_birth_short : x ≠ y + 1 := by
            intro h
            apply hdeath
            omega
          have hright_stay_short : x ≠ y := by
            intro h
            apply hstay
            omega
          rw [manyServerUniformizedKernel_apply_succ,
            manyServerUniformizedKernel_apply_succ]
          simp [hforward_death, hreverse_death,
            hleft_birth_short, hleft_stay_short,
            hright_birth_short, hright_stay_short]

/-- The normalized factorial/geometric PMF is invariant for the potential-event
many-server chain. -/
theorem manyServerStationaryPMF_uniformized_stationary
    (trafficIntensity : ℝ≥0) (servers : ℕ) (hservers : 0 < servers)
    (htraffic_lt_one : trafficIntensity < 1) :
    PMFStationary
      (manyServerUniformizedKernel trafficIntensity servers hservers)
      (manyServerStationaryPMF (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)) :=
  (manyServerStationaryPMF_uniformized_detailedBalance
    trafficIntensity servers hservers htraffic_lt_one).stationary

end AppliedModelingLib.Probability.Queueing
