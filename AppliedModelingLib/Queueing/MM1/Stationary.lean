import AppliedModelingLib.Queueing.MM1.GeometricStationary
import Mathlib.Tactic

/-!
# M/M/1 birth--death generator balance

This module isolates the algebraic stationary-law seam.  It intentionally
uses generator balance rather than claiming a constructed continuous-time
Markov process.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

open ProbabilityTheory

/-- Birth and death rates for a queue-length process on `ℕ`. -/
structure BirthDeathRates where
  birth : ℕ → ℝ
  death : ℕ → ℝ
  death_zero : death 0 = 0

/-- The global generator-balance equations for a birth--death rate family. -/
def StationaryGeneratorBalance (G : BirthDeathRates) (mass : ℕ → ℝ) : Prop :=
  ∀ n : ℕ,
    mass n * (G.birth n + G.death n) =
      (if n = 0 then 0 else mass (n - 1) * G.birth (n - 1)) +
        mass (n + 1) * G.death (n + 1)

/-- A normalized nonnegative solution of the birth--death generator equations. -/
structure GeneratorStationaryLaw (G : BirthDeathRates) where
  mass : ℕ → ℝ
  nonneg : ∀ n, 0 ≤ mass n
  hasSum_one : HasSum mass 1
  generator_balance : StationaryGeneratorBalance G mass

/-- Detailed balance across each adjacent queue-length edge. -/
def DetailedBalance (G : BirthDeathRates) (mass : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, mass n * G.birth n = mass (n + 1) * G.death (n + 1)

/-- Detailed balance implies the birth--death global balance equations. -/
theorem DetailedBalance.stationaryGeneratorBalance
    {G : BirthDeathRates} {mass : ℕ → ℝ}
    (hbalance : DetailedBalance G mass) :
    StationaryGeneratorBalance G mass := by
  intro n
  cases n with
  | zero =>
      simpa [StationaryGeneratorBalance, G.death_zero] using hbalance 0
  | succ n =>
      have hleft := hbalance n
      have hright := hbalance (n + 1)
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      calc
        mass (n + 1) * (G.birth (n + 1) + G.death (n + 1)) =
            mass (n + 1) * G.birth (n + 1) +
              mass (n + 1) * G.death (n + 1) := by ring
        _ = mass (n + 2) * G.death (n + 2) + mass n * G.birth n := by
            rw [hright, ← hleft]
        _ = mass n * G.birth n + mass (n + 2) * G.death (n + 2) := by ring

/-- The reflected M/M/1 birth--death rate family. -/
def mm1BirthDeathRates (arrivalRate serviceRate : ℝ) : BirthDeathRates where
  birth := fun _ => arrivalRate
  death := fun n => if n = 0 then 0 else serviceRate
  death_zero := by simp

/-- Geometric candidate stationary mass at traffic intensity `rho`. -/
def mm1StationaryMass (rho : ℝ) (n : ℕ) : ℝ := rho ^ n * (1 - rho)

/-- The M/M/1 stationary mass is the real PMF of the matching geometric law. -/
theorem mm1StationaryMass_eq_geometricPMFReal (rho : ℝ) (n : ℕ) :
    mm1StationaryMass rho n = geometricPMFReal (1 - rho) n := by
  simp only [mm1StationaryMass, geometricPMFReal]
  ring

theorem mm1StationaryMass_nonneg
    {rho : ℝ} (hrho_nonneg : 0 ≤ rho) (hrho_le_one : rho ≤ 1) (n : ℕ) :
    0 ≤ mm1StationaryMass rho n := by
  exact mul_nonneg (pow_nonneg hrho_nonneg n) (sub_nonneg.mpr hrho_le_one)

/-- The M/M/1 detailed-balance recurrence when `arrivalRate = rho * serviceRate`. -/
theorem mm1_detailedBalance
    (rho serviceRate : ℝ) :
    DetailedBalance (mm1BirthDeathRates (rho * serviceRate) serviceRate)
      (mm1StationaryMass rho) := by
  intro n
  simp only [mm1BirthDeathRates, mm1StationaryMass, Nat.succ_ne_zero, if_false]
  rw [pow_succ]
  ring

/-- The geometric M/M/1 mass satisfies all generator-balance equations. -/
theorem mm1_stationaryGeneratorBalance
    (rho serviceRate : ℝ) :
    StationaryGeneratorBalance (mm1BirthDeathRates (rho * serviceRate) serviceRate)
      (mm1StationaryMass rho) :=
  (mm1_detailedBalance rho serviceRate).stationaryGeneratorBalance

/-- Under `0 ≤ rho < 1`, the candidate M/M/1 stationary mass sums to one. -/
theorem hasSum_mm1StationaryMass
    (rho : ℝ) (hrho_nonneg : 0 ≤ rho) (hrho_lt_one : rho < 1) :
    HasSum (mm1StationaryMass rho) 1 := by
  convert geometricPMFRealSum (p := 1 - rho)
    (sub_pos.mpr hrho_lt_one) (sub_le_self 1 hrho_nonneg) using 1
  funext n
  simp only [mm1StationaryMass, geometricPMFReal]
  ring

/-- The traffic intensity inferred from stable positive M/M/1 rates. -/
noncomputable def mm1TrafficIntensity (arrivalRate serviceRate : ℝ) : ℝ :=
  arrivalRate / serviceRate

theorem mm1TrafficIntensity_nonneg
    {arrivalRate serviceRate : ℝ} (harrival_nonneg : 0 ≤ arrivalRate)
    (hservice_pos : 0 < serviceRate) :
    0 ≤ mm1TrafficIntensity arrivalRate serviceRate := by
  exact div_nonneg harrival_nonneg hservice_pos.le

theorem mm1TrafficIntensity_lt_one
    {arrivalRate serviceRate : ℝ} (hstable : arrivalRate < serviceRate)
    (hservice_pos : 0 < serviceRate) :
    mm1TrafficIntensity arrivalRate serviceRate < 1 := by
  exact (div_lt_one hservice_pos).mpr hstable

/-- Stable M/M/1 rates yield a normalized geometric solution of generator balance. -/
theorem mm1_geometricStationaryBalance_of_rates
    (arrivalRate serviceRate : ℝ) (hservice_pos : 0 < serviceRate) :
    StationaryGeneratorBalance (mm1BirthDeathRates arrivalRate serviceRate)
      (mm1StationaryMass (mm1TrafficIntensity arrivalRate serviceRate)) := by
  have hrate : mm1TrafficIntensity arrivalRate serviceRate * serviceRate = arrivalRate := by
    unfold mm1TrafficIntensity
    field_simp [ne_of_gt hservice_pos]
  simpa [hrate] using
    (mm1_stationaryGeneratorBalance
      (mm1TrafficIntensity arrivalRate serviceRate) serviceRate)

/--
Stable M/M/1 rates determine a normalized geometric solution of the explicit
birth--death generator balance equations.

This is a generator-level stationarity result.  Turning it into invariance of
a path-space continuous-time Markov chain still requires a nonexplosive CTMC
construction and a generator-to-semigroup theorem.
-/
noncomputable def mm1_geometricGeneratorStationaryLaw
    (arrivalRate serviceRate : ℝ) (harrival_nonneg : 0 ≤ arrivalRate)
    (hservice_pos : 0 < serviceRate) (hstable : arrivalRate < serviceRate) :
    GeneratorStationaryLaw (mm1BirthDeathRates arrivalRate serviceRate) where
  mass := mm1StationaryMass (mm1TrafficIntensity arrivalRate serviceRate)
  nonneg := fun n => mm1StationaryMass_nonneg
    (mm1TrafficIntensity_nonneg harrival_nonneg hservice_pos)
    (le_of_lt (mm1TrafficIntensity_lt_one hstable hservice_pos)) n
  hasSum_one := hasSum_mm1StationaryMass
    (mm1TrafficIntensity arrivalRate serviceRate)
    (mm1TrafficIntensity_nonneg harrival_nonneg hservice_pos)
    (mm1TrafficIntensity_lt_one hstable hservice_pos)
  generator_balance := mm1_geometricStationaryBalance_of_rates
    arrivalRate serviceRate hservice_pos

end Queueing
end Probability
end AppliedModelingLib
