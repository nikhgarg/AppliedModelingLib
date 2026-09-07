import AppliedModelingLib.Queueing.BirthDeathDiffusionScaling
import AppliedModelingLib.Queueing.ManyServerTrajectory
import Mathlib.Tactic

/-!
# Generator bridge for uniformized many-server queues

This module identifies the changed-state increment intensities of the
Poissonized potential-event construction with the rates of the corresponding
many-server birth--death family.  It connects the explicit kernel construction
to the generator drift and second-jump-moment expressions used by diffusion
approximations.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped ENNReal NNReal

/-- The changed-state increment intensity of the uniformized many-server
kernel gives the birth--death generator drift at every state.  Self-loops
have zero increment and therefore do not appear in the expression. -/
theorem manyServerUniformizedKernel_changedState_drift_intensity
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (coordinate : ℕ → ℝ) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1)).toReal *
        (coordinate (state + 1) - coordinate state) +
      manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state - 1)).toReal *
        (coordinate (state - 1) - coordinate state) =
      birthDeathScaledDrift
        (manyServerBirthDeathRates
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) serviceRate servers)
        coordinate state := by
  cases state with
  | zero =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp [birthDeathScaledDrift, manyServerBirthDeathRates]
  | succ state =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp only [Nat.succ_sub_one]
      rw [manyServerUniformizedKernel_death_intensity]
      rfl

/-- The changed-state squared-increment intensity of the uniformized
many-server kernel gives the birth--death generator second jump moment at
every state.  Self-loops have zero squared increment and therefore do not
appear in the expression. -/
theorem manyServerUniformizedKernel_changedState_variance_intensity
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (coordinate : ℕ → ℝ) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1)).toReal *
        (coordinate (state + 1) - coordinate state) ^ 2 +
      manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state - 1)).toReal *
        (coordinate (state - 1) - coordinate state) ^ 2 =
      birthDeathScaledVariance
        (manyServerBirthDeathRates
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) serviceRate servers)
        coordinate state := by
  cases state with
  | zero =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp [birthDeathScaledVariance, manyServerBirthDeathRates]
  | succ state =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp only [Nat.succ_sub_one]
      rw [manyServerUniformizedKernel_death_intensity]
      rfl

/-- The changed-state third absolute-increment intensity of the uniformized
many-server kernel gives the birth--death generator third absolute jump
moment at every state.  This is the canonical-process version of the
Lindeberg/Taylor-remainder quantity; self-loops again contribute zero. -/
theorem manyServerUniformizedKernel_changedState_thirdAbsoluteMoment_intensity
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers state : ℕ)
    (hservers : 0 < servers) (coordinate : ℕ → ℝ) :
    manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state + 1)).toReal *
        |coordinate (state + 1) - coordinate state| ^ 3 +
      manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers *
        (manyServerUniformizedKernel trafficIntensity servers hservers state (state - 1)).toReal *
        |coordinate (state - 1) - coordinate state| ^ 3 =
      birthDeathScaledThirdAbsoluteMoment
        (manyServerBirthDeathRates
          ((servers : ℝ) * (trafficIntensity : ℝ) * serviceRate) serviceRate servers)
        coordinate state := by
  cases state with
  | zero =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp [birthDeathScaledThirdAbsoluteMoment, manyServerBirthDeathRates]
  | succ state =>
      rw [manyServerUniformizedKernel_birth_intensity]
      simp only [Nat.succ_sub_one]
      rw [manyServerUniformizedKernel_death_intensity]
      rfl

end AppliedModelingLib.Probability.Queueing
