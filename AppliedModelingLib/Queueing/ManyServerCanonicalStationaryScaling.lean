import AppliedModelingLib.Queueing.ManyServerCanonicalTrajectory
import AppliedModelingLib.Queueing.ManyServerScaledStationaryLaw

/-!
# Stationary scaled canonical many-server trajectories

This module transports the invariant marginal of the canonical-clock
uniformized many-server construction through the usual centered square-root
state coordinate. It provides deterministic-time marginal laws only; it does
not identify a continuous-time semigroup or assert process-level convergence.
-/

namespace AppliedModelingLib.Probability.Queueing

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-- At every deterministic time, the centered square-root state of the
stationary canonical-clock uniformized many-server queue has the centered
scaled invariant law. -/
theorem manyServerCenteredScaledCanonicalStationaryTrajectoryAt_hasLaw
    (trafficIntensity : ℝ≥0) (serviceRate : ℝ) (servers : ℕ)
    (hservers : 0 < servers) (hserviceRate : 0 < serviceRate)
    (htraffic_lt_one : trafficIntensity < 1) (time : ℝ≥0) :
    HasLaw
      (fun z : (ℕ → ℕ) × (ℕ → ℝ) =>
        affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))
          (stationaryTrajectoryAtForwardPoissonCount (α := ℕ)
            (manyServerCanonicalForwardPoissonClock
              trafficIntensity serviceRate servers hservers hserviceRate) time z))
      (manyServerCenteredScaledStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one))
      ((stationaryTrajMeasure
        (manyServerStationaryLaw (trafficIntensity : ℝ) servers
          (by positivity) (by exact_mod_cast htraffic_lt_one))
        (countablePMFKernel
          (manyServerUniformizedKernel trafficIntensity servers hservers))).prod
        (PoissonProcess.exponentialInterarrivalMeasure
          (manyServerUniformizationRate (trafficIntensity : ℝ) serviceRate servers))) := by
  let coordinate : ℕ → ℝ :=
    affineQueueCoordinate (servers : ℝ) (Real.sqrt (servers : ℝ))
  have hcoordinate : HasLaw coordinate
      ((manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)).map coordinate)
      (manyServerStationaryLaw (trafficIntensity : ℝ) servers
        (by positivity) (by exact_mod_cast htraffic_lt_one)) :=
    ⟨(measurable_of_countable coordinate).aemeasurable, rfl⟩
  simpa [coordinate, manyServerCenteredScaledStationaryLaw, Function.comp_def] using
    hcoordinate.comp
      (manyServerUniformizedCanonicalStationaryTrajectoryAt_hasLaw
        trafficIntensity serviceRate servers hservers hserviceRate htraffic_lt_one time)

end AppliedModelingLib.Probability.Queueing
