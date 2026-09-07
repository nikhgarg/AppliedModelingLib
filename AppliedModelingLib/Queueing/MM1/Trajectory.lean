import AppliedModelingLib.Foundations.Probability.Processes.Markov.StationaryTrajectory
import AppliedModelingLib.Queueing.MM1.Kernel

/-!
# Stationary embedded M/M/1 trajectories

This module specializes the foundational invariant-kernel trajectory
construction to the uniformized stable M/M/1 chain.
-/

open scoped ENNReal NNReal

open MeasureTheory ProbabilityTheory

namespace AppliedModelingLib.Probability.Queueing

theorem geoNNPMF_uniformized_stationaryTraj_marginal
    (rho : ℝ≥0) (hrho : rho < 1) (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF rho hrho).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (uniformizedBirthProbability rho)
          (uniformizedBirthProbability_le_one rho)))).map
        (fun x => x n) =
      (geoNNPMF rho hrho).toMeasure := by
  exact stationaryTrajMeasure_marginal
    (geoNNPMF_uniformized_kernelInvariant rho hrho) n

/-- The rate-specialized uniformized M/M/1 embedded trajectory retains its
geometric traffic-intensity marginal at every discrete jump index. -/
theorem mm1_uniformized_stationaryTraj_marginal
    (arrivalRate serviceRate : ℝ≥0) (hstable : arrivalRate < serviceRate)
    (n : ℕ) :
    (stationaryTrajMeasure
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure
      (countablePMFKernel
        (reflectedBirthDeathKernel
          (arrivalRate / (arrivalRate + serviceRate))
          (rate_fraction_le_one arrivalRate serviceRate)))).map
        (fun x => x n) =
      (geoNNPMF (mm1TrafficIntensityNN arrivalRate serviceRate)
        (mm1TrafficIntensityNN_lt_one hstable)).toMeasure := by
  exact stationaryTrajMeasure_marginal
    (mm1_uniformized_geometric_stationary arrivalRate serviceRate hstable).kernelInvariant n

end AppliedModelingLib.Probability.Queueing
