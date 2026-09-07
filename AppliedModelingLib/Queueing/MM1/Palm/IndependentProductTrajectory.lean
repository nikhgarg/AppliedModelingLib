import AppliedModelingLib.Foundations.Probability.PalmProductTaggedArrival
import AppliedModelingLib.Queueing.MM1.Trajectory

/-!
# Independent tagged products for the uniformized M/M/1 trajectory

This module is the M/M/1 specialization of the foundational independent
tagged-arrival product construction.  It does not identify the independent
gap path with the clock driving the embedded chain.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory ProbabilityTheory

/-- Concrete stable-uniformized-M/M/1 state marginal on the independent tagged product space.
The statement deliberately does not claim that its gap path drives the embedded chain. -/
theorem geoNNPMF_uniformized_independentProductTagged_coordinate_hasLaw
    (rho : NNReal) (hrho : rho < 1) (n : ℕ) (rate : ℝ) (hrate : 0 < rate) :
    HasLaw (fun x : (ℕ → ℕ) × (ℤ → ℝ) => x.1 n)
      (Queueing.geoNNPMF rho hrho).toMeasure
      (independentProductTaggedArrivalAtZero
        (Queueing.stationaryTrajMeasure
          (Queueing.geoNNPMF rho hrho).toMeasure
          (Queueing.countablePMFKernel
            (Queueing.reflectedBirthDeathKernel
              (Queueing.uniformizedBirthProbability rho)
              (Queueing.uniformizedBirthProbability_le_one rho))))
        rate hrate).Ptag := by
  exact independentProductTaggedArrivalAtZero_stationaryTrajectory_coordinate_hasLaw
    (Queueing.geoNNPMF_uniformized_kernelInvariant rho hrho) n rate hrate

end AppliedModelingLib.Probability.PoissonProcess
