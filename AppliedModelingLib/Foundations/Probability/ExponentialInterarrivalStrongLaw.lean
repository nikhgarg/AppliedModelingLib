import AppliedModelingLib.Foundations.Probability.ExponentialInterarrivalNonexplosion
import Mathlib.Tactic

/-!
# Strong-law rate for canonical exponential renewal epochs

This module records the sample-path law of large numbers for the concrete
canonical exponential-interarrival construction. It is an input-process fact:
it neither constructs a queue nor infers stability from an arrival rate.
-/

namespace AppliedModelingLib.Probability.PoissonProcess

open MeasureTheory Filter
open scoped Topology ProbabilityTheory Function

noncomputable section

/--
At positive exponential rate, canonical arrival epochs have their expected
asymptotic duration per arrival. The normalization uses `n + 1` because
`arrivalTime n` contains precisely the first `n + 1` interarrival gaps.
-/
theorem ae_tendsto_arrivalTime_div_nat_succ
    {rate : Real} (hrate : 0 < rate) :
    ∀ᵐ omega ∂exponentialInterarrivalMeasure rate,
      Tendsto
        (fun n : Nat => arrivalTime n omega / ((n + 1 : Nat) : Real))
        atTop (nhds (1 / rate)) := by
  have hindep : Pairwise ((· ⟂ᵢ[exponentialInterarrivalMeasure rate] ·) on interarrival) := by
    intro i j hij
    exact (iIndepFun_interarrival hrate).indepFun hij
  have hident : ∀ i, ProbabilityTheory.IdentDistrib (interarrival i) (interarrival 0)
      (exponentialInterarrivalMeasure rate) (exponentialInterarrivalMeasure rate) :=
    fun i => (interarrival_hasLaw hrate i).identDistrib (interarrival_hasLaw hrate 0)
  have hmean : (exponentialInterarrivalMeasure rate)[interarrival 0] = 1 / rate :=
    integral_interarrival_zero_eq_inv_rate hrate
  filter_upwards [ProbabilityTheory.strong_law_ae_real interarrival
    (integrable_interarrival_zero hrate) hindep hident] with omega homega
  have hshift := homega.comp (tendsto_add_atTop_nat 1)
  simpa [arrivalTime, Function.comp_def, hmean] using hshift

end

end AppliedModelingLib.Probability.PoissonProcess
