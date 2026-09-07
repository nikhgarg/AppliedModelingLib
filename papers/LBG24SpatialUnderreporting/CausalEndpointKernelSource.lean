import LBG24SpatialUnderreporting.CollapsedCausalObservationLaw
import AppliedModelingLib.Foundations.Probability.KernelCompProdDensity

/-!
# Atomic causal endpoint kernels for LBG Appendix Theorem 2

The empirical endpoints in Eqs. (33)--(34) include deterministic caps such as
`S + 100 days`.  They therefore need not have Lebesgue densities.  This file
starts the corrected-model construction with an arbitrary rate-free endpoint
kernel: the Poisson gap block still has its exact density relative to the
joint base measure, including when the endpoint kernel has atoms.
-/

namespace LBG24SpatialUnderreporting

open MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability.PoissonProcess
open scoped ENNReal NNReal ProbabilityTheory

noncomputable section

/-- The finite iid Poisson gap block retains its rate density after adjoining
an arbitrary rate-free endpoint response kernel.  Unlike the older endpoint
density source, `endpointKernel` may be atomic. -/
theorem iidGapLaw_compProd_endpointKernel_eq_withDensity_rateFactor
    {count : ℕ} {Endpoint : Type*} [MeasurableSpace Endpoint]
    (endpointKernel : Kernel (Fin count -> ℝ) Endpoint)
    [IsSFiniteKernel endpointKernel]
    {rate : ℝ} (rate_pos : 0 < rate) :
    CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ endpointKernel =
      ((volume : Measure (Fin count -> ℝ)) ⊗ₘ endpointKernel).withDensity
        (fun p => exponentialBlockDensity rate count p.1) := by
  unfold CollapsedFiniteStageEndpointModel.iidGapLaw
  rw [pi_expMeasure_eq_withDensity_exponentialBlock rate_pos count]
  exact Measure.compProd_withDensity_left
    (measurable_exponentialBlockDensity rate count)

/-- A deterministic stopping cap is a rate-free endpoint response kernel.

This is the corrected-model representation needed for source choices such as
`E = S + 100 days`: conditional on the visible prefix, the endpoint can be a
point mass rather than a Lebesgue-density draw. -/
noncomputable def deterministicEndpointKernel
    {Prefix : Type*} [MeasurableSpace Prefix]
    (cap : Prefix -> ℝ) (hcap : Measurable cap) : Kernel Prefix ℝ :=
  Kernel.deterministic cap hcap

theorem deterministicEndpointKernel_apply
    {Prefix : Type*} [MeasurableSpace Prefix]
    (cap : Prefix -> ℝ) (hcap : Measurable cap) (history : Prefix) :
    deterministicEndpointKernel cap hcap history = Measure.dirac (cap history) :=
  Kernel.deterministic_apply hcap history

theorem deterministicEndpointKernel_isMarkov
    {Prefix : Type*} [MeasurableSpace Prefix]
    (cap : Prefix -> ℝ) (hcap : Measurable cap) :
    IsMarkovKernel (deterministicEndpointKernel cap hcap) := by
  unfold deterministicEndpointKernel
  infer_instance

/-- The exact Poisson gap density remains valid after adjoining a deterministic
endpoint cap.  The reference measure retains the cap's Dirac mass, so no
spurious Lebesgue density for the endpoint is introduced. -/
theorem iidGapLaw_compProd_deterministicEndpoint_eq_withDensity_rateFactor
    {count : ℕ}
    (cap : (Fin count -> ℝ) -> ℝ) (hcap : Measurable cap)
    {rate : ℝ} (rate_pos : 0 < rate) :
    CollapsedFiniteStageEndpointModel.iidGapLaw count rate ⊗ₘ
        deterministicEndpointKernel cap hcap =
      ((volume : Measure (Fin count -> ℝ)) ⊗ₘ
        deterministicEndpointKernel cap hcap).withDensity
          (fun p => exponentialBlockDensity rate count p.1) := by
  letI : IsMarkovKernel (deterministicEndpointKernel cap hcap) :=
    deterministicEndpointKernel_isMarkov cap hcap
  exact iidGapLaw_compProd_endpointKernel_eq_withDensity_rateFactor
    (deterministicEndpointKernel cap hcap) rate_pos

/-- At a single causal endpoint race, projecting onto an endpoint that beats
the next report gives its original response law weighted by the Poisson
no-arrival tail.  No endpoint density is required. -/
theorem endpointClock_terminalLaw_eq_withDensity_noArrivalTail
    (endpointLaw : Measure ℝ) [SFinite endpointLaw]
    {rate : ℝ} (rate_pos : 0 < rate) :
    Measure.map Prod.snd
        (((expMeasure rate).prod endpointLaw).restrict endpointWinsEvent) =
      endpointLaw.withDensity (fun endpoint =>
        expMeasure rate (Set.Ioi endpoint)) := by
  letI : IsProbabilityMeasure (expMeasure rate) :=
    isProbabilityMeasure_expMeasure rate_pos
  exact map_snd_restrict_endpointWins_eq_withDensity _ _

/-- The preceding terminal-race law specializes to a deterministic cap.  The
reference endpoint measure is the exact Dirac mass at that cap, retaining the
source model's atomic endpoint rather than replacing it with a density. -/
theorem deterministicEndpointClock_terminalLaw_eq_withDensity_noArrivalTail
    {Prefix : Type*} [MeasurableSpace Prefix]
    (cap : Prefix -> ℝ) (hcap : Measurable cap) (history : Prefix)
    {rate : ℝ} (rate_pos : 0 < rate) :
    Measure.map Prod.snd
        (((expMeasure rate).prod
          (deterministicEndpointKernel cap hcap history)).restrict
            endpointWinsEvent) =
      (Measure.dirac (cap history)).withDensity (fun endpoint =>
        expMeasure rate (Set.Ioi endpoint)) := by
  rw [deterministicEndpointKernel_apply]
  exact endpointClock_terminalLaw_eq_withDensity_noArrivalTail
    (Measure.dirac (cap history)) rate_pos

end

end LBG24SpatialUnderreporting
