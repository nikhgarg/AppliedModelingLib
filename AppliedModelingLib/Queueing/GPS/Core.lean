import AppliedModelingLib.Queueing.Core
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-!
# Deterministic fluid-GPS service-floor comparison

For one GPS class, this module turns the fluid allocation lower bound into the
FCFS constant-rate recurrence used by `Queueing.FCFSServiceFloorUpperBoundFromInitial`.
It is deterministic: the stationary/Palm and Poisson/M/M/1 arguments are
separate inputs at the tail-probability layer.
-/

namespace AppliedModelingLib
namespace Probability
namespace Queueing

noncomputable section

/-- Instantaneous normalized GPS allocation to one backlogged class. -/
def idealGPSClassRate (capacity weight activeWeightSum : ℝ) : ℝ :=
  capacity * weight / activeWeightSum

/-- A backlogged GPS class receives at least its unnormalized guaranteed share. -/
theorem idealGPSClassRate_ge_guaranteed
    {capacity weight activeWeightSum : ℝ}
    (hcapacity : 0 ≤ capacity) (hweight : 0 ≤ weight)
    (hsum_pos : 0 < activeWeightSum) (hsum_le_one : activeWeightSum ≤ 1) :
    capacity * weight ≤ idealGPSClassRate capacity weight activeWeightSum := by
  unfold idealGPSClassRate
  rw [le_div_iff₀ hsum_pos]
  nlinarith [mul_nonneg hcapacity hweight]

/-- Integrating a pointwise rate floor gives the corresponding work floor. -/
theorem intervalIntegral_ge_const_of_pointwise_le
    {rate start finish : ℝ} {instantaneousRate : ℝ → ℝ}
    (hstart_finish : start ≤ finish)
    (hintegrable : IntervalIntegrable instantaneousRate MeasureTheory.volume start finish)
    (hpointwise : ∀ t ∈ Set.Icc start finish, rate ≤ instantaneousRate t) :
    rate * (finish - start) ≤
      ∫ t in start..finish, instantaneousRate t := by
  have hconst : IntervalIntegrable (fun _ : ℝ => rate) MeasureTheory.volume start finish :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hstart_finish hconst hintegrable
    hpointwise
  rw [intervalIntegral.integral_const] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

/--
The same interval service-floor calculation from an almost-everywhere rate
lower bound.  This is the form a cadlag or absolutely-continuous GPS path can
normally establish without choosing endpoint values for its instantaneous
allocation.
-/
theorem intervalIntegral_ge_const_of_ae_le
    {rate start finish : ℝ} {instantaneousRate : ℝ → ℝ}
    (hstart_finish : start ≤ finish)
    (hintegrable : IntervalIntegrable instantaneousRate MeasureTheory.volume start finish)
    (hpointwise : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc start finish)),
      rate ≤ instantaneousRate t) :
    rate * (finish - start) ≤
      ∫ t in start..finish, instantaneousRate t := by
  have hconst : IntervalIntegrable (fun _ : ℝ => rate) MeasureTheory.volume start finish :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_ae_restrict hstart_finish hconst hintegrable
    hpointwise
  rw [intervalIntegral.integral_const] at hmono
  simpa [smul_eq_mul, mul_comm] using hmono

/--
Pathwise data for one ideal fluid GPS class coupled to a constant-rate FCFS
comparator.  `actualServiceStart` is the physical GPS service start, whereas
`initialBusyUntil` belongs to the comparison queue.  The inequalities linking
them permit the comparator's initial workload to dominate the actual pre-tag
workload; this is the needed stationary/Palm coupling direction.

The endpoint-inclusive rate convention is immaterial to the interval integral.
A full cadlag model may instead establish the same rate inequality almost
everywhere on the busy interval.
-/
structure CoupledIntegratedIdealFluidGPSPath
    (initialBusyUntil : ℝ) (arrival work departure : ℕ → ℝ)
    (capacity weight : ℝ) where
  capacity_nonneg : 0 ≤ capacity
  weight_nonneg : 0 ≤ weight
  guaranteed_rate_pos : 0 < capacity * weight
  actualServiceStart : ℕ → ℝ
  arrival_le_actualServiceStart : ∀ n, arrival n ≤ actualServiceStart n
  departure_after_actualServiceStart : ∀ n,
    actualServiceStart n ≤ departure n
  actualStart_zero_le_comparatorStart :
    actualServiceStart 0 ≤ max (arrival 0) initialBusyUntil
  actualStart_succ_le_comparatorStart : ∀ n,
    actualServiceStart (n + 1) ≤ max (arrival (n + 1)) (departure n)
  activeWeightSum : ℝ → ℝ
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable : ∀ n,
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      (actualServiceStart n) (departure n)
  service_increment_eq_integral : ∀ n,
    service (departure n) - service (actualServiceStart n) =
      ∫ t in actualServiceStart n..departure n, instantaneousClassRate t
  gps_allocation_on_actual_job : ∀ n t,
    t ∈ Set.Icc (actualServiceStart n) (departure n) →
      instantaneousClassRate t =
        idealGPSClassRate capacity weight (activeWeightSum t)
  activeWeightSum_pos_on_actual_job : ∀ n t,
    t ∈ Set.Icc (actualServiceStart n) (departure n) →
      0 < activeWeightSum t
  activeWeightSum_le_one_on_actual_job : ∀ n t,
    t ∈ Set.Icc (actualServiceStart n) (departure n) →
      activeWeightSum t ≤ 1
  completed_work_eq_service : ∀ n,
    service (departure n) - service (actualServiceStart n) = work n

namespace CoupledIntegratedIdealFluidGPSPath

variable {initialBusyUntil capacity weight : ℝ} {arrival work departure : ℕ → ℝ}

/-- GPS's integrated class-rate floor on each physical FCFS service interval. -/
theorem integrated_gps_floor
    (H : CoupledIntegratedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) (n : ℕ) :
    capacity * weight * (departure n - H.actualServiceStart n) ≤
      H.service (departure n) - H.service (H.actualServiceStart n) := by
  rw [H.service_increment_eq_integral n]
  apply intervalIntegral_ge_const_of_pointwise_le (H.departure_after_actualServiceStart n)
    (H.rate_intervalIntegrable n)
  intro t ht
  rw [H.gps_allocation_on_actual_job n t ht]
  exact idealGPSClassRate_ge_guaranteed H.capacity_nonneg H.weight_nonneg
    (H.activeWeightSum_pos_on_actual_job n t ht)
    (H.activeWeightSum_le_one_on_actual_job n t ht)

/-- Each job departs no later than a rate-`Cφ` service window after its actual start. -/
theorem departure_le_actualStart_add_work_div
    (H : CoupledIntegratedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) (n : ℕ) :
    departure n ≤ H.actualServiceStart n + work n / (capacity * weight) := by
  have hservice := H.integrated_gps_floor n
  rw [H.completed_work_eq_service n] at hservice
  have hduration : departure n - H.actualServiceStart n ≤
      work n / (capacity * weight) := by
    apply (le_div_iff₀ H.guaranteed_rate_pos).2
    nlinarith [hservice]
  linarith

/--
The fluid GPS path has the recurrence required by the existing FCFS comparison
theorem.  Consequently it can be supplied pointwise as the
`hServiceFloorRecurrence` input of the GPS response-tail theorem.
-/
theorem toFCFSServiceFloorUpperBoundFromInitial
    (H : CoupledIntegratedIdealFluidGPSPath
      initialBusyUntil arrival work departure capacity weight) :
    FCFSServiceFloorUpperBoundFromInitial initialBusyUntil arrival work departure
      (capacity * weight) := by
  refine ⟨?_, ?_⟩
  · calc
      departure 0 ≤ H.actualServiceStart 0 + work 0 / (capacity * weight) :=
        H.departure_le_actualStart_add_work_div 0
      _ ≤ max (arrival 0) initialBusyUntil + work 0 / (capacity * weight) := by
        linarith [H.actualStart_zero_le_comparatorStart]
  · intro n
    calc
      departure (n + 1) ≤ H.actualServiceStart (n + 1) +
          work (n + 1) / (capacity * weight) :=
        H.departure_le_actualStart_add_work_div (n + 1)
      _ ≤ max (arrival (n + 1)) (departure n) +
          work (n + 1) / (capacity * weight) := by
        linarith [H.actualStart_succ_le_comparatorStart n]

end CoupledIntegratedIdealFluidGPSPath

end
end Queueing
end Probability
end AppliedModelingLib
