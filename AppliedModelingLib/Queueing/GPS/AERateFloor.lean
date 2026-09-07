import AppliedModelingLib.Queueing.GPS.Core

/-!
# A.e. rate-floor GPS-to-FCFS comparison

This variant of the deterministic GPS comparison does not encode endpointwise
GPS allocation identities.  Instead, it assumes only that the guaranteed
class-rate floor holds almost everywhere on each physical job-service
interval.  Together with interval integrability and the work/service identity,
this is enough to derive the existing constant-rate FCFS recurrence.

It is intended for cadlag or absolutely-continuous service paths, where rate
values on a finite set of endpoints should not matter.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

/--
Pathwise data for a fluid GPS class with an almost-everywhere guaranteed-rate
floor on each actual job-service interval.  The comparison queue may have an
initial busy time that dominates the physical pre-tag workload, exactly as in
`CoupledIntegratedIdealFluidGPSPath`.
-/
structure CoupledAERateFloorGPSPath
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
  instantaneousClassRate : ℝ → ℝ
  service : ℝ → ℝ
  rate_intervalIntegrable : ∀ n,
    IntervalIntegrable instantaneousClassRate MeasureTheory.volume
      (actualServiceStart n) (departure n)
  ae_guaranteed_rate_floor_on_actual_job : ∀ n,
    ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Icc (actualServiceStart n) (departure n))),
      capacity * weight ≤ instantaneousClassRate t
  service_increment_eq_integral : ∀ n,
    service (departure n) - service (actualServiceStart n) =
      ∫ t in actualServiceStart n..departure n, instantaneousClassRate t
  completed_work_eq_service : ∀ n,
    service (departure n) - service (actualServiceStart n) = work n

namespace CoupledAERateFloorGPSPath

variable {initialBusyUntil capacity weight : ℝ} {arrival work departure : ℕ → ℝ}

/-- The a.e. rate floor integrates to the guaranteed work floor on each job interval. -/
theorem integrated_rate_floor
    (H : CoupledAERateFloorGPSPath
      initialBusyUntil arrival work departure capacity weight) (n : ℕ) :
    capacity * weight * (departure n - H.actualServiceStart n) ≤
      H.service (departure n) - H.service (H.actualServiceStart n) := by
  rw [H.service_increment_eq_integral n]
  exact intervalIntegral_ge_const_of_ae_le
    (H.departure_after_actualServiceStart n)
    (H.rate_intervalIntegrable n)
    (H.ae_guaranteed_rate_floor_on_actual_job n)

/-- Each job completes within its a.e.-floor constant-rate service window. -/
theorem departure_le_actualStart_add_work_div
    (H : CoupledAERateFloorGPSPath
      initialBusyUntil arrival work departure capacity weight) (n : ℕ) :
    departure n ≤ H.actualServiceStart n + work n / (capacity * weight) := by
  have hservice := H.integrated_rate_floor n
  rw [H.completed_work_eq_service n] at hservice
  have hduration : departure n - H.actualServiceStart n ≤
      work n / (capacity * weight) := by
    apply (le_div_iff₀ H.guaranteed_rate_pos).2
    nlinarith [hservice]
  linarith

/--
The a.e.-rate-floor path supplies the existing FCFS constant-rate service
floor recurrence, so it can be used directly in the GPS response-tail layer.
-/
theorem toFCFSServiceFloorUpperBoundFromInitial
    (H : CoupledAERateFloorGPSPath
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

end CoupledAERateFloorGPSPath

end

end AppliedModelingLib.Probability.Queueing
