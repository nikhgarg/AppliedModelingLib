import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedResponseIntegrability

/-!
# Layer-cake identity for a tagged nonpreemptive-priority queue wait

The finite mean queue wait of the stationary selected-Palm construction is
the integral of its strict waiting tail.  This is the analytic side of a
Palm/compensation argument; it is independent of how the tail event is
represented by finite queue replays.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

/-- Under strict total load, the selected-Palm mean queue wait is its strict
tail integral over positive physical time. -/
theorem integral_stationaryPriorityClassTaggedQueueWait_eq_integral_tail
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      ∫ t in Set.Ioi (0 : ℝ),
        ((Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag).real
          {z | t < stationaryPriorityClassTaggedQueueWait meanService i z} := by
  exact (integrable_stationaryPriorityClassTaggedQueueWait_of_totalStable
    arrivalRate meanService harrivalRate hmeanService hstable i).integral_eq_integral_meas_lt
      (ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)

end

end AppliedModelingLib.Queueing
