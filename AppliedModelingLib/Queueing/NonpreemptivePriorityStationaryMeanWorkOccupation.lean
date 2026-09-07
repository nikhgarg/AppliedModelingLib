import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryFiniteOccupation
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFuturePairPredictability
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedSelectedMarkInvariance
import AppliedModelingLib.Queueing.NonpreemptivePriorityWaitingOccupation
import AppliedModelingLib.Queueing.NonpreemptivePriorityMeanBalance
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryWaitingCampbellTransport

/-!
# Stationary occupation identities for priority mean-work equations

This module collects the stationary/Palm occupation identities which turn the
pathwise tagged-service ledger into the finite nonpreemptive-priority
mean-work balance.  The declarations are stated for the generic marked
priority queue rather than for a particular paper interface.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The active residual work seen at a selected class arrival has the standard
exponential residual-work numerator.  The proof combines the literal
stationary finite-window energy balance with the selected-Palm state law. -/
theorem integral_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_eq_finitePriorityResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hstable : ∑ i, arrivalRate i * meanService i < 1) (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
          (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      finitePriorityResidualWork arrivalRate meanService := by
  calc
    ∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂
        (Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
            (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
        ∫ omega, stationaryPriorityRemotePastActiveResidualWork meanService omega ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate :=
      integral_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_eq_stationary
        arrivalRate meanService harrivalRate hmeanService hstable i
    _ = ∑ j, arrivalRate j * meanService j ^ 2 :=
      integral_stationaryPriorityRemotePastActiveResidualWork_eq_squareWorkRate
        arrivalRate meanService harrivalRate hmeanService hstable
          (Nat.pos_of_ne_zero (fun hn => by subst n; exact Fin.elim0 i))
    _ = finitePriorityResidualWork arrivalRate meanService := rfl

/-- After evaluating the active residual occupation, the selected-Palm
mean-work equation has only the priority-filtered waiting occupation left to
identify. -/
theorem finitePriorityStrictSlack_mul_integral_stationaryPriorityClassTaggedQueueWait_eq_residual_add_waiting
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    finitePriorityStrictSlack meanService arrivalRate i *
      (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) =
      finitePriorityResidualWork arrivalRate meanService +
        ∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  rw [finitePriorityStrictSlack_mul_integral_stationaryPriorityClassTaggedQueueWait_eq_preArrivalTerms
    arrivalRate meanService harrivalRate hmeanService hstable i,
    integral_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_eq_finitePriorityResidualWork
      arrivalRate meanService harrivalRate hmeanService hstable i]

/-- The selected-Palm mean waiting times of the stable stationary marked
priority queue satisfy the finite nonpreemptive-priority mean-work balance.
The active-residual term is evaluated by the stationary energy identity; the
priority-filtered waiting term is evaluated by the Campbell transport of
customer waiting occupations. -/
theorem finiteNonpreemptivePriorityMeanWaitBalance_stationaryPriorityClassTaggedQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1) :
    finiteNonpreemptivePriorityMeanWaitBalance arrivalRate meanService
      (fun i => ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) := by
  intro i
  change finitePriorityStrictSlack meanService arrivalRate i *
      (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂
        stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
    finitePriorityResidualWork arrivalRate meanService +
      ∑ j, if j ≤ i then meanService j * arrivalRate j *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService j z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate j) else 0
  calc
    finitePriorityStrictSlack meanService arrivalRate i *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂
          stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
        finitePriorityResidualWork arrivalRate meanService +
          ∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z ∂
            stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i := by
              simpa only [stationaryPriorityClassTaggedPalmMeasure] using
                (finitePriorityStrictSlack_mul_integral_stationaryPriorityClassTaggedQueueWait_eq_residual_add_waiting
                  arrivalRate meanService harrivalRate hmeanService hstable i)
    _ = finitePriorityResidualWork arrivalRate meanService +
        (∫ omega, stationaryPriorityRemotePastAtLeastAsUrgentWaitingWork meanService i omega ∂
          Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure arrivalRate) := by
            congr 1
            simpa only [stationaryPriorityClassTaggedPalmMeasure] using
              (integral_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_eq_stationary
                arrivalRate meanService harrivalRate hmeanService hstable i)
    _ = finitePriorityResidualWork arrivalRate meanService +
        (∑ j ∈ Finset.univ.filter (fun k : Fin n => k ≤ i),
          arrivalRate j *
            (∫ z, stationaryPriorityClassTaggedWorkRequirement meanService j z *
              stationaryPriorityClassTaggedQueueWait meanService j z ∂
              stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate j)) := by
                congr 1
                symm
                exact
                  sum_arrivalRate_mul_integral_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait_eq_integral_remotePastAtLeastAsUrgentWaitingWork
                    arrivalRate meanService harrivalRate hmeanService hstable i
    _ = finitePriorityResidualWork arrivalRate meanService +
        (∑ j ∈ Finset.univ.filter (fun k : Fin n => k ≤ i),
          arrivalRate j *
            (meanService j *
              (∫ z, stationaryPriorityClassTaggedQueueWait meanService j z ∂
                stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate j))) := by
                congr 1
                apply Finset.sum_congr rfl
                intro j _
                congr 1
                simpa only [stationaryPriorityClassTaggedPalmMeasure] using
                  (integral_stationaryPriorityClassTaggedWorkRequirement_mul_queueWait
                    arrivalRate meanService harrivalRate hmeanService hstable j)
    _ = finitePriorityResidualWork arrivalRate meanService +
        (∑ j, if j ≤ i then
          meanService j * arrivalRate j *
            (∫ z, stationaryPriorityClassTaggedQueueWait meanService j z ∂
              stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate j) else 0) := by
                congr 1
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro j _
                by_cases hji : j ≤ i
                · simp [hji]
                  ring
                · simp [hji]

/-- Under strict total load, the selected-Palm expected queue wait in the
stationary marked priority queue is the standard closed-form finite-priority
queue-wait expression. -/
theorem integral_stationaryPriorityClassTaggedQueueWait_eq_finiteNonpreemptivePriorityQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂
      stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
      finiteNonpreemptivePriorityQueueWait arrivalRate meanService i := by
  have hloadNonnegative : ∀ k, 0 ≤ meanService k * arrivalRate k := by
    intro k
    exact (mul_pos (hmeanService k) (harrivalRate k)).le
  have htotal : ∑ k, meanService k * arrivalRate k < 1 := by
    calc
      ∑ k, meanService k * arrivalRate k = ∑ k, arrivalRate k * meanService k := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ < 1 := hstable
  have hstrict : ∀ k, finitePriorityStrictSlack meanService arrivalRate k ≠ 0 := by
    intro k
    exact ne_of_gt
      (finitePriorityStrictSlack_pos_of_totalLoad_lt_one
        meanService arrivalRate hloadNonnegative htotal k)
  have hinclusive : ∀ k, finitePriorityInclusiveSlack meanService arrivalRate k ≠ 0 := by
    intro k
    exact ne_of_gt
      (finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
        meanService arrivalRate hloadNonnegative htotal k)
  exact finiteNonpreemptivePriorityMeanWaitBalance_eq_queueWait
    arrivalRate meanService
    (fun k => ∫ z, stationaryPriorityClassTaggedQueueWait meanService k z ∂
      stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate k)
    hstrict hinclusive
    (finiteNonpreemptivePriorityMeanWaitBalance_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable) i

end

end AppliedModelingLib.Queueing
