import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedCanonicalTrace

/-!
# Deterministic-time tails of a selected priority response

The literal selected-Palm response tail can be split into its post-arrival
workload and the finite-horizon future marked-input ledger.  This is a
pathwise consequence of the concrete replay work-conservation result.
-/

namespace AppliedModelingLib.Queueing

open Filter

noncomputable section

/-- If a literal selected response is still unfinished at a nonnegative time,
then either the post-admission workload exceeds its chosen share of that time
or the finite future marked work exceeds the complementary share. -/
theorem ae_stationaryPriorityClassTaggedResponseTime_lt_imp_arrivalWork_or_futureWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (t futureShare : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      t < stationaryPriorityClassTaggedResponseTime meanService i z →
        (1 - futureShare) * t ≤
          stationaryPriorityClassTaggedArrivalTotalWork meanService i z ∨
        futureShare * t ≤
          stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t := by
  filter_upwards [
    ae_stationaryPriorityClassTaggedResponseTime_lt_imp_negArrivalWork_le_netFuture
      arrivalRate meanService harrivalRate hmeanService hstable i t ht] with z hnet
  intro hresponse
  by_contra hsplit
  simp only [not_or] at hsplit
  have harrival : stationaryPriorityClassTaggedArrivalTotalWork meanService i z <
      (1 - futureShare) * t :=
    lt_of_not_ge hsplit.1
  have hfuture : stationaryPriorityTaggedTotalFutureWorkAggregate meanService i z t <
      futureShare * t :=
    lt_of_not_ge hsplit.2
  have hnet' := hnet hresponse
  unfold stationaryPriorityTaggedNetFutureInput at hnet'
  linarith

end

end AppliedModelingLib.Queueing
