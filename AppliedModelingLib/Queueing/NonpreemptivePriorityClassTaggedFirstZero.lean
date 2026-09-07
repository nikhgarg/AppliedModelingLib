import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedServiceStartPredictability
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceWorkInvariance

/-!
# First-zero characterization for a tagged priority customer's service start

Before a tagged customer starts service, its pre-service ledger is strictly
positive.  Combined with the finite ledger identity, this gives the strict
first-zero side of the service-start characterization used by marked-input
factorizations.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The deterministic service-start ledger at a strict future horizon: work
already present before the tag, plus later strictly more urgent work, minus
elapsed service capacity. -/
noncomputable def stationaryPriorityClassTaggedPreServiceLedgerExpression
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : ℝ :=
  (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
    stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService i z) - t +
    nonpreemptivePriorityTaggedStrictArrivalWork
      (stationaryPriorityClassTaggedJob meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t)

/-- The pathwise data used to characterize a selected customer's queue wait
as the first zero of its pre-service ledger. -/
def stationaryPriorityClassTaggedFirstZeroData
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) : Prop :=
  Probability.PoissonProcess.suspensionGoodGapPath z.1.1 ∧
  (∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
    liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) ∧
  0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z ∧
  stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i z
      (stationaryPriorityClassTaggedQueueWait meanService i z) = 0 ∧
  ∀ t : ℝ, 0 ≤ t → t < stationaryPriorityClassTaggedQueueWait meanService i z →
    0 < stationaryPriorityClassTaggedPreServiceLedgerExpression meanService i z t

/-- Two nonnegative times coincide when a common real-valued ledger vanishes
at each time and is strictly positive at every earlier nonnegative time. -/
theorem eq_of_first_zero_of_pos_before
    (ledger : ℝ → ℝ) (left right : ℝ)
    (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleftZero : ledger left = 0) (hrightZero : ledger right = 0)
    (hleftPos : ∀ t : ℝ, 0 ≤ t → t < left → 0 < ledger t)
    (hrightPos : ∀ t : ℝ, 0 ≤ t → t < right → 0 < ledger t) :
    left = right := by
  rcases lt_trichotomy left right with hlt | heq | hgt
  · have hpositive : 0 < ledger left := hrightPos left hleft hlt
    rw [hleftZero] at hpositive
    linarith
  · exact heq
  · have hpositive : 0 < ledger right := hleftPos right hright hgt
    rw [hrightZero] at hpositive
    linarith

/-- Positive work marks are preserved by the strict finite replay that omits
arrivals exactly at its queried horizon. -/
theorem positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k) :
    positiveNonpreemptivePriorityResidualWork
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  apply positiveNonpreemptivePriorityResidualWork_advance
  apply positiveNonpreemptivePriorityResidualWork_run
  · exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
      meanService i z hpositive
  · intro job hjob
    unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon at hjob
    rcases List.mem_map.mp hjob with ⟨q, _, rfl⟩
    exact hpositive q.1 q.2

/-- Under the stable selected-Palm law, every strictly pre-service horizon has
a strictly positive service-start ledger.  The displayed expression uses only
work present before the selected arrival and strictly higher-priority work
that arrived before the queried horizon. -/
theorem ae_forall_stationaryPriorityClassTagged_preServiceLedgerExpression_pos_before_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ t : ℝ, 0 ≤ t → t < stationaryPriorityClassTaggedQueueWait meanService i z →
        0 <
          (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
            stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
              meanService i z) - t +
            nonpreemptivePriorityTaggedStrictArrivalWork
              (stationaryPriorityClassTaggedJob meanService i z)
              (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
                meanService i z t) := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_forall_nonpreemptivePriorityTaggedPreServiceWork_before_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hcutoff hpositive hwaiting hledger
  intro t ht hlt
  let state := stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z t
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have htagWaiting : tag ∈ state.waiting i := by
    apply (stationaryPriorityClassTaggedJob_mem_waiting_iff_waitingIdentifier_beforeHorizon
      meanService i z t hgood hcutoff).mpr
    exact (hwaiting t ht).mpr hlt
  have hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity state tag = 1 by
      simpa [state, tag] using
        nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t hgood]
  have hnotActive : ¬ ∃ residual, state.active = some (tag, residual) :=
    (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
      state tag i htagWaiting hmultiplicity).1
  have hledgerPos : 0 < nonpreemptivePriorityTaggedPreServiceWork state tag := by
    apply nonpreemptivePriorityTaggedPreServiceWork_pos_of_mem_waiting
    · exact positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t hpositive
    · exact nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t
    · exact hnotActive
    · simpa [state, tag] using htagWaiting
  simpa [state, tag] using (hledger t ht hlt).symm ▸ hledgerPos

/-- At the selected customer's service-start epoch, the pre-service ledger
expression vanishes.  Together with strict positivity at earlier horizons,
this identifies the queue wait as the first zero of an input-only ledger. -/
theorem ae_stationaryPriorityClassTagged_preServiceLedgerExpression_eq_zero_at_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
          meanService i z) - stationaryPriorityClassTaggedQueueWait meanService i z +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z (stationaryPriorityClassTaggedQueueWait meanService i z)) = 0 := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_exists_stationaryPriorityClassTaggedNetPastCutoff
      arrivalRate meanService harrivalRate hstable i,
    ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hpositive hcutoff hwait hcompletion
  rcases hcompletion with ⟨_, completedAt, _, hresponseTime, hresponseTail⟩
  rcases Filter.eventually_atTop.1 hresponseTail with ⟨responseCutoff, hresponseTail⟩
  let wait := stationaryPriorityClassTaggedQueueWait meanService i z
  let u := max wait responseCutoff
  have hwait_le_u : wait ≤ u := le_max_left _ _
  have hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z u = some completedAt := by
    exact hresponseTail u (le_max_right _ _)
  have hstart : wait =
      completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simp [wait, stationaryPriorityClassTaggedQueueWait, hresponseTime]
  have hledger := stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork
    meanService i z wait u completedAt hgood hpositive hcutoff
      (by simpa [wait] using hwait) hwait_le_u hstart hresponse
  dsimp [wait] at hledger ⊢
  linarith

/-- The stable selected-Palm law satisfies the complete first-zero data
package almost surely. -/
theorem ae_stationaryPriorityClassTaggedFirstZeroData
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedFirstZeroData meanService i z := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_stationaryPriorityClassTagged_preServiceLedgerExpression_eq_zero_at_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_forall_stationaryPriorityClassTagged_preServiceLedgerExpression_pos_before_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hcoalescence hnonneg hzero hpos
  exact ⟨hgood, hcoalescence, hnonneg,
    by simpa [stationaryPriorityClassTaggedPreServiceLedgerExpression] using hzero,
    by
      intro t ht hlt
      simpa [stationaryPriorityClassTaggedPreServiceLedgerExpression] using hpos t ht hlt⟩

end

end AppliedModelingLib.Queueing
