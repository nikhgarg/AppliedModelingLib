import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFutureMarkPredictability
import AppliedModelingLib.Queueing.NonpreemptivePrioritySimultaneousArrivals
import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceInterval
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedStrictCompletionBound
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceLedger
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedMeanWorkTerms

/-!
# Prefix observability of a tagged priority service start

The tagged customer is waiting at a strict future horizon precisely when its
service has not begun before that horizon.  This module first gives that
finite-replay observation a Borel representative; later results will transfer
the representative through the isolated future-mark factor.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

open scoped MeasureTheory

/-- The causal selected/Palm queue state immediately before a finite future
horizon.  Unlike the usual right-closed replay, this execution omits all
arrivals exactly at its endpoint.  It is therefore the causal counterpart of
the strict finite replay used for predictable service-start observations. -/
noncomputable def stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n) :=
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t)
  advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals

/-- Coalescence of the live remote past transfers the strict finite replay to
the corresponding causal strict post-arrival execution. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_liveEquivalent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t =
      stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
    stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    stationaryPriorityClassTaggedArrivalState
  dsimp only
  rw [clearNonpreemptivePriorityCompletionLedger_eq_of_liveEquivalent _ _ hequivalent]

/-- Numeric indicator that the selected customer is still in a FIFO list at a
strict finite replay horizon.  A value of one means the tagged service has not
yet started before the horizon. -/
noncomputable def stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ) : ℝ :=
  nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t)

/-- The causal strict state has the same numeric tagged-waiting observation as
any live-equivalent finite replay. -/
theorem stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_liveEquivalent
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older t : ℝ)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z)) :
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z older t =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t) := by
  unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_liveEquivalent
    meanService i z older t hequivalent]

/-- The finite tagged-waiting observation inherits deterministic-clock prefix
locality from the replay state. -/
theorem stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_futureMark_prefix_of_bound
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ) (older t : ℝ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1)
    (hbound : ∀ r,
      stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (r + 1)) < t → r < N) :
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        older t =
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
        older t := by
  unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_futureMark_prefix_of_bound
    meanService i j x y N older t hxy hprefix hgood hbound]

/-- The deterministic-clock finite tagged-waiting observation, represented
from the external factor and exactly the isolated marks whose labels can
occur through that clock.  The external count uses a weak endpoint, so it is
also valid when the clock coincides with an arrival. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older t : ℝ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
  fun z =>
    let N := multiclassPalmFutureMarkExternalFutureCountThrough i j t z.1
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
        (multiclassPalmFutureMarkPrefixRepresentative i j N (z.1, fun r => z.2 r)))
      older t

/-- On a good selected suspension, the Borel deterministic-clock observation
equals the literal finite replay.  This is a genuine random-prefix locality
statement: the prefix length is determined by the external arrival path, not
by the isolated work marks. -/
theorem stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation_eq_of_good
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older t : ℝ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation
      meanService i j older t (x.1, x.2) =
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        older t := by
  let N := multiclassPalmFutureMarkExternalFutureCountThrough i j t x.1
  let y : MulticlassPalmFutureMarkFactorCarrier i j :=
    multiclassPalmFutureMarkPrefixRepresentative i j N (x.1, fun r => x.2 r)
  have hxy : x.1 = y.1 := by
    rfl
  have hprefix : ∀ r < N, x.2 r = y.2 r := by
    intro r hr
    change x.2 r = futureMarkPrefixZeroExtension N (fun s => x.2 s) r
    rw [futureMarkPrefixZeroExtension_eq_of_lt N (fun s => x.2 s) r hr]
  have hbound : ∀ r,
      stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (r + 1)) < t → r < N := by
    intro r hr
    exact lt_multiclassPalmFutureMarkExternalFutureCountThrough_of_arrival_lt
      i j x r t hr
  have hlocal :=
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_futureMark_prefix_of_bound
      meanService i j x y N older t hxy hprefix hgood hbound
  change stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
      older t = _
  exact hlocal.symm

/-- Under strict total load, strict finite tagged-waiting observations
eventually agree with the causal selected/Palm state as their past horizon is
sent to infinity.  This is the queue-state transfer needed before any
unbounded stopped-reward limit is taken. -/
theorem ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_coalescence
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (t : ℝ) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older t =
          nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
            (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
              meanService i z t) := by
  filter_upwards [ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
    arrivalRate meanService harrivalRate hmeanService hstable i] with z hz
  rcases hz with ⟨cutoff, hcutoff, hcoalescence⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro older holder
  exact stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_liveEquivalent
    meanService i z older t (hcoalescence older holder)

/-- The strictly-before-horizon future ledger never reintroduces the selected
Palm customer. -/
theorem stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedJob meanService i z ∉
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t := by
  intro htag
  apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
    meanService i z t hgood
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    meanService i z t hgood]
  exact List.mem_append_left _ htag

/-- At its Palm admission epoch, the selected record's active residual can
never exceed its declared work.  The remote-past state contains no prior tag,
so this is the fresh-admission instance of the generic residual invariant. -/
theorem nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityTaggedResidualLeService
      (stationaryPriorityClassTaggedJob meanService i z)
      (stationaryPriorityClassTaggedArrivalState meanService i z) := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremoteFresh : ¬ nonpreemptivePriorityWorkStateContainsJob remote tag := by
    simpa [remote, tag] using
      not_nonpreemptivePriorityWorkStateContainsJob_stationaryPriorityClassTaggedRemotePastState
        meanService i z hgood
  have hclearedFresh : ¬ nonpreemptivePriorityWorkStateContainsJob cleared tag := by
    intro hcontains
    apply hremoteFresh
    rcases hcontains with hactive | hwaiting | hcompleted
    · exact Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hactive)
    · exact Or.inr (Or.inl (by
        simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hwaiting))
    · simp [cleared, clearNonpreemptivePriorityCompletionLedger] at hcompleted
  change nonpreemptivePriorityTaggedResidualLeService tag
    (admitNonpreemptivePriorityJob cleared tag)
  exact nonpreemptivePriorityTaggedResidualLeService_admit_self_of_fresh
    cleared tag hclearedFresh

/-- The strict finite causal selected-Palm replay preserves the fact that a
live tagged residual is at most the selected customer's declared work. -/
theorem nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityTaggedResidualLeService
      (stationaryPriorityClassTaggedJob meanService i z)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hinitial : nonpreemptivePriorityTaggedResidualLeService tag initial := by
    simpa [initial, tag] using
      nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hfuture : ∀ newJob ∈ jobs, newJob ≠ tag := by
    intro newJob hmember htag
    subst newJob
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
      meanService i z t hgood (by simpa [jobs] using hmember)
  have hrun : nonpreemptivePriorityTaggedResidualLeService tag afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedResidualLeService_run_of_forall_ne
        initial jobs tag hinitial hfuture
  change nonpreemptivePriorityTaggedResidualLeService tag
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)
  exact nonpreemptivePriorityTaggedResidualLeService_advance
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag hrun

/-- The right-closed causal selected/Palm replay also preserves the fact that
an active selected residual cannot exceed the customer's declared service
work. -/
theorem nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityTaggedResidualLeService
      (stationaryPriorityClassTaggedJob meanService i z)
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hinitial : nonpreemptivePriorityTaggedResidualLeService tag initial := by
    simpa [initial, tag] using
      nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hfuture : ∀ newJob ∈ jobs, newJob ≠ tag := by
    intro newJob hmember htag
    subst newJob
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood (by simpa [jobs] using hmember)
  have hrun : nonpreemptivePriorityTaggedResidualLeService tag afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedResidualLeService_run_of_forall_ne
        initial jobs tag hinitial hfuture
  change nonpreemptivePriorityTaggedResidualLeService tag
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)
  exact nonpreemptivePriorityTaggedResidualLeService_advance
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag hrun

/-- A right-closed selected/Palm replay can be cut at an intermediate
nonnegative horizon and continued with the later arrival ledger. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalState_eq_advance_run_after
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hs : 0 ≤ s) (hsu : s ≤ u) :
    stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u))) u
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u)) := by
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u
  have hafterFrontTime : afterFront.currentTime ≤ s := by
    dsimp [afterFront, initial, front]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood]
      exact hs
    · intro job hjob
      exact arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z s hgood job hjob
  have htailTime : ∀ job ∈ tail, s ≤ job.arrivalTime := by
    intro job hjob
    exact (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
      meanService i z s u hgood job (by simpa [tail] using hjob)).le
  have hcut := advance_runNonpreemptivePriorityArrivalTrace_cut
    afterFront tail s u hafterFrontTime hsu htailTime
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
    meanService i z s u hgood hs hsu, runNonpreemptivePriorityArrivalTrace_append]
  simpa [initial, front, afterFront, tail] using hcut

/-- Every finite causal selected/Palm post-arrival state is work-conserving:
an idle server has no residual FIFO work. -/
theorem nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    nonpreemptivePriorityWorkConserving
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
  dsimp only
  apply nonpreemptivePriorityWorkConserving_advance
  apply nonpreemptivePriorityWorkConserving_run
  exact nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
    meanService i z

/-- Strictly before a later recorded selected completion minus the selected
service work, the selected job must still be in a FIFO list.  An active tag
would have a scheduled nonpreemptive completion no later than that displayed
time, contradicting the first recorded selected completion at the later
horizon. -/
theorem exists_waiting_stationaryPriorityClassTaggedFinitePostArrivalState_of_lt_response_sub_service
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hslt : s < completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    ∃ priority,
      stationaryPriorityClassTaggedJob meanService i z ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s).waiting priority := by
  let state := stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hworkRequirementPos :
      0 < stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hpositive i 0
  have htagWork : tag.serviceWork =
      stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [tag] using stationaryPriorityClassTaggedJob_serviceWork meanService i z
  have htagWorkPos : 0 < tag.serviceWork := by
    rwa [htagWork]
  have hsltCompletion : s < completedAt := by
    linarith
  rcases stationaryPriorityClassTaggedJob_live_in_finitePostArrivalState_of_lt_responseTime
    meanService i z s u completedAt hgood hpositive hs hsu hsltCompletion hresponse with
      hactive | hwaiting
  · rcases hactive with ⟨residual, hactive⟩
    have hresidualPos : 0 < residual := by
      exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hpositive).1 (tag, residual) (by simpa [state] using hactive)
    have hresidualLe : residual ≤ tag.serviceWork := by
      exact nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hgood residual (by simpa [state] using hactive)
    have hstateTime : state.currentTime = s := by
      simpa [state] using
        stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
          meanService i z s hs hgood
    let completionTime := state.currentTime + residual
    have hcompletionLt : completionTime < completedAt := by
      dsimp [completionTime]
      rw [hstateTime]
      linarith [htagWork]
    have hcompletedLeHorizon : completedAt ≤ u := by
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_horizon_of_eq_some
        meanService i z u completedAt hgood hpositive (hs.trans hsu) hresponse
    have hcompletionLeHorizon : completionTime ≤ u :=
      hcompletionLt.le.trans hcompletedLeHorizon
    have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state := by
      dsimp [completionTime]
      exact nonpreemptivePriorityTaggedServiceSchedule_of_active state tag residual
        (by simpa [state] using hactive) hresidualPos
    let initial := stationaryPriorityClassTaggedArrivalState meanService i z
    let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s
    let afterFront := runNonpreemptivePriorityArrivalTrace initial front
    let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u
    have hafterFrontTime : afterFront.currentTime ≤ s := by
      dsimp [afterFront, initial, front]
      apply runNonpreemptivePriorityArrivalTrace_currentTime_le
      · rw [stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood]
        exact hs
      · intro job hjob
        exact arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
          meanService i z s hgood job hjob
    have htailTime : ∀ job ∈ tail, s ≤ job.arrivalTime := by
      intro job hjob
      exact (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
        meanService i z s u hgood job (by simpa [tail] using hjob)).le
    have hcut := advance_runNonpreemptivePriorityArrivalTrace_cut
      afterFront tail s u hafterFrontTime hsu htailTime
    have hfinalState : stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u =
        advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace state tail)) u
          (runNonpreemptivePriorityArrivalTrace state tail) := by
      unfold stationaryPriorityClassTaggedFinitePostArrivalState
      dsimp only
      rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
        meanService i z s u hgood hs hsu, runNonpreemptivePriorityArrivalTrace_append]
      simpa [state, initial, front, afterFront, tail] using hcut
    have hscheduledRecorded : (tag, completionTime) ∈
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace state tail)) u
          (runNonpreemptivePriorityArrivalTrace state tail)).completed := by
      exact mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_taggedServiceSchedule
        u completionTime state tail tag hcompletionLeHorizon hschedule
    have hscheduledRecordedFinal : (tag, completionTime) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
      rw [hfinalState]
      exact hscheduledRecorded
    have hfirst : completedAt ≤ completionTime := by
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
        meanService i z u completedAt completionTime tag hpositive hresponse rfl
          (by simpa [tag] using hscheduledRecordedFinal)
    exact (not_lt_of_ge hfirst hcompletionLt).elim
  · exact hwaiting

/-- A selected job that is still waiting in a finite causal replay cannot
complete by the current horizon plus its own service work.  This is the
strict-delay half of the tagged service-start identification. -/
theorem lt_response_sub_service_of_mem_waiting_stationaryPriorityClassTaggedFinitePostArrivalState
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ) (priority : Fin n)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hwaiting : stationaryPriorityClassTaggedJob meanService i z ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s).waiting priority)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    s < completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
  let state := stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u
  have htagWork : tag.serviceWork =
      stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [tag] using stationaryPriorityClassTaggedJob_serviceWork meanService i z
  have hstateTime : state.currentTime = s := by
    simpa [state] using
      stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
        meanService i z s hs hgood
  have hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1 := by
    simpa [state, tag] using
      (nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hgood).le
  have hstatePositive : positiveNonpreemptivePriorityResidualWork state := by
    simpa [state] using
      positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hpositive
  have hstateWork : nonpreemptivePriorityWorkConserving state := by
    simpa [state] using
      nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s
  have htailPositive : ∀ job ∈ tail, 0 < job.serviceWork := by
    intro job hjob
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter_iff
      meanService i z s u job).mp (by simpa [tail] using hjob) with ⟨j, k, _, hjobEq⟩
    subst job
    exact hpositive j k
  have htailDistinct : ∀ job ∈ tail, job ≠ tag := by
    intro job hjob htag
    subst job
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z u hgood
    rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
      meanService i z s u hgood hs hsu]
    exact List.mem_append_right _ (by simpa [tail] using hjob)
  have hfinalState := stationaryPriorityClassTaggedFinitePostArrivalState_eq_advance_run_after
    meanService i z s u hgood hs hsu
  have hrecorded : (tag, completedAt) ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
    rcases exists_completed_of_nonpreemptivePriorityRecordedCompletionTime_eq_some
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u)
      (Sigma.mk i 0) completedAt (by
        simpa [stationaryPriorityClassTaggedFinitePostArrivalResponseTime] using hresponse) with
      ⟨job, hidentifier, hcompleted⟩
    have hjob : job = tag := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
        meanService i z u job hgood
      · exact Or.inr (Or.inr ⟨completedAt, hcompleted⟩)
      · exact hidentifier
    subst job
    exact hcompleted
  have hfinalRecorded : (tag, completedAt) ∈
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state tail)) u
        (runNonpreemptivePriorityArrivalTrace state tail)).completed := by
    rw [← hfinalState]
    exact hrecorded
  have hstrict := taggedCompletion_gt_currentTime_add_service_of_mem_waiting
    state tag priority tail u completedAt
    (by simpa [state, tag] using hwaiting) hmultiplicity hstatePositive hstateWork
    htailPositive htailDistinct hfinalRecorded
  rw [hstateTime, htagWork] at hstrict
  linarith

/-- In a finite causal selected/Palm replay, the selected identifier is in a
FIFO list exactly before the recorded selected completion time minus the
selected service work. -/
theorem nonpreemptivePriorityWaitingIdentifier_finitePostArrivalState_iff_lt_response_sub_service
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) ↔
      s < completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
  constructor
  · rintro ⟨priority, job, hwaiting, hidentifier⟩
    have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
        meanService i z s job hgood
      · exact Or.inr (Or.inl ⟨priority, hwaiting⟩)
      · exact hidentifier
    subst job
    exact lt_response_sub_service_of_mem_waiting_stationaryPriorityClassTaggedFinitePostArrivalState
      meanService i z s u completedAt priority hgood hpositive hs hsu hwaiting hresponse
  · intro hslt
    rcases exists_waiting_stationaryPriorityClassTaggedFinitePostArrivalState_of_lt_response_sub_service
      meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse with
      ⟨priority, hwaiting⟩
    refine ⟨priority, stationaryPriorityClassTaggedJob meanService i z, hwaiting, ?_⟩
    simp [stationaryPriorityClassTaggedJob]

/-- On the full-measure stable selected-Palm carrier, the finite causal FIFO
observation at every nonnegative time is exactly the indicator that the
literal queue wait has not yet elapsed. -/
theorem ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalState_iff_lt_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ s : ℝ, 0 ≤ s →
        (nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) ↔
          s < stationaryPriorityClassTaggedQueueWait meanService i z) := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hgood hpositive hcompletion
  rcases hcompletion with ⟨_, completedAt, _, hresponse, htail⟩
  rcases Filter.eventually_atTop.1 htail with ⟨bound, hbound⟩
  intro s hs
  let u := max s bound
  have hsu : s ≤ u := le_max_left _ _
  have hfiniteResponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z u = some completedAt := by
    exact hbound u (le_max_right _ _)
  have hfinite := nonpreemptivePriorityWaitingIdentifier_finitePostArrivalState_iff_lt_response_sub_service
    meanService i z s u completedAt hgood hpositive hs hsu hfiniteResponse
  simpa [stationaryPriorityClassTaggedQueueWait, hresponse] using hfinite

/-- The strict causal replay, like its right-closed counterpart, retains
exactly one literal copy of the selected job. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) = 1 := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t)
  have hfuture : ∀ newJob ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t,
      newJob ≠ stationaryPriorityClassTaggedJob meanService i z := by
    intro newJob hmember htag
    subst newJob
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
      meanService i z t hgood hmember
  have hrun : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals
      (stationaryPriorityClassTaggedJob meanService i z) =
        nonpreemptivePriorityWorkStateJobMultiplicity
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (stationaryPriorityClassTaggedJob meanService i z) := by
    exact nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
      (stationaryPriorityClassTaggedArrivalState meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t)
      (stationaryPriorityClassTaggedJob meanService i z) hfuture
  change nonpreemptivePriorityWorkStateJobMultiplicity
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)
    (stationaryPriorityClassTaggedJob meanService i z) = 1
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance, hrun]
  exact nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
    meanService i z hgood

/-- A strict causal post-arrival replay reaches its queried physical horizon
whenever that horizon is nonnegative. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_currentTime_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
      meanService i z t).currentTime = t := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  let afterArrivals := runNonpreemptivePriorityArrivalTrace
    (stationaryPriorityClassTaggedArrivalState meanService i z)
    (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t)
  apply advanceNonpreemptivePriorityWorkState_currentTime_eq_target
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood]
      exact ht
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t job hjob).le
  · exact le_rfl

/-- The strict causal selected/Palm replay is non-idling, just as the
right-closed finite replay is. -/
theorem nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    nonpreemptivePriorityWorkConserving
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t) := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  apply nonpreemptivePriorityWorkConserving_advance
  apply nonpreemptivePriorityWorkConserving_run
  exact nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
    meanService i z

/-- On a path where the remote past has coalesced to a finite canonical
window, every strict-horizon selected replay retains class-consistent FIFO
lists. -/
theorem hasClassConsistentWaiting_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff) :
    hasClassConsistentWaiting
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t) := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  have hremoteClass : hasClassConsistentWaiting remote := by
    rw [show remote = canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0 by
      simpa [remote] using
        stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
          meanService i z hcutoff]
    exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-hcutoff.choose) 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hremoteClass
  have hinitialClass : hasClassConsistentWaiting initial := by
    simpa [initial, stationaryPriorityClassTaggedArrivalState] using
      hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared
        (stationaryPriorityClassTaggedJob meanService i z) hclearedClass
  change hasClassConsistentWaiting
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace initial jobs)) t
      (runNonpreemptivePriorityArrivalTrace initial jobs))
  apply hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
  exact hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
    initial jobs hinitialClass

/-- At every nonnegative strict horizon at which the selected customer is
still waiting, its deterministic pre-service ledger equals the ledger at
admission minus elapsed physical time plus precisely the work of the
strictly higher-priority arrivals observed before that horizon. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hwaiting : stationaryPriorityClassTaggedJob meanService i z ∈
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t).waiting i) :
    nonpreemptivePriorityTaggedPreServiceWork
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t)
        (stationaryPriorityClassTaggedJob meanService i z) =
      nonpreemptivePriorityTaggedPreServiceWork
          (stationaryPriorityClassTaggedArrivalState meanService i z)
          (stationaryPriorityClassTaggedJob meanService i z) - t +
        nonpreemptivePriorityTaggedStrictArrivalWork
          (stationaryPriorityClassTaggedJob meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
            meanService i z t) := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremoteClass : hasClassConsistentWaiting remote := by
    rw [show remote = canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0 by
      simpa [remote] using
        stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
          meanService i z hcutoff]
    exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-hcutoff.choose) 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hremoteClass
  have hinitialClass : hasClassConsistentWaiting initial := by
    simpa [initial, stationaryPriorityClassTaggedArrivalState] using
      hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared tag hclearedClass
  have hinitialWork : nonpreemptivePriorityWorkConserving initial := by
    simpa [initial] using
      nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have hinitialMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity initial tag = 1 := by
    simpa [initial, tag] using
      nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hinitialTime : initial.currentTime = 0 := by
    simpa [initial] using
      stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hnew : ∀ job ∈ jobs, job ≠ tag := by
    intro job hmember htag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
      meanService i z t hgood (by simpa [jobs, tag] using hmember)
  have hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime := by
    intro job hmember
    rw [hinitialTime]
    exact (arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t hgood job (by
        rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
          meanService i z t hgood]
        exact List.mem_append_left _ (by simpa [jobs] using hmember))).le
  have hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
    have hfull := pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z t
    rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
      meanService i z t hgood] at hfull
    exact (List.pairwise_append.mp hfull).1
  have hclassRun : hasClassConsistentWaiting afterArrivals := by
    simpa [afterArrivals] using
      hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace initial jobs hinitialClass
  have hworkRun : nonpreemptivePriorityWorkConserving afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityWorkConserving_run initial jobs hinitialWork
  have hmultRun : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
        nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
      simpa [afterArrivals] using
        nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
          initial jobs tag hnew]
    rw [hinitialMultiplicity]
  have hclockRun : afterArrivals.currentTime ≤ t := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le initial jobs t
    · rw [hinitialTime]
      exact ht
    · intro job hmember
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t job (by simpa [jobs] using hmember)).le
  have hwaitingRun : tag ∈ afterArrivals.waiting i := by
    apply mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
      (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag i
    simpa [stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon,
      initial, jobs, afterArrivals, tag] using hwaiting
  have hadvance := nonpreemptivePriorityTaggedPreServiceWork_advance_eq_sub_of_waiting
    (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals tag
    hclockRun hclassRun hworkRun hmultRun le_rfl hwaiting
  have htrace := nonpreemptivePriorityTaggedPreServiceWork_run_eq_sub_add_of_waiting
    initial jobs tag hstart hsorted hinitialClass hinitialWork
      (by simpa [hinitialMultiplicity]) hnew hwaitingRun
  have hendTime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime 0 jobs := by
    have htime := runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
      initial jobs hstart hsorted
    simpa [afterArrivals, hinitialTime] using htime
  change nonpreemptivePriorityTaggedPreServiceWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals) tag =
    nonpreemptivePriorityTaggedPreServiceWork initial tag - t +
      nonpreemptivePriorityTaggedStrictArrivalWork tag jobs
  calc
    nonpreemptivePriorityTaggedPreServiceWork
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals) tag =
        nonpreemptivePriorityTaggedPreServiceWork afterArrivals tag -
          (t - afterArrivals.currentTime) := hadvance
    _ = (nonpreemptivePriorityTaggedPreServiceWork initial tag -
          nonpreemptivePriorityArrivalTraceEndTime 0 jobs +
            nonpreemptivePriorityTaggedStrictArrivalWork tag jobs) -
          (t - nonpreemptivePriorityArrivalTraceEndTime 0 jobs) := by
          rw [htrace, hendTime]
          simp only [hinitialTime, sub_zero]
    _ = nonpreemptivePriorityTaggedPreServiceWork initial tag - t +
          nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := by ring

/-- The strict-horizon selected-Palm ledger is therefore already expressed in
the three physical components of the priority waiting-time argument: the two
pre-arrival state terms, elapsed time, and strictly higher-priority future
arrivals. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_eq_preArrival
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hwaiting : stationaryPriorityClassTaggedJob meanService i z ∈
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t).waiting i) :
    nonpreemptivePriorityTaggedPreServiceWork
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t)
        (stationaryPriorityClassTaggedJob meanService i z) =
      (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
          meanService i z) - t +
        nonpreemptivePriorityTaggedStrictArrivalWork
          (stationaryPriorityClassTaggedJob meanService i z)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
            meanService i z t) := by
  calc
    nonpreemptivePriorityTaggedPreServiceWork
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t)
        (stationaryPriorityClassTaggedJob meanService i z) =
        nonpreemptivePriorityTaggedPreServiceWork
            (stationaryPriorityClassTaggedArrivalState meanService i z)
            (stationaryPriorityClassTaggedJob meanService i z) - t +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z t) :=
      nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t ht hgood hcutoff hwaiting
    _ = (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
            meanService i z) - t +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z t) := by
      rw [nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood hcutoff]

/-- The right-closed finite replay is obtained from the strict replay by
admitting exactly the arrivals at the queried endpoint. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalState_eq_run_beforeHorizon_atHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t =
      runNonpreemptivePriorityArrivalTrace
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t)
        (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
          meanService i z t) := by
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z t
  have hclock : (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ t := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [show initial.currentTime = 0 by
        exact stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero
          meanService i z hgood]
      exact ht
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z t job (by simpa [front] using hjob)).le
  have htail : ∀ job ∈ tail, job.arrivalTime = t := by
    intro job hjob
    exact arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
      meanService i z t hgood job (by simpa [tail] using hjob)
  have hsplit := canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    meanService i z t hgood
  unfold stationaryPriorityClassTaggedFinitePostArrivalState
    stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
  dsimp only
  rw [hsplit]
  simpa [initial, front, tail] using
    advance_runNonpreemptivePriorityArrivalTrace_append_of_all_arrivalTime_eq_target
      initial front tail t hclock htail

/-- In the strict causal finite replay, any literal record carrying the
selected identifier is the selected job itself. -/
theorem eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalStateBeforeHorizon_of_identifier_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n))
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t) job)
    (hidentifier : job.identifier = (Sigma.mk i 0 : NonpreemptivePriorityArrivalIndex n)) :
    job = stationaryPriorityClassTaggedJob meanService i z := by
  unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon at hcontains
  dsimp only at hcontains
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hafter : nonpreemptivePriorityWorkStateContainsJob afterArrivals job := by
    exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse _ t _ _
      (by simpa [afterArrivals] using hcontains)
  rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse initial jobs job hafter with
      hinitial | hjobs
  · exact eq_stationaryPriorityClassTaggedJob_of_contains_arrivalState_of_identifier_eq
      meanService i z job hgood (by simpa [initial] using hinitial) hidentifier
  · have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      have hfuture : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
          meanService i z t := by
        simpa [jobs] using hjobs
      unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon at hfuture
      rcases List.mem_map.mp hfuture with ⟨q, hq, rfl⟩
      change q = Sigma.mk i 0 at hidentifier
      subst q
      rfl
    apply False.elim
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
      meanService i z t hgood
    rwa [← htag]

/-- For a class-consistent strict replay, the selected identifier is waiting
exactly when the literal selected job occurs in its own priority-class FIFO
list. -/
theorem stationaryPriorityClassTaggedJob_mem_waiting_iff_waitingIdentifier_beforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff) :
    stationaryPriorityClassTaggedJob meanService i z ∈
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t).waiting i ↔
      nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t) := by
  constructor
  · intro hwaiting
    exact ⟨i, stationaryPriorityClassTaggedJob meanService i z, hwaiting, by
      simp [stationaryPriorityClassTaggedJob]⟩
  · rintro ⟨priority, job, hmember, hidentifier⟩
    have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalStateBeforeHorizon_of_identifier_eq
        meanService i z t job hgood
      · exact Or.inr (Or.inl ⟨priority, hmember⟩)
      · exact hidentifier
    subst job
    have hclass := hasClassConsistentWaiting_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
      meanService i z t hcutoff priority
        (stationaryPriorityClassTaggedJob meanService i z) hmember
    have hpriority : priority = i := by
      simpa [stationaryPriorityClassTaggedJob] using hclass.symm
    simpa [hpriority] using hmember

/-- Omitting endpoint arrivals does not change whether the selected Palm
customer is waiting.  Endpoint arrivals are new tagged-free records, and the
strict replay is already work-conserving at that physical time. -/
theorem nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1) :
    nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t) ↔
      nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t) := by
  let strictState := stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z t
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z t
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hstate : stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t =
      runNonpreemptivePriorityArrivalTrace strictState tail := by
    simpa [strictState, tail] using
      stationaryPriorityClassTaggedFinitePostArrivalState_eq_run_beforeHorizon_atHorizon
        meanService i z t ht hgood
  have hwork : nonpreemptivePriorityWorkConserving strictState := by
    simpa [strictState] using
      nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t
  have hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity strictState tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity strictState tag = 1 by
      simpa [strictState, tag] using
        nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
          meanService i z t hgood]
  have htimes : ∀ job ∈ tail, job.arrivalTime = strictState.currentTime := by
    intro job hjob
    rw [arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
      meanService i z t hgood job (by simpa [tail] using hjob),
      show strictState.currentTime = t by
        simpa [strictState] using
          stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_currentTime_eq
            meanService i z t ht hgood]
  have hnew : ∀ job ∈ tail, job ≠ tag := by
    intro job hjob htag
    subst job
    apply stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobs
      meanService i z t hgood
    rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
      meanService i z t hgood]
    exact List.mem_append_right _ (by simpa [tail, tag] using hjob)
  have hwaiting :=
    exists_mem_waiting_iff_exists_mem_waiting_runNonpreemptivePriorityArrivalTrace_of_arrivalTime_eq
      strictState tail tag hwork hmultiplicity htimes hnew
  constructor
  · rintro ⟨priority, job, hmember, hidentifier⟩
    have htag : job = tag := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalStateBeforeHorizon_of_identifier_eq
        meanService i z t job hgood
      · exact Or.inr (Or.inl ⟨priority, hmember⟩)
      · exact hidentifier
    subst job
    rcases hwaiting.mp ⟨priority, hmember⟩ with ⟨laterPriority, hlater⟩
    refine ⟨laterPriority, tag, ?_, ?_⟩
    · rw [hstate]
      exact hlater
    · simp [tag, stationaryPriorityClassTaggedJob]
  · rintro ⟨priority, job, hmember, hidentifier⟩
    have hmemberFull : job ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z t).waiting priority :=
      hmember
    have htag : job = tag := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
        meanService i z t job hgood
      · exact Or.inr (Or.inl ⟨priority, hmemberFull⟩)
      · exact hidentifier
    subst job
    have hmemberRun : tag ∈
        (runNonpreemptivePriorityArrivalTrace strictState tail).waiting priority := by
      rw [← hstate]
      exact hmemberFull
    rcases hwaiting.mpr ⟨priority, hmemberRun⟩ with ⟨earlierPriority, hearlier⟩
    refine ⟨earlierPriority, tag, hearlier, ?_⟩
    simp [tag, stationaryPriorityClassTaggedJob]

/-- At the selected customer's recorded completion time minus its declared
service work, the strict causal replay has just begun that customer's
nonpreemptive service.  Thus its active residual is the full declared work,
not a later residual. -/
theorem exists_active_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_of_response_sub_service
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hstart : s = completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    ∃ residual,
      residual = stationaryPriorityClassTaggedWorkRequirement meanService i z ∧
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual) := by
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let strictState := stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z s
  let fullState := stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s
  let boundary := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z s
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u
  have hworkPos : 0 < stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hpositive i 0
  have htagWork : tag.serviceWork =
      stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [tag] using stationaryPriorityClassTaggedJob_serviceWork meanService i z
  have hslt : s < completedAt := by linarith
  rcases stationaryPriorityClassTaggedJob_live_in_finitePostArrivalState_of_lt_responseTime
    meanService i z s u completedAt hgood hpositive hs hsu hslt hresponse with
      hactive | hwaiting
  · rcases hactive with ⟨residual, hactive⟩
    have hresidualPos : 0 < residual := by
      exact (positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hpositive).1 (tag, residual) (by simpa [fullState, tag] using hactive)
    have hresidualLe : residual ≤ tag.serviceWork := by
      exact nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedFinitePostArrivalState
        meanService i z s hgood residual (by simpa [fullState, tag] using hactive)
    have hstateTime : fullState.currentTime = s := by
      simpa [fullState] using
        stationaryPriorityClassTaggedFinitePostArrivalState_currentTime_eq_horizon
          meanService i z s hs hgood
    let scheduledAt := s + residual
    have hscheduledLeCompletion : scheduledAt ≤ completedAt := by
      dsimp [scheduledAt]
      rw [← htagWork] at hstart
      linarith
    have hcompletedLeHorizon : completedAt ≤ u := by
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_horizon_of_eq_some
        meanService i z u completedAt hgood hpositive (hs.trans hsu) hresponse
    have hscheduledLeHorizon : scheduledAt ≤ u :=
      hscheduledLeCompletion.trans hcompletedLeHorizon
    have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag scheduledAt fullState := by
      dsimp [scheduledAt]
      rw [← hstateTime]
      exact nonpreemptivePriorityTaggedServiceSchedule_of_active fullState tag residual
        (by simpa [fullState, tag] using hactive) hresidualPos
    have hfinal := stationaryPriorityClassTaggedFinitePostArrivalState_eq_advance_run_after
      meanService i z s u hgood hs hsu
    have hscheduledRecorded : (tag, scheduledAt) ∈
        (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
      rw [hfinal]
      exact mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_taggedServiceSchedule
        u scheduledAt fullState tail tag hscheduledLeHorizon hschedule
    have hcompletionLeScheduled : completedAt ≤ scheduledAt := by
      exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_of_eq_some
        meanService i z u completedAt scheduledAt tag hpositive hresponse rfl hscheduledRecorded
    have hresidualEq : residual = tag.serviceWork := by
      dsimp [scheduledAt] at hscheduledLeCompletion hcompletionLeScheduled
      linarith
    have hstrictContains : nonpreemptivePriorityWorkStateContainsJob strictState tag := by
      unfold strictState stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
      dsimp only
      apply nonpreemptivePriorityWorkStateContainsJob_advance
      apply nonpreemptivePriorityWorkStateContainsJob_run
      unfold stationaryPriorityClassTaggedArrivalState
      exact nonpreemptivePriorityWorkStateContainsJob_admit_self _ _
    have hfullState : fullState =
        runNonpreemptivePriorityArrivalTrace strictState boundary := by
      simpa [fullState, strictState, boundary] using
        stationaryPriorityClassTaggedFinitePostArrivalState_eq_run_beforeHorizon_atHorizon
          meanService i z s hs hgood
    have hstrictTime : strictState.currentTime = s := by
      simpa [strictState] using
        stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_currentTime_eq
          meanService i z s hs hgood
    have hboundaryTimes : ∀ job ∈ boundary, job.arrivalTime = strictState.currentTime := by
      intro job hjob
      rw [arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
        meanService i z s hgood job (by simpa [boundary] using hjob), hstrictTime]
    rcases hstrictContains with hstrictActive | hstrictWaiting | hstrictCompleted
    · rcases hstrictActive with ⟨strictResidual, hstrictActive⟩
      have hrunActive :
          (runNonpreemptivePriorityArrivalTrace strictState boundary).active =
            some (tag, strictResidual) := by
        exact active_eq_runNonpreemptivePriorityArrivalTrace_of_active_of_arrivalTime_eq
          strictState boundary tag strictResidual hstrictActive hboundaryTimes
      have hfullActive : fullState.active = some (tag, strictResidual) := by
        rw [hfullState]
        exact hrunActive
      have hstrictResidualEq : strictResidual = residual := by
        have hsome : some (tag, strictResidual) = some (tag, residual) :=
          hfullActive.symm.trans (by simpa [fullState, tag] using hactive)
        exact congrArg Prod.snd (Option.some.inj hsome)
      refine ⟨strictResidual, ?_, ?_⟩
      · rw [hstrictResidualEq, hresidualEq, htagWork]
      · simpa [strictState, tag] using hstrictActive
    · rcases hstrictWaiting with ⟨strictPriority, hstrictWaiting⟩
      have hstrictWaitingId : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
        strictState := ⟨strictPriority, tag, hstrictWaiting,
          by simp [tag, stationaryPriorityClassTaggedJob]⟩
      have hfullWaitingId : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
        fullState := by
        apply (nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff
          meanService i z s hs hgood).mp
        simpa [strictState] using hstrictWaitingId
      rcases hfullWaitingId with ⟨priority, job, hmember, hidentifier⟩
      have hjob : job = tag := by
        apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
          meanService i z s job hgood
        · exact Or.inr (Or.inl ⟨priority, by simpa [fullState] using hmember⟩)
        · simpa [tag] using hidentifier
      subst job
      have hmult : nonpreemptivePriorityWorkStateJobMultiplicity fullState tag ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity fullState tag = 1 by
          simpa [fullState, tag] using
            nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
              meanService i z s hgood]
      exact (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
        fullState tag priority (by simpa [fullState] using hmember) hmult).1
          ⟨residual, by simpa [fullState, tag] using hactive⟩ |>.elim
    · rcases hstrictCompleted with ⟨completedAt', hstrictCompleted⟩
      have hcompletedFull : (tag, completedAt') ∈ fullState.completed := by
        rw [hfullState]
        exact mem_completed_runNonpreemptivePriorityArrivalTrace
          strictState boundary tag completedAt' hstrictCompleted
      have hmult : nonpreemptivePriorityWorkStateJobMultiplicity fullState tag = 1 := by
        simpa [fullState, tag] using
          nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
            meanService i z s hgood
      have htooMany := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_completed
        fullState tag residual completedAt' (by simpa [fullState, tag] using hactive) hcompletedFull
      rw [hmult] at htooMany
      omega
  · rcases hwaiting with ⟨priority, hwaiting⟩
    have hwaitingId : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s) :=
        ⟨priority, tag, hwaiting, by simp [tag, stationaryPriorityClassTaggedJob]⟩
    have hlt := (nonpreemptivePriorityWaitingIdentifier_finitePostArrivalState_iff_lt_response_sub_service
      meanService i z s u completedAt hgood hpositive hs hsu hresponse).mp hwaitingId
    rw [hstart] at hlt
    exact (lt_irrefl _ hlt).elim

/-- When the selected customer has a strictly positive queue wait, the finite
strict replay at its service-start time realizes the exact tagged-work ledger.
This is a finite deterministic consequence of the recorded response time,
with no limiting argument at the endpoint. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork_of_pos
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hs : 0 < s) (hsu : s ≤ u)
    (hstart : s = completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    s =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z s) := by
  let remote := stationaryPriorityClassTaggedRemotePastState meanService i z
  let cleared := clearNonpreemptivePriorityCompletionLedger remote
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z s
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hremoteClass : hasClassConsistentWaiting remote := by
    rw [show remote = canonicalStationaryPriorityClassTaggedFiniteWindowState
        meanService i z (-hcutoff.choose) 0 by
      simpa [remote] using
        stationaryPriorityClassTaggedRemotePastState_eq_finiteWindowState_of_exists_cutoff
          meanService i z hcutoff]
    exact hasClassConsistentWaiting_canonicalStationaryPriorityClassTaggedFiniteWindowState
      meanService i z (-hcutoff.choose) 0
  have hclearedClass : hasClassConsistentWaiting cleared := by
    simpa [cleared, clearNonpreemptivePriorityCompletionLedger] using hremoteClass
  have hinitialClass : hasClassConsistentWaiting initial := by
    simpa [initial, stationaryPriorityClassTaggedArrivalState] using
      hasClassConsistentWaiting_admitNonpreemptivePriorityJob cleared tag hclearedClass
  have hinitialPositive : positiveNonpreemptivePriorityResidualWork initial := by
    simpa [initial] using
      positiveNonpreemptivePriorityResidualWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hpositive
  have hinitialWork : nonpreemptivePriorityWorkConserving initial := by
    simpa [initial] using
      nonpreemptivePriorityWorkConserving_stationaryPriorityClassTaggedArrivalState
        meanService i z
  have hinitialBound : nonpreemptivePriorityTaggedResidualLeService tag initial := by
    simpa [initial, tag] using
      nonpreemptivePriorityTaggedResidualLeService_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hinitialMultiplicity :
      nonpreemptivePriorityWorkStateJobMultiplicity initial tag = 1 := by
    simpa [initial, tag] using
      nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood
  have hinitialTime : initial.currentTime = 0 := by
    simpa [initial] using
      stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hpositiveJobs : ∀ job ∈ jobs, 0 < job.serviceWork := by
    intro job hmember
    have hfull : job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobs
        meanService i z s := by
      rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
        meanService i z s hgood]
      exact List.mem_append_left _ (by simpa [jobs] using hmember)
    rcases (mem_canonicalStationaryPriorityClassTaggedFutureArrivalJobs_iff
      meanService i z s job).mp hfull with ⟨j, k, _, hcoordinate⟩
    subst job
    exact hpositive j k
  have hnew : ∀ job ∈ jobs, job ≠ tag := by
    intro job hmember htag
    subst job
    exact stationaryPriorityClassTaggedJob_not_mem_canonicalFutureArrivalJobsBeforeHorizon
      meanService i z s hgood (by simpa [jobs, tag] using hmember)
  have harrivalStart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime := by
    intro job hmember
    rw [hinitialTime]
    exact (arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z s hgood job (by
        rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
          meanService i z s hgood]
        exact List.mem_append_left _ (by simpa [jobs] using hmember))).le
  have hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
    have hfull := pairwise_arrivalTime_le_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z s
    rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
      meanService i z s hgood] at hfull
    exact (List.pairwise_append.mp hfull).1
  have hclock : afterArrivals.currentTime ≤ s := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le initial jobs s
    · rw [hinitialTime]
      exact hs.le
    · intro job hmember
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z s job (by simpa [jobs] using hmember)).le
  have hclockLt : afterArrivals.currentTime < s := by
    apply runNonpreemptivePriorityArrivalTrace_currentTime_lt initial jobs s
    · exact harrivalStart
    · exact hsorted
    · rw [hinitialTime]
      exact hs
    · intro job hmember
      exact arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z s job (by simpa [jobs] using hmember)
  have hpositiveAfter : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using
      positiveNonpreemptivePriorityResidualWork_run initial jobs hinitialPositive hpositiveJobs
  have hclassAfter : hasClassConsistentWaiting afterArrivals := by
    simpa [afterArrivals] using
      hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace initial jobs hinitialClass
  have hboundAfter : nonpreemptivePriorityTaggedResidualLeService tag afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedResidualLeService_run_of_forall_ne
        initial jobs tag hinitialBound hnew
  have hmultAfter : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
        nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
      simpa [afterArrivals] using
        nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
          initial jobs tag hnew]
    rw [hinitialMultiplicity]
  rcases exists_active_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_of_response_sub_service
    meanService i z s u completedAt hgood hpositive hs.le hsu hstart hresponse with
      ⟨residual, hresidual, hactive⟩
  have hterminal :
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) s afterArrivals).active =
          some (tag, tag.serviceWork) := by
    have htagWork : tag.serviceWork =
        stationaryPriorityClassTaggedWorkRequirement meanService i z := by
      simpa [tag] using stationaryPriorityClassTaggedJob_serviceWork meanService i z
    rw [htagWork, ← hresidual]
    simpa [stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon,
      initial, jobs, afterArrivals, tag] using hactive
  have hwaiting : tag ∈ afterArrivals.waiting tag.priority := by
    exact mem_waiting_of_advance_active_tag_full_of_lt
      (totalNonpreemptivePriorityWorkJobs afterArrivals) s afterArrivals tag
      hclock hclockLt hpositiveAfter hclassAfter hboundAfter hmultAfter le_rfl hterminal
  have hledger :=
    nonpreemptivePriorityServiceStart_elapsed_eq_taggedPreServiceWork_add_strictArrivalWork
      initial jobs s tag harrivalStart hsorted hinitialPositive hpositiveJobs
      hinitialClass hinitialWork hinitialBound (by simpa [hinitialMultiplicity]) hnew
      hwaiting hclock hterminal
  calc
    s = s - initial.currentTime := by rw [hinitialTime]; ring
    _ = nonpreemptivePriorityTaggedPreServiceWork initial tag +
          nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := hledger
    _ = stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            nonpreemptivePriorityTaggedStrictArrivalWork
              (stationaryPriorityClassTaggedJob meanService i z)
              (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
                meanService i z s) := by
      rw [show nonpreemptivePriorityTaggedPreServiceWork initial tag =
          stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
            stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z by
          simpa [initial, tag] using
            nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
              meanService i z hgood hcutoff]

/-- The same service-start ledger holds at a zero queue wait.  There are then
no strictly post-origin arrivals before service start, and the admission state
has already dispatched the selected customer. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork_of_eq_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hu : 0 ≤ u)
    (hstart : 0 = completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    0 =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z 0) := by
  let initial := stationaryPriorityClassTaggedArrivalState meanService i z
  let jobs := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z 0
  let tag := stationaryPriorityClassTaggedJob meanService i z
  have hinitialTime : initial.currentTime = 0 := by
    simpa [initial] using
      stationaryPriorityClassTaggedArrivalState_currentTime_eq_zero meanService i z hgood
  have hjobsNil : jobs = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro job hmember
    have hlt := arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z 0 job (by simpa [jobs] using hmember)
    have hpos := arrivalTime_pos_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
      meanService i z 0 hgood job (by
        rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
          meanService i z 0 hgood]
        exact List.mem_append_left _ (by simpa [jobs] using hmember))
    linarith
  have hstrictState :
      stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z 0 =
        initial := by
    unfold stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    dsimp only
    change advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs (runNonpreemptivePriorityArrivalTrace initial jobs))
      0 (runNonpreemptivePriorityArrivalTrace initial jobs) = initial
    rw [hjobsNil]
    simp only [runNonpreemptivePriorityArrivalTrace]
    rw [show (0 : ℝ) = initial.currentTime by exact hinitialTime.symm]
    exact advanceNonpreemptivePriorityWorkState_eq_self_of_target_eq_currentTime
      (totalNonpreemptivePriorityWorkJobs initial) initial
  rcases exists_active_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_of_response_sub_service
    meanService i z 0 u completedAt hgood hpositive le_rfl hu hstart hresponse with
      ⟨residual, hresidual, hactive⟩
  have htagWork : tag.serviceWork =
      stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simpa [tag] using stationaryPriorityClassTaggedJob_serviceWork meanService i z
  have hinitialActive : initial.active = some (tag, tag.serviceWork) := by
    rw [← hstrictState, htagWork, ← hresidual]
    simpa [tag] using hactive
  have hprezero : nonpreemptivePriorityTaggedPreServiceWork initial tag = 0 :=
    nonpreemptivePriorityTaggedPreServiceWork_eq_zero_of_active
      initial tag tag.serviceWork hinitialActive
  have hpreArrival :
      nonpreemptivePriorityTaggedPreServiceWork initial tag =
        stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z := by
    simpa [initial, tag] using
      nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedArrivalState
        meanService i z hgood hcutoff
  have hstrictZero : nonpreemptivePriorityTaggedStrictArrivalWork tag jobs = 0 := by
    rw [hjobsNil]
    rfl
  calc
    0 = nonpreemptivePriorityTaggedPreServiceWork initial tag +
          nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := by
      rw [hprezero, hstrictZero]
      ring
    _ = stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            nonpreemptivePriorityTaggedStrictArrivalWork
              (stationaryPriorityClassTaggedJob meanService i z)
              (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
                meanService i z 0) := by
      rw [hpreArrival]

/-- The selected customer's queue wait is exactly its admission ledger plus
the strictly higher-priority arrivals before service start, provided a finite
response observation records that service start. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hs : 0 ≤ s) (hsu : s ≤ u)
    (hstart : s = completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt) :
    s =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
          nonpreemptivePriorityTaggedStrictArrivalWork
            (stationaryPriorityClassTaggedJob meanService i z)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
              meanService i z s) := by
  rcases hs.eq_or_lt with hzero | hpositiveWait
  · have hu : 0 ≤ u := by simpa [hzero] using hsu
    have hstartZero : 0 =
        completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
      simpa [hzero] using hstart
    simpa [hzero] using
      stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork_of_eq_zero
        meanService i z u completedAt hgood hpositive hcutoff hu hstartZero hresponse
  · exact stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork_of_pos
      meanService i z s u completedAt hgood hpositive hcutoff hpositiveWait hsu hstart hresponse

/-- The strict-arrival ledger of a finite right-closed selected-Palm future
trace is exactly the sum of the corresponding strictly higher-priority
classwise work aggregates. -/
theorem nonpreemptivePriorityTaggedStrictArrivalWork_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) :
    nonpreemptivePriorityTaggedStrictArrivalWork
      (stationaryPriorityClassTaggedJob meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) =
      ∑ j ∈ Finset.univ.filter (fun j => j < i),
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t := by
  classical
  letI : DecidableRel (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    Classical.decRel _
  letI : IsTrans (NonpreemptivePriorityArrivalIndex n)
      (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ _ => stationaryPriorityClassTaggedArrivalIndexLE_trans i z⟩
  letI : Std.Antisymm (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨fun _ _ => stationaryPriorityClassTaggedArrivalIndexLE_antisymm i z⟩
  letI : Std.Total (stationaryPriorityClassTaggedArrivalIndexLE i z) :=
    ⟨stationaryPriorityClassTaggedArrivalIndexLE_total i z⟩
  let ledger := nonpreemptivePriorityArrivalWindowIndices
    (stationaryPriorityClassTaggedFutureArrivalIndices i z t)
  rw [nonpreemptivePriorityTaggedStrictArrivalWork_eq_sum_map]
  unfold
    canonicalStationaryPriorityClassTaggedFutureArrivalJobs
    canonicalStationaryPriorityClassTaggedFutureArrivalIndices
  simp only [List.map_map]
  change (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
      (fun q => if q.1 < i then
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 else 0)).sum = _
  calc
    (ledger.sort (stationaryPriorityClassTaggedArrivalIndexLE i z) |>.map
        (fun q => if q.1 < i then
          stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 else 0)).sum =
        (ledger.toList.map fun q => if q.1 < i then
          stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 else 0).sum :=
      ((Finset.sort_perm_toList ledger
        (stationaryPriorityClassTaggedArrivalIndexLE i z)).map _).sum_eq
    _ = ∑ q ∈ ledger, if q.1 < i then
        stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 else 0 := by
      simpa only [ledger.toList_toFinset] using
        (List.sum_toFinset
          (fun q => if q.1 < i then
            stationaryPriorityClassTaggedWorkRequirementAt meanService i z q.1 q.2 else 0)
          ledger.nodup_toList).symm
    _ = ∑ j ∈ Finset.univ.filter (fun j => j < i),
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t := by
      unfold ledger nonpreemptivePriorityArrivalWindowIndices
        stationaryPriorityTaggedFutureWorkAggregate
        stationaryPriorityClassTaggedFutureArrivalIndices
      rw [Finset.sum_sigma]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j < i
      · have hne : j ≠ i := ne_of_lt hji
        simp [hji, hne]
      · simp [hji]

/-- If no strictly higher-priority customer arrives exactly at a queried
horizon, the strict causal ledger through that horizon equals the associated
right-closed strict-priority input aggregate. -/
theorem nonpreemptivePriorityTaggedStrictArrivalWork_beforeHorizon_eq_strictFutureAggregate
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hboundary : ∀ job ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z t,
      ¬ job.priority < i) :
    nonpreemptivePriorityTaggedStrictArrivalWork
      (stationaryPriorityClassTaggedJob meanService i z)
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i z t) =
      ∑ j ∈ Finset.univ.filter (fun j => j < i),
        stationaryPriorityTaggedFutureWorkAggregate meanService i z j t := by
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z t
  let tail := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z t
  have htail : ∀ job ∈ tail, ¬ job.priority < tag.priority := by
    simpa [tag, tail] using hboundary
  have happend := nonpreemptivePriorityTaggedStrictArrivalWork_append_of_forall_not_lt
    tag front tail htail
  have hsplit := canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
    meanService i z t hgood
  calc
    nonpreemptivePriorityTaggedStrictArrivalWork tag front =
        nonpreemptivePriorityTaggedStrictArrivalWork tag (front ++ tail) := happend.symm
    _ = nonpreemptivePriorityTaggedStrictArrivalWork tag
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z t) := by
        rw [hsplit]
    _ = ∑ j ∈ Finset.univ.filter (fun j => j < i),
          stationaryPriorityTaggedFutureWorkAggregate meanService i z j t := by
        simpa [tag] using
          nonpreemptivePriorityTaggedStrictArrivalWork_canonicalStationaryPriorityClassTaggedFutureArrivalJobs
            meanService i z t

/-- A passive-arrival no-tie certificate excludes strictly higher-priority
jobs from the boundary portion of a finite selected-Palm future ledger. -/
theorem no_strict_priority_boundary_job_of_passive_arrival_ne
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (ht : 0 ≤ t)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hnoTie : ∀ (j : {k : Fin n // k ≠ i}) (N : ℕ),
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 (Int.ofNat (N + 1)) ≠ t) :
    ∀ job ∈ canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z t,
      ¬ job.priority < i := by
  intro job hjob hpriority
  unfold canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon at hjob
  rcases List.mem_map.mp hjob with ⟨q, hq, rfl⟩
  have hqindex : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon
      i z t q.1 := by
    simpa [canonicalStationaryPriorityClassTaggedFutureArrivalIndicesAtHorizon,
      nonpreemptivePriorityArrivalWindowIndices] using hq
  have hqfuture : q.2 ∈ stationaryPriorityClassTaggedFutureArrivalIndices i z t q.1 := by
    exact (Finset.mem_filter.mp hqindex).1
  have hne : q.1 ≠ i := ne_of_lt hpriority
  have hqpassive : q.2 ∈ Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed
      0 t (z.2 ⟨q.1, hne⟩).1 := by
    simpa [stationaryPriorityClassTaggedFutureArrivalIndices, hne] using hqfuture
  rw [Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_eq_futureCanonicalIndices
    (z.2 ⟨q.1, hne⟩).1 t ht] at hqpassive
  rcases Finset.mem_image.mp hqpassive with ⟨N, _, hqEq⟩
  have harrival : stationaryPriorityClassTaggedArrival i z q.1 q.2 = t := by
    exact stationaryPriorityClassTaggedArrival_eq_horizon_of_mem_futureAtHorizon
      i z t hgood q.1 q.2 hqindex
  apply hnoTie ⟨q.1, hne⟩ N
  rw [hqEq]
  simpa [stationaryPriorityClassTaggedArrival,
    multiclassStationaryPoissonWorkClassTaggedArrival, hne] using harrival

/-- A finite recorded response and a passive-arrival no-tie certificate give
the literal selected queue wait as its two admission-state work terms plus
the right-closed strictly higher-priority future-work aggregate. -/
theorem stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictFutureWork_of_response
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (u completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hpositive : ∀ j k,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i z j k)
    (hcutoff : ∃ cutoff : ℝ, 0 ≤ cutoff ∧
      stationaryPriorityClassTaggedNetPastCutoff meanService i z cutoff)
    (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z)
    (horizon : stationaryPriorityClassTaggedQueueWait meanService i z ≤ u)
    (hstart : stationaryPriorityClassTaggedQueueWait meanService i z =
      completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z)
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some completedAt)
    (hnoTie : ∀ (j : {k : Fin n // k ≠ i}) (N : ℕ),
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 (Int.ofNat (N + 1)) ≠
        stationaryPriorityClassTaggedQueueWait meanService i z) :
    stationaryPriorityClassTaggedQueueWait meanService i z =
      stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
        stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
          stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z := by
  let wait := stationaryPriorityClassTaggedQueueWait meanService i z
  have hboundary : ∀ job ∈
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z wait,
      ¬ job.priority < i := by
    exact no_strict_priority_boundary_job_of_passive_arrival_ne
      meanService i z wait hwait hgood (by simpa [wait] using hnoTie)
  have hstrict := nonpreemptivePriorityTaggedStrictArrivalWork_beforeHorizon_eq_strictFutureAggregate
    meanService i z wait hgood hboundary
  have hledger := stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictArrivalWork
    meanService i z wait u completedAt hgood hpositive hcutoff hwait horizon
      (by simpa [wait] using hstart) hresponse
  calc
    stationaryPriorityClassTaggedQueueWait meanService i z =
        stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            nonpreemptivePriorityTaggedStrictArrivalWork
              (stationaryPriorityClassTaggedJob meanService i z)
              (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
                meanService i z wait) := hledger
    _ = stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            (∑ j ∈ Finset.univ.filter (fun j => j < i),
              stationaryPriorityTaggedFutureWorkAggregate meanService i z j wait) := by
      rw [hstrict]
    _ = stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z := by
      unfold stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
      rfl

/-- On the stable selected-Palm carrier, the predictable strict-horizon FIFO
observation is exactly the indicator that the literal queue wait has not yet
elapsed. -/
theorem ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ s : ℝ, 0 ≤ s →
        (nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
          (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z s) ↔
          s < stationaryPriorityClassTaggedQueueWait meanService i z) := by
  filter_upwards [
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good arrivalRate harrivalRate i,
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalState_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hgood hfull
  intro s hs
  exact (nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff
    meanService i z s hs hgood).trans (hfull s hs)

/-- Before the literal selected queue-wait endpoint, the tagged-service
ledger has the exact physical pre-arrival/elapsed-time/future-work
decomposition almost surely.  This strict-horizon statement complements the
separate finite service-start result for a positive queue wait. -/
theorem ae_forall_nonpreemptivePriorityTaggedPreServiceWork_before_lt_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ t : ℝ, 0 ≤ t → t < stationaryPriorityClassTaggedQueueWait meanService i z →
        nonpreemptivePriorityTaggedPreServiceWork
            (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
              meanService i z t)
            (stationaryPriorityClassTaggedJob meanService i z) =
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
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hgood hcutoff hwaiting
  intro t ht hlt
  have hwaitingId : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t) :=
    (hwaiting t ht).mpr hlt
  have hwaitingTag : stationaryPriorityClassTaggedJob meanService i z ∈
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z t).waiting i :=
    (stationaryPriorityClassTaggedJob_mem_waiting_iff_waitingIdentifier_beforeHorizon
      meanService i z t hgood hcutoff).mpr hwaitingId
  exact nonpreemptivePriorityTaggedPreServiceWork_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_eq_preArrival
    meanService i z t ht hgood hcutoff hwaitingTag

/-- For each deterministic nonnegative horizon, sufficiently remote strict
finite replays equal the literal selected-Palm queue-wait indicator.  This is
the pointwise stabilization statement used before passing a stopped reward to
an unbounded future horizon. -/
theorem ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) (t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
          meanService i z older t =
          if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_coalescence
      arrivalRate meanService harrivalRate hmeanService hstable i t,
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalescence hwaiting
  rcases hcoalescence with ⟨cutoff, hcutoff, hcoalescence⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro older holder
  rw [hcoalescence older holder]
  unfold nonpreemptivePriorityWaitingIdentifierIndicator
  rw [hwaiting t ht]

/-- A single remote-past cutoff makes every nonnegative strict finite-horizon
tagged-waiting observation agree with the literal queue-wait indicator.  This
uniform form is what permits a finite stopped-index argument to inspect all
of its candidate arrival horizons under one coalesced replay. -/
theorem ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        ∀ t : ℝ, 0 ≤ t →
          stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
            meanService i z older t =
            if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_forall_nonpreemptivePriorityWaitingIdentifier_finitePostArrivalStateBeforeHorizon_iff_lt_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i] with z hcoalescence hwaiting
  rcases hcoalescence with ⟨cutoff, hcutoff, hcoalescence⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro older holder t ht
  rw [stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_eq_of_liveEquivalent
    meanService i z older t (hcoalescence older holder)]
  unfold nonpreemptivePriorityWaitingIdentifierIndicator
  rw [hwaiting t ht]

/-- Before a strict causal horizon, FIFO membership of the selected
identifier means that the unique selected record has neither begun service
nor entered the completion ledger. -/
theorem not_exists_stationaryPriorityClassTagged_active_or_completed_of_waitingBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (t : ℝ) (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hwaiting : nonpreemptivePriorityWaitingIdentifier (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t)) :
    (¬ ∃ residual,
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual)) ∧
      (¬ ∃ completedAt,
        (stationaryPriorityClassTaggedJob meanService i z, completedAt) ∈
          (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
            meanService i z t).completed) := by
  rcases hwaiting with ⟨priority, job, hmember, hidentifier⟩
  have htag : job = stationaryPriorityClassTaggedJob meanService i z := by
    apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalStateBeforeHorizon_of_identifier_eq
      meanService i z t job hgood
    · exact Or.inr (Or.inl ⟨priority, hmember⟩)
    · exact hidentifier
  subst job
  apply not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
    (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z t)
    (stationaryPriorityClassTaggedJob meanService i z) priority hmember
  rw [nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z t hgood]

/-- A strict finite selected replay has a Borel tagged-waiting observation at
every Borel sample-dependent right horizon.  The countable fixed-skeleton
cover freezes precisely the discrete FIFO placement of the tagged identifier.
-/
theorem measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n) (older : ℝ)
    (target : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ)
    (htarget : Measurable target) :
    Measurable (fun z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i z older (target z)) := by
  let Piece := List (NonpreemptivePriorityArrivalIndex n) ×
    List (NonpreemptivePriorityArrivalIndex n) ×
      StationaryPriorityClassTaggedFixedReplaySkeleton
  refine Probability.measurable_of_countable_measurable_cover
    (fun q : Piece =>
      stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
        i older target q.1 q.2.1 ∩
        {z | stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
          meanService i older target q.1 q.2.1 q.2.2 z})
    ?_ ?_
    (fun z => stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i z older (target z))
    (fun q => fixedNonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFixedReplayStateAt
        meanService i older target q.1 q.2.1 q.2.2))
    ?_ ?_
  · intro q
    exact (measurableSet_stationaryPriorityClassTaggedFiniteReplayLedgerFiberBeforeHorizonAt
      i older target htarget q.1 q.2.1).inter
      (measurableSet_stationaryPriorityClassTaggedFixedReplayBranchMatchesAt
        meanService i older target htarget q.1 q.2.1 q.2.2)
  · ext z
    constructor
    · intro _
      simp
    · intro _
      let pastLabels := canonicalStationaryPriorityClassTaggedArrivalWindowIndices
        i z (-older) 0
      let futureLabels := canonicalStationaryPriorityClassTaggedFutureArrivalIndicesBeforeHorizon
        i z (target z)
      let initial := stationaryPriorityClassTaggedFixedPastInitial i older
      let pastJobs := stationaryPriorityClassTaggedFixedJobs meanService i pastLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches initial pastJobs z with
        ⟨pastArrivalSlots, hpastArrivals⟩
      let pastAfter := runFixedPriorityArrivalTraceBranch initial pastJobs pastArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs pastAfter) (fun _ => 0) pastAfter z with
        ⟨pastTerminalCompletionCount, pastTerminal, hpastTerminal⟩
      let skeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := []
          futureTerminalCompletionCount := 0
          futureTerminal := .hold }
      let postTag := stationaryPriorityClassTaggedFixedPostTagState
        meanService i older pastLabels skeleton
      let futureJobs := stationaryPriorityClassTaggedFixedJobs meanService i futureLabels
      rcases exists_fixedPriorityArrivalTraceBranchMatches postTag futureJobs z with
        ⟨futureArrivalSlots, hfutureArrivals⟩
      let postFuture := runFixedPriorityArrivalTraceBranch postTag futureJobs futureArrivalSlots
      rcases exists_fixedPriorityAdvanceBranchMatches
        (totalFixedNonpreemptivePriorityWorkJobs postFuture) target postFuture z with
        ⟨futureTerminalCompletionCount, futureTerminal, hfutureTerminal⟩
      let finalSkeleton : StationaryPriorityClassTaggedFixedReplaySkeleton :=
        { pastArrivalSlots := pastArrivalSlots
          pastTerminalCompletionCount := pastTerminalCompletionCount
          pastTerminal := pastTerminal
          futureArrivalSlots := futureArrivalSlots
          futureTerminalCompletionCount := futureTerminalCompletionCount
          futureTerminal := futureTerminal }
      refine Set.mem_iUnion.mpr ⟨(pastLabels, futureLabels, finalSkeleton), ?_⟩
      refine ⟨?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨hpastArrivals, hpastTerminal, hfutureArrivals, hfutureTerminal⟩
  · intro q
    exact measurable_fixedNonpreemptivePriorityWaitingIdentifierIndicator
      (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFixedReplayStateAt
        meanService i older target q.1 q.2.1 q.2.2)
  · intro q z hz
    rcases hz with ⟨hledger, hmatches⟩
    unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
    symm
    change fixedNonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFixedReplayStateAt
          meanService i older target q.1 q.2.1 q.2.2) z =
      nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
        (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
          meanService i z older (target z))
    rw [fixedNonpreemptivePriorityWaitingIdentifierIndicator_eval]
    rw [stationaryPriorityClassTaggedFixedReplayStateAt_eval_eq_finiteReplayStateBeforeHorizon_of_matches
      meanService i older target q.1 q.2.1 q.2.2 z hledger hmatches]

/-- The variable finite-prefix deterministic-clock waiting observation is
Borel.  Its proof pastes the fixed-prefix formulas along the countably many
external renewal-count fibers. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older t : ℝ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation
      meanService i j older t) := by
  let count := multiclassPalmFutureMarkExternalFutureCountThrough i j t
  let Piece := MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)
  let piece : ℕ → Piece → ℝ := fun N z =>
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
        (multiclassPalmFutureMarkPrefixRepresentative i j N (z.1, fun r => z.2 r)))
      older t
  refine Probability.measurable_of_countable_measurable_cover
    (fun N : ℕ => {z : Piece | count z.1 = N}) ?_ ?_
    (stationaryPriorityClassTaggedFutureMarkDeterministicWaitingObservation
      meanService i j older t) piece ?_ ?_
  · intro N
    change MeasurableSet ((fun z : Piece => count z.1) ⁻¹' {N})
    exact ((measurable_multiclassPalmFutureMarkExternalFutureCountThrough i j t).comp
      measurable_fst) (measurableSet_singleton N)
  · ext z
    simp
  · intro N
    apply (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
      meanService i older (fun _ => t) measurable_const).comp
    apply (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm.measurable.comp
    apply (measurable_multiclassPalmFutureMarkPrefixRepresentative i j N).comp
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro r
    exact (measurable_pi_apply (X := fun _ : ℕ => ℝ) r).comp measurable_snd
  · intro N z hz
    change count z.1 = N at hz
    subst N
    rfl

/-- The Borel tagged-waiting observation obtained from the external factor and
the first `N` isolated future service marks.  It is evaluated strictly before
the `(N+1)`st isolated passive arrival, so the next mark is not inspected. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkPrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range N → ℝ) → ℝ :=
  fun x =>
    stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
      meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
        (multiclassPalmFutureMarkPrefixRepresentative i j N x)) older
      (stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm
          (multiclassPalmFutureMarkPrefixRepresentative i j N x))
        j.1 (Int.ofNat (N + 1)))

/-- The finite-prefix tagged-waiting observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkPrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkPrefixWaiting
      meanService i j older N) := by
  apply (measurable_stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon_at
    meanService i older
    (fun z => stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1)))
    (measurable_stationaryPriorityClassTaggedArrival i j.1 (Int.ofNat (N + 1)))).comp
  exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm.measurable.comp
    (measurable_multiclassPalmFutureMarkPrefixRepresentative i j N)

/-- With a fixed remote-past cutoff, the finite state immediately before the
`(N+1)`st isolated passive arrival depends only on the external factor and the
first `N` isolated future marks. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_futureMark_prefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x y : MulticlassPalmFutureMarkFactorCarrier i j) (N : ℕ) (older : ℝ)
    (hxy : x.1 = y.1) (hprefix : ∀ r < N, x.2 r = y.2 r)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
          j.1 (Int.ofNat (N + 1))) := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let w := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y
  let t := stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (N + 1))
  let u := stationaryPriorityClassTaggedArrival i w j.1 (Int.ofNat (N + 1))
  change stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t =
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i w older u
  have ht : t = u := by
    simpa [t, z, w] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
        i j x y j.1 (Int.ofNat (N + 1)) hxy)
  have hpast : canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0 =
      canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i w (-older) 0 := by
    simpa [z, w] using
      (canonicalStationaryPriorityClassTaggedFiniteWindowState_eq_of_futureMark_factor
        meanService i j x y older hxy hgood)
  have htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w := by
    unfold stationaryPriorityClassTaggedJob
    rw [show stationaryPriorityClassTaggedArrival i z i 0 =
        stationaryPriorityClassTaggedArrival i w i 0 by
      simpa [z, w] using
        (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_arrival_eq_of_fst_eq
          i j x y i 0 hxy)]
    rw [show stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w i 0 by
      exact congrArg (fun r => meanService i * r)
        (by simpa [z, w] using
          (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_selectedRequirement_eq_of_fst_eq
            i j x y 0 hxy))]
  have hfuture : canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
      meanService i z t =
      canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon meanService i w u := by
    simpa [z, w, t, u] using
      (canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon_eq_of_futureMark_prefix
        meanService i j x y N hxy hprefix)
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_pastState_eq
    meanService i z w older t u ht hpast htag hfuture

/-- On a good selected suspension, the literal strict replay has the same
tagged-waiting value as its external-factor/future-mark prefix representative. -/
theorem stationaryPriorityClassTaggedFutureMarkPrefixWaiting_eq_of_good
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).1.1) :
    stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older N
      (x.1, fun r => x.2 r) =
      stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (N + 1))) := by
  let y : MulticlassPalmFutureMarkFactorCarrier i j :=
    multiclassPalmFutureMarkPrefixRepresentative i j N (x.1, fun r => x.2 r)
  have hfst : x.1 = y.1 := by
    rfl
  have hprefix : ∀ r < N, x.2 r = y.2 r := by
    intro r hr
    change x.2 r = futureMarkPrefixZeroExtension N (fun s => x.2 s) r
    rw [futureMarkPrefixZeroExtension_eq_of_lt N (fun s => x.2 s) r hr]
  have heq :=
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_futureMark_prefix
      meanService i j x y N older hfst hprefix hgood
  change nonpreemptivePriorityWaitingIdentifierIndicator (Sigma.mk i 0)
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y) older
        (stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm y)
          j.1 (Int.ofNat (N + 1)))) = _
  unfold stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
  rw [← heq]

/-- Evaluate the finite-prefix tagged-waiting observation on an external state
and an entire IID stream by retaining only its first `N` coordinates. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
  fun z => stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older N
    (z.1, fun r => z.2 r)

/-- The finite-prefix tagged-waiting observation is Borel on the
external-state/IID-stream carrier. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
      meanService i j older N) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixWaiting
    meanService i j older N).comp
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro r
  exact (measurable_pi_apply (X := fun _ : ℕ => ℝ) r).comp measurable_snd

/-- Under the factored selected-Palm law, one remote-past cutoff makes every
isolated-arrival waiting observation agree with the literal queue-wait
indicator.  The result is simultaneous in the isolated arrival index, so any
deterministically capped service-start stop may use a single finite replay. -/
theorem ae_exists_stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_eq_queueWaitIndicator_all
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older → ∀ N : ℕ,
        stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
          meanService i j older N x =
          if stationaryPriorityClassTaggedArrival i
              ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
              j.1 (Int.ofNat (N + 1)) <
              stationaryPriorityClassTaggedQueueWait meanService i
                ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          then 1 else 0 := by
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  let μ := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let ν := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  have hpres : MeasurePreserving e μ ν := by
    simpa [e, μ, ν] using
      (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
        arrivalRate harrivalRate i j)
  have hsource : ∀ᵐ z ∂μ,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        ∀ t : ℝ, 0 ≤ t →
          stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
            meanService i z older t =
            if t < stationaryPriorityClassTaggedQueueWait meanService i z then 1 else 0 := by
    simpa [μ] using
      (ae_exists_stationaryPriorityClassTaggedFiniteReplayWaitingBeforeHorizon_eq_queueWaitIndicator_all
        arrivalRate meanService harrivalRate hmeanService hstable i)
  have hback : MeasurePreserving e.symm ν μ := by
    exact hpres.symm e
  rw [← hback.map_eq] at hsource
  have hsource' : ∀ᵐ x ∂ν,
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older →
        ∀ t : ℝ, 0 ≤ t →
          stationaryPriorityClassTaggedFiniteReplayWaitingIndicatorBeforeHorizon
            meanService i (e.symm x) older t =
            if t < stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) then 1 else 0 := by
    exact ae_of_ae_map hback.measurable.aemeasurable hsource
  filter_upwards [hsource', ae_multiclassPalmFutureMarkFactor_good_and_positive
    arrivalRate meanService harrivalRate hmeanService i j] with x hcut hx
  rcases hx with ⟨hgood, _⟩
  rcases hcut with ⟨cutoff, hcutoff, hcut⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro older holder N
  have harrival_nonneg : 0 ≤ stationaryPriorityClassTaggedArrival i (e.symm x)
      j.1 (Int.ofNat (N + 1)) := by
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2] using
      (Probability.PoissonProcess.zero_lt_suspensionBaseArrival_ofNat_succ
        ((e.symm x).2 j).1 N).le
  rw [show stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
      meanService i j older N x =
      stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older N
        (x.1, fun r => x.2 r) by rfl]
  rw [stationaryPriorityClassTaggedFutureMarkPrefixWaiting_eq_of_good
    meanService i j older N x (by simpa [e] using hgood)]
  simpa [e] using hcut older holder
    (stationaryPriorityClassTaggedArrival i (e.symm x) j.1 (Int.ofNat (N + 1)))
    harrival_nonneg

/-- The number of isolated passive arrivals observed before the literal queue
wait, capped at a deterministic index.  This is the physical count which the
predictable capped service-start index will represent after remote-past
coalescence. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    MulticlassPalmFutureMarkFactorCarrier i j → ℕ := by
  classical
  intro x
  exact if h : ∃ m < cap,
      ¬ stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (m + 1)) <
          stationaryPriorityClassTaggedQueueWait meanService i
            ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
    then Nat.find h else cap

/-- The physical capped queue-wait count never exceeds its deterministic cap. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_le_cap
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount meanService i j cap x ≤ cap := by
  classical
  unfold stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- Enlarging the deterministic index cap can only enlarge the number of
isolated arrivals observed strictly before the tagged queue wait. -/
theorem monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    Monotone (fun cap : ℕ =>
      stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount meanService i j cap x) := by
  classical
  intro cap cap' hcapcap'
  let P : ℕ → Prop := fun m =>
    ¬ stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (m + 1)) <
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
  change (if h : ∃ m < cap, P m then Nat.find h else cap) ≤
    if h : ∃ m < cap', P m then Nat.find h else cap'
  by_cases h : ∃ m < cap, P m
  · have h' : ∃ m < cap', P m := by
      rcases h with ⟨m, hmcap, hm⟩
      exact ⟨m, lt_of_lt_of_le hmcap hcapcap', hm⟩
    rw [dif_pos h, dif_pos h']
    apply Nat.find_min' h
    have hfirst : Nat.find h' ≤ Nat.find h :=
      Nat.find_min' h' ⟨(Nat.find_spec h).1.trans_le hcapcap',
        (Nat.find_spec h).2⟩
    exact ⟨lt_of_le_of_lt hfirst (Nat.find_spec h).1, (Nat.find_spec h').2⟩
  · rw [dif_neg h]
    by_cases h' : ∃ m < cap', P m
    · rw [dif_pos h']
      apply Nat.le_of_not_gt
      intro hlt
      exact h ⟨Nat.find h', hlt, (Nat.find_spec h').2⟩
    · rw [dif_neg h']
      exact hcapcap'

/-- Every passive renewal path has a first labelled arrival that is not
strictly before the tagged queue-wait horizon.  This is a pathwise
nonexplosion consequence; no queueing tail estimate is used. -/
theorem exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    ∃ m : ℕ,
      ¬ stationaryPriorityClassTaggedArrival i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
          j.1 (Int.ofNat (m + 1)) <
          stationaryPriorityClassTaggedQueueWait meanService i
            ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  have htend := Probability.PoissonProcess.tendsto_suspensionBaseArrival_ofNat_succ_atTop
    (z.2 j).1
  have hlarge : ∀ᶠ m : ℕ in Filter.atTop,
      stationaryPriorityClassTaggedQueueWait meanService i z ≤
        Probability.PoissonProcess.suspensionBaseArrival (z.2 j).1
          (Int.ofNat (m + 1)) :=
    Filter.tendsto_atTop.1 htend (stationaryPriorityClassTaggedQueueWait meanService i z)
  rcases Filter.eventually_atTop.1 hlarge with ⟨m, hm⟩
  refine ⟨m, ?_⟩
  simpa [z, stationaryPriorityClassTaggedArrival,
    multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2] using
    (not_lt.mpr (hm m le_rfl))

/-- The finite first index at which the isolated passive arrival is no
longer strictly before the tagged queue wait. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkQueueWaitCount
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) :
    MulticlassPalmFutureMarkFactorCarrier i j → ℕ :=
  fun x => Nat.find
    (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
      meanService i j x)

/-- A deterministic capped count is exactly the minimum of the cap and the
finite first-failure index. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount meanService i j cap x =
      min cap (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x) := by
  classical
  let P : ℕ → Prop := fun m =>
    ¬ stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (m + 1)) <
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
  let q := stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x
  have hexists : ∃ m, P m := by
    simpa [P] using
      (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
        meanService i j x)
  have hq : P q := by
    simpa [q, P, stationaryPriorityClassTaggedFutureMarkQueueWaitCount] using
      (Nat.find_spec
        (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
          meanService i j x))
  have hqmin : ∀ m, P m → q ≤ m := by
    intro m hm
    simpa [q, P, stationaryPriorityClassTaggedFutureMarkQueueWaitCount] using
      (Nat.find_min'
        (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
          meanService i j x) (by simpa [P] using hm))
  change (if h : ∃ m < cap, P m then Nat.find h else cap) = min cap q
  by_cases hqc : q < cap
  · have hcap : ∃ m < cap, P m := ⟨q, hqc, hq⟩
    rw [dif_pos hcap, min_eq_right hqc.le]
    apply Nat.le_antisymm
    · exact Nat.find_min' hcap ⟨hqc, hq⟩
    · exact hqmin (Nat.find hcap) (Nat.find_spec hcap).2
  · have hcap : ¬ ∃ m < cap, P m := by
      rintro ⟨m, hm, hP⟩
      exact (not_lt_of_ge (hqmin m hP)) (hm.trans_le (Nat.le_of_not_gt hqc))
    rw [dif_neg hcap, min_eq_left (Nat.le_of_not_gt hqc)]

/-- Refining the deterministic cap sends the capped isolated-arrival count to
the finite first-failure index.  In fact the sequence is eventually constant. -/
theorem tendsto_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    Filter.Tendsto (fun cap : ℕ =>
      stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount meanService i j cap x)
      Filter.atTop
      (nhds (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x)) := by
  apply tendsto_nhds_of_eventually_eq
  refine Filter.eventually_atTop.2
    ⟨stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x, ?_⟩
  intro cap hcap
  rw [stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min]
  exact min_eq_right hcap

/-- The finite first-failure index is bounded by the literal right-closed
passive-arrival count through the same queue-wait horizon. -/
theorem stationaryPriorityClassTaggedFutureMarkQueueWaitCount_le_rightClosedCard
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x ≤
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x))
        (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1).card := by
  classical
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let q := stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x
  let S : Finset ℕ := Finset.range q
  let f : ℕ → ℤ := fun r => Int.ofNat (r + 1)
  let L : Finset ℤ := Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
    (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1
  have hstrict : ∀ r < q,
      stationaryPriorityClassTaggedArrival i z j.1 (Int.ofNat (r + 1)) <
        stationaryPriorityClassTaggedQueueWait meanService i z := by
    intro r hr
    by_contra hnot
    have hfailure : ¬ stationaryPriorityClassTaggedArrival i z j.1
        (Int.ofNat (r + 1)) < stationaryPriorityClassTaggedQueueWait meanService i z := hnot
    have hmin := Nat.find_min
      (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
        meanService i j x)
      (by simpa [q, stationaryPriorityClassTaggedFutureMarkQueueWaitCount] using hr)
    exact hmin (by simpa [z] using hfailure)
  have himage : S.image f ⊆ L := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨r, hr, rfl⟩
    have hrq : r < q := Finset.mem_range.mp (by simpa [S] using hr)
    have hlt := hstrict r hrq
    have hpos : 0 < Probability.PoissonProcess.suspensionBaseArrival (z.2 j).1
        (Int.ofNat (r + 1)) :=
      Probability.PoissonProcess.zero_lt_suspensionBaseArrival_ofNat_succ (z.2 j).1 r
    have hltpassive : Probability.PoissonProcess.suspensionBaseArrival (z.2 j).1
        (Int.ofNat (r + 1)) < stationaryPriorityClassTaggedQueueWait meanService i z := by
      simpa [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2] using hlt
    change Int.ofNat (r + 1) ∈ L
    rw [Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff]
    constructor
    · simpa [z] using hpos
    · simpa [z] using hltpassive.le
  have hinj : Function.Injective f := by
    intro r s hrs
    exact Nat.add_right_cancel (Int.ofNat_inj.mp hrs)
  change q ≤ L.card
  calc
    q = S.card := by simp [S]
    _ = (S.image f).card := (Finset.card_image_of_injective S hinj).symm
    _ ≤ L.card := Finset.card_le_card himage

/-- The literal isolated-class work accrued before the tagged queue wait,
truncated at a deterministic arrival-index cap. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    MulticlassPalmFutureMarkFactorCarrier i j → ℝ :=
  fun x => ∑ r ∈ Finset.range (cap + 1),
    if r < stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
      meanService i j cap x then meanService j.1 * x.2 r else 0

/-- With nonnegative service work, enlarging the deterministic index cap can
only enlarge the accrued isolated-class work before the tagged queue wait. -/
theorem monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hmean : 0 ≤ meanService j.1) (hwork : ∀ r, 0 ≤ x.2 r) :
    Monotone (fun cap : ℕ =>
      stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap x) := by
  intro cap cap' hcapcap'
  let count : ℕ → ℕ := fun cap =>
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount meanService i j cap x
  let reward : ℕ → ℝ := fun r => meanService j.1 * x.2 r
  have hcount : count cap ≤ count cap' := by
    exact monotone_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
      meanService i j x hcapcap'
  have hsubset : Finset.range (cap + 1) ⊆ Finset.range (cap' + 1) := by
    exact Finset.range_subset_range.mpr (Nat.succ_le_succ hcapcap')
  change (∑ r ∈ Finset.range (cap + 1), if r < count cap then reward r else 0) ≤
    ∑ r ∈ Finset.range (cap' + 1), if r < count cap' then reward r else 0
  calc
    (∑ r ∈ Finset.range (cap + 1), if r < count cap then reward r else 0) ≤
        ∑ r ∈ Finset.range (cap' + 1), if r < count cap then reward r else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
          intro r _ hrange
          by_cases hlt : r < count cap
          · simp [hlt, reward, mul_nonneg hmean (hwork r)]
          · simp [hlt]
    _ ≤ ∑ r ∈ Finset.range (cap' + 1), if r < count cap' then reward r else 0 := by
      apply Finset.sum_le_sum
      intro r _
      by_cases hlt : r < count cap
      · have hlt' : r < count cap' := lt_of_lt_of_le hlt hcount
        simp [hlt, hlt']
      · by_cases hlt' : r < count cap'
        · exact (by simp [hlt, hlt', reward, mul_nonneg hmean (hwork r)])
        · simp [hlt, hlt']

/-- The literal isolated-class marked work accumulated strictly before the
tagged queue wait.  The first-failure index makes this a finite sum on every
nonexplosive passive renewal path. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkQueueWaitWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) :
    MulticlassPalmFutureMarkFactorCarrier i j → ℝ :=
  fun x => ∑ r ∈ Finset.range
    (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x),
      meanService j.1 * x.2 r

/-- Once its cap reaches the first-failure index, the capped marked work is
exactly the literal strict-before-wait marked sum. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork_eq_queueWaitWork_of_le
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (cap : ℕ)
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hcap : stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x ≤ cap) :
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap x =
      stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x := by
  let q := stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x
  let reward : ℕ → ℝ := fun r => meanService j.1 * x.2 r
  unfold stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    stationaryPriorityClassTaggedFutureMarkQueueWaitWork
  rw [stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_eq_min,
    min_eq_right hcap]
  change (∑ r ∈ Finset.range (cap + 1), if r < q then reward r else 0) =
    ∑ r ∈ Finset.range q, reward r
  have hsubset : Finset.range q ⊆ Finset.range (cap + 1) := by
    exact Finset.range_subset_range.mpr (Nat.lt_succ_of_le hcap).le
  calc
    (∑ r ∈ Finset.range (cap + 1), if r < q then reward r else 0) =
        ∑ r ∈ Finset.range q, if r < q then reward r else 0 := by
          symm
          apply Finset.sum_subset hsubset
          intro r hr hrnot
          have hqle : q ≤ r := Nat.le_of_not_gt (by simpa using hrnot)
          simp [not_lt.mpr hqle]
    _ = ∑ r ∈ Finset.range q, reward r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp [Finset.mem_range.mp hr]

/-- The capped marked-work sequence converges by eventual equality to the
literal strict-before-wait marked sum. -/
theorem tendsto_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j) :
    Filter.Tendsto (fun cap : ℕ =>
      stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap x)
      Filter.atTop
      (nhds (stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x)) := by
  apply tendsto_nhds_of_eventually_eq
  refine Filter.eventually_atTop.2
    ⟨stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x, ?_⟩
  intro cap hcap
  exact stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork_eq_queueWaitWork_of_le
    meanService i j cap x hcap

/-- The finite-prefix waiting observation after `N+1` coordinates is the
prefix function evaluated on the visible IID marks through coordinate `N`. -/
theorem stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_succ
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
      meanService i j older (N + 1) z =
      stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older (N + 1)
        (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
          MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) := by
  rfl

/-- The waiting observation before any isolated future mark is read from the
external state alone. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) :
    MulticlassPalmFutureMarkExternalCarrier i j → ℝ :=
  fun s => stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older 0
    (s, emptyFutureMarkPrefix)

/-- The zero-coordinate waiting observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) :
    Measurable (stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
      meanService i j older) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixWaiting
    meanService i j older 0).comp
  exact measurable_id.prodMk measurable_const

/-- At coordinate zero the stream-level observation is its external
zero-prefix representative. -/
theorem stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
      meanService i j older 0 z =
      stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting meanService i j older z.1 := by
  unfold stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
    stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
  apply congrArg (stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older 0)
  apply Prod.ext
  · rfl
  · funext r
    exact False.elim (Nat.not_lt_zero r.1 (Finset.mem_range.mp r.2))

/-- The bounded first isolated-arrival index by which the tagged service has
begun.  It equals the cap if the tag remains waiting at every earlier
observation. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedServiceStart
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℕ := by
  classical
  intro z
  exact if h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
        meanService i j older m z ≠ 1
    then Nat.find h else cap

/-- The finite replay service-start index never exceeds its deterministic
cap. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedServiceStart_le_cap
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      meanService i j older cap z ≤ cap := by
  classical
  unfold stationaryPriorityClassTaggedFutureMarkCappedServiceStart
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- Strictly before the capped service-start index, the tag is still waiting
at every queried isolated arrival. -/
theorem lt_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_iff
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap q : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    q < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      meanService i j older cap z ↔
      q < cap ∧ ∀ m ≤ q,
        stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
          meanService i j older m z = 1 := by
  classical
  unfold stationaryPriorityClassTaggedFutureMarkCappedServiceStart
  by_cases h : ∃ m < cap,
      stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
        meanService i j older m z ≠ 1
  · rw [dif_pos h]
    constructor
    · intro hq
      rcases Nat.find_spec h with ⟨hcap, hne⟩
      refine ⟨lt_of_lt_of_le hq (Nat.le_of_lt hcap), ?_⟩
      intro m hm
      by_contra hwaiting
      have hmcap : m < cap :=
        lt_of_le_of_lt hm (lt_of_lt_of_le hq (Nat.le_of_lt hcap))
      have hmin : Nat.find h ≤ m := Nat.find_min' h ⟨hmcap, hwaiting⟩
      exact (Nat.not_lt_of_ge hmin) (lt_of_le_of_lt hm hq)
    · rintro ⟨hqcap, hwaiting⟩
      apply Nat.lt_of_not_ge
      intro hfind
      rcases Nat.find_spec h with ⟨_, hne⟩
      exact hne (hwaiting (Nat.find h) hfind)
  · rw [dif_neg h]
    constructor
    · intro hq
      refine ⟨hq, ?_⟩
      intro m hm
      by_contra hwaiting
      exact h ⟨m, lt_of_le_of_lt hm hq, hwaiting⟩
    · exact fun hq => hq.1

/-- Under strict load, a single sufficiently remote finite replay identifies
the predictable capped service-start index with the literal capped count of
isolated passive arrivals before the tagged queue wait. -/
theorem ae_exists_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_queueWaitCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      ∃ cutoff : ℝ, 0 ≤ cutoff ∧ ∀ older : ℝ, cutoff ≤ older → ∀ cap : ℕ,
        stationaryPriorityClassTaggedFutureMarkCappedServiceStart
          meanService i j older cap x =
        stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap x := by
  filter_upwards [
    ae_exists_stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_eq_queueWaitIndicator_all
      arrivalRate meanService harrivalRate hmeanService hstable i j] with x hx
  rcases hx with ⟨cutoff, hcutoff, hx⟩
  refine ⟨cutoff, hcutoff, ?_⟩
  intro older holder cap
  let A : ℕ → Prop := fun m =>
    stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
      meanService i j older m x ≠ 1
  let B : ℕ → Prop := fun m =>
    ¬ stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (m + 1)) <
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
  have hAB : ∀ m : ℕ, A m ↔ B m := by
    intro m
    dsimp [A, B]
    rw [hx older holder m]
    by_cases hm : stationaryPriorityClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
        j.1 (Int.ofNat (m + 1)) <
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)
    · simp
    · simp
  change (if h : ∃ m < cap, A m then Nat.find h else cap) =
    if h : ∃ m < cap, B m then Nat.find h else cap
  by_cases hA : ∃ m < cap, A m
  · have hB : ∃ m < cap, B m := by
      rcases hA with ⟨m, hmcap, hm⟩
      exact ⟨m, hmcap, (hAB m).mp hm⟩
    rw [dif_pos hA, dif_pos hB]
    apply Nat.le_antisymm
    · apply Nat.find_min' hA
      rcases Nat.find_spec hB with ⟨hmcap, hm⟩
      exact ⟨hmcap, (hAB _).mpr hm⟩
    · apply Nat.find_min' hB
      rcases Nat.find_spec hA with ⟨hmcap, hm⟩
      exact ⟨hmcap, (hAB _).mp hm⟩
  · have hB : ¬ ∃ m < cap, B m := by
      intro hB
      rcases hB with ⟨m, hmcap, hm⟩
      exact hA ⟨m, hmcap, (hAB m).mpr hm⟩
    rw [dif_neg hA, dif_neg hB]

/-- Continuation at the first isolated coordinate is measurable from the
external factor alone. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_continuation_zero
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    MeasurableSet[MeasurableSpace.comap (Prod.fst :
      MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) →
      MulticlassPalmFutureMarkExternalCarrier i j) inferInstance]
      {z | 0 < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
        meanService i j older cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j) :=
    {s | 0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
        meanService i j older s = 1}
  have hzero : MeasurableSet
      {s : MulticlassPalmFutureMarkExternalCarrier i j |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
          meanService i j older s = 1} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
        meanService i j older (measurableSet_singleton (1 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : 0 < cap
    · simpa [U, hcap] using hzero
    · simp [U, hcap]
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (0 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
        meanService i j older z.1 = 1) ↔
    0 < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      meanService i j older cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_iff]
  constructor
  · rintro ⟨hcap, hwaiting⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    have hmzero : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    rw [stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_zero]
    exact hwaiting
  · rintro ⟨hcap, hwaiting⟩
    refine ⟨hcap, ?_⟩
    have hobs := hwaiting 0 (Nat.zero_le 0)
    rw [stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_zero] at hobs
    exact hobs

/-- Evaluate a shorter waiting observation after restricting a visible
external-state/IID prefix through coordinate `N`. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1)) :
    MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) → ℝ :=
  fun u => stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older (q.1 + 1)
    (u.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2)) u.2)

/-- Every shorter visible-prefix waiting observation is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1)) :
    Measurable (stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
      meanService i j older N q) := by
  apply (measurable_stationaryPriorityClassTaggedFutureMarkPrefixWaiting
    meanService i j older (q.1 + 1)).comp
  exact measurable_fst.prodMk
    ((AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.measurable_prefixRestriction
      q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))).comp measurable_snd)

/-- Evaluating a visible-prefix waiting observation on an actual stream gives
its literal finite-prefix observation. -/
theorem stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting_apply_stateStreamPrefix
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (N : ℕ)
    (q : Finset.range (N + 1))
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting meanService i j older N q
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
      stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
        meanService i j older (q.1 + 1) z := by
  unfold stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
  change stationaryPriorityClassTaggedFutureMarkPrefixWaiting meanService i j older (q.1 + 1)
      (z.1, AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2)) = _
  have hrestriction :
      AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction
        q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))
          (AppliedModelingLib.Probability.IIDStream.streamPrefix N z.2) =
        AppliedModelingLib.Probability.IIDStream.streamPrefix q.1 z.2 := by
    simpa only [Function.comp_apply] using congrFun
      (AppliedModelingLib.Probability.IIDStream.PrefixStoppingIndex.prefixRestriction_streamPrefix
        (α := ℝ) q.1 N (Nat.le_of_lt_succ (Finset.mem_range.mp q.2))) z.2
  rw [hrestriction]
  rfl

/-- At every positive coordinate, continuation of the capped service-start
index is measurable from the external factor and the preceding IID prefix. -/
theorem measurableSet_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_continuation_succ
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap N : ℕ) :
    MeasurableSet[MeasurableSpace.comap
      (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
        MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N) inferInstance]
      {z | N + 1 < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
        meanService i j older cap z} := by
  let U : Set (MulticlassPalmFutureMarkExternalCarrier i j ×
      (Finset.range (N + 1) → ℝ)) :=
    {u | N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting meanService i j older u.1 = 1 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
          meanService i j older N q u = 1}
  have hzero : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting meanService i j older u.1 = 1} := by
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      ((measurable_stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting
        meanService i j older).comp measurable_fst (measurableSet_singleton (1 : ℝ)))
  have hvisible : MeasurableSet
      {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
            meanService i j older N q u = 1} := by
    rw [show {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
        ∀ q : Finset.range (N + 1),
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
            meanService i j older N q u = 1} =
        ⋂ q : Finset.range (N + 1),
          {u | stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
            meanService i j older N q u = 1} by
      ext u
      simp]
    apply MeasurableSet.iInter
    intro q
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      (measurable_stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
        meanService i j older N q (measurableSet_singleton (1 : ℝ)))
  have hU : MeasurableSet U := by
    by_cases hcap : N + 1 < cap
    · have hUeq : U =
          {u : MulticlassPalmFutureMarkExternalCarrier i j × (Finset.range (N + 1) → ℝ) |
            stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting meanService i j older u.1 = 1} ∩
          {u | ∀ q : Finset.range (N + 1),
            stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting
              meanService i j older N q u = 1} := by
          ext u
          simp [U, hcap]
      rw [hUeq]
      exact hzero.inter hvisible
    · have hUempty : U = ∅ := by
        ext u
        simp [U, hcap]
      rw [hUempty]
      exact MeasurableSet.empty
  refine MeasurableSpace.measurableSet_comap.2 ⟨U, hU, ?_⟩
  ext z
  change (N + 1 < cap ∧
      stationaryPriorityClassTaggedFutureMarkZeroPrefixWaiting meanService i j older z.1 = 1 ∧
      ∀ q : Finset.range (N + 1),
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting meanService i j older N q
          (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
            MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) = 1) ↔
    N + 1 < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      meanService i j older cap z
  rw [lt_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_iff]
  constructor
  · rintro ⟨hcap, hzero, hvisible⟩
    refine ⟨hcap, ?_⟩
    intro m hm
    cases m with
    | zero =>
        rw [stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_zero]
        exact hzero
    | succ m =>
        have hmle : m ≤ N := Nat.succ_le_succ_iff.mp hm
        let q : Finset.range (N + 1) :=
          ⟨m, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hmle)⟩
        have hq := hvisible q
        rw [stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting_apply_stateStreamPrefix
          meanService i j older N q z] at hq
        simpa [q] using hq
  · rintro ⟨hcap, hobs⟩
    refine ⟨hcap, ?_, ?_⟩
    · have hzero := hobs 0 (Nat.zero_le _)
      rw [stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation_zero] at hzero
      exact hzero
    · intro q
      calc
        stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting meanService i j older N q
            (AppliedModelingLib.Probability.IIDStream.stateStreamPrefix (σ :=
              MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) N z) =
            stationaryPriorityClassTaggedFutureMarkWaitingPrefixObservation
              meanService i j older (q.1 + 1) z :=
          stationaryPriorityClassTaggedFutureMarkVisiblePrefixWaiting_apply_stateStreamPrefix
            meanService i j older N q z
        _ = 1 := hobs (q.1 + 1)
          (Nat.succ_le_succ (Nat.lt_succ_iff.mp (Finset.mem_range.mp q.2)))

/-- The bounded service-start index is predictable with respect to the
isolated IID future-mark stream.  Whether a mark is accrued is decided before
that mark is exposed. -/
noncomputable def stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ) :
    AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex
      (σ := MulticlassPalmFutureMarkExternalCarrier i j) (α := ℝ) where
  toFun := stationaryPriorityClassTaggedFutureMarkCappedServiceStart meanService i j older cap
  continuation_zero_measurable :=
    measurableSet_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_continuation_zero
      meanService i j older cap
  continuation_succ_prefix_measurable := fun N =>
    measurableSet_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_continuation_succ
      meanService i j older cap N

/-- The predictable service-start index has the advertised concrete value. -/
theorem stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ) (cap : ℕ)
    (z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :
    stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
      meanService i j older cap z =
      stationaryPriorityClassTaggedFutureMarkCappedServiceStart meanService i j older cap z := rfl

/-- Finite marked-renewal compensation before the bounded service-start
index: expected isolated class work is its mean requirement times the expected
number of arrivals observed while the tag is still waiting. -/
theorem integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ)
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (cap : ℕ) :
    ∫ z,
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
        (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
          meanService i j older cap)
        (fun work : ℝ => meanService j.1 * work) cap z
        ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      (∑ r ∈ Finset.range (cap + 1),
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))).real
          ((stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j older cap).continuationEvent r)) * meanService j.1 := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hmeasurable : Measurable (fun work : ℝ => meanService j.1 * work) :=
    measurable_const.mul measurable_id
  have hintegrable : Integrable (fun work : ℝ => meanService j.1 * work)
      (ProbabilityTheory.expMeasure (1 : ℝ)) := by
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hmean : ∫ work : ℝ, meanService j.1 * work ∂ProbabilityTheory.expMeasure (1 : ℝ) =
      meanService j.1 := by
    rw [MeasureTheory.integral_const_mul,
      AppliedModelingLib.Probability.integral_id_expMeasure (by norm_num)]
    norm_num
  rw [AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_truncatedStrictStoppedReward
    ρ (ProbabilityTheory.expMeasure (1 : ℝ))
    (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
      meanService i j older cap)
    (fun work : ℝ => meanService j.1 * work) hmeasurable hintegrable cap, hmean]

/-- The continuation-tail sum of the bounded predictable service-start index
is its expected accrued isolated-arrival count. -/
theorem integral_coe_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_sum
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older : ℝ)
    (ρ : Measure (MulticlassPalmFutureMarkExternalCarrier i j))
    [IsProbabilityMeasure ρ] (cap : ℕ) :
    ∫ z,
      (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
        meanService i j older cap z : ℝ)
        ∂(ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))) =
      ∑ r ∈ Finset.range (cap + 1),
        (ρ.prod (AppliedModelingLib.Probability.IIDStream.measure
          (ProbabilityTheory.expMeasure (1 : ℝ)))).real
          ((stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j older cap).continuationEvent r) := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  let τ := stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
    meanService i j older cap
  have htruncated :
      (fun z : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) =>
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          τ (fun _ : ℝ => (1 : ℝ)) cap z) =
        fun z => (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
          meanService i j older cap z : ℝ) := by
    funext z
    rw [AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward_const_of_le_cap]
    · simp [τ, stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply]
    · simpa [τ, stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply]
        using stationaryPriorityClassTaggedFutureMarkCappedServiceStart_le_cap
          meanService i j older cap z
  rw [← htruncated]
  rw [AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.integral_truncatedStrictStoppedReward
    ρ (ProbabilityTheory.expMeasure (1 : ℝ))
      τ (fun _ : ℝ => (1 : ℝ)) measurable_const (integrable_const _) cap]
  simp [τ]

/-- Sending the remote-past cutoff to infinity transfers the finite
predictable service-start count to the literal capped number of isolated
arrivals strictly before the stationary tagged queue wait.  The deterministic
cap supplies the integrable domination, so this step uses no unproved
unbounded stopping or tail-summability principle. -/
theorem tendsto_integral_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    Filter.Tendsto (fun older : ℕ =>
      ∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
          meanService i j (older : ℝ) cap z : ℝ)
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      Filter.atTop
      (nhds (∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z : ℝ)
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let F : ℕ → MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun older z =>
      ((stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
        meanService i j (older : ℝ) cap z : ℕ) : ℝ)
  let f : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun z => (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
      meanService i j cap z : ℝ)
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hcast : Measurable (fun q : ℕ => (q : ℝ)) := Measurable.of_discrete
  have hmeasurable : ∀ older, AEStronglyMeasurable (F older) M := by
    intro older
    exact (hcast.comp
      (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
        meanService i j (older : ℝ) cap).measurable).aestronglyMeasurable
  have hbound : ∀ older, ∀ᵐ z ∂M, ‖F older z‖ ≤ (cap : ℝ) := by
    intro older
    filter_upwards with z
    have hnonneg : 0 ≤ F older z := Nat.cast_nonneg _
    rw [Real.norm_of_nonneg hnonneg]
    dsimp [F]
    exact_mod_cast stationaryPriorityClassTaggedFutureMarkCappedServiceStart_le_cap
      meanService i j (older : ℝ) cap z
  have hlimit : ∀ᵐ z ∂M, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [
      ae_exists_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_queueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j] with z hz
    rcases hz with ⟨cutoff, hcutoff, hz⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    dsimp [F, f]
    rw [stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply,
      hz (older : ℝ) (hN.trans (by exact_mod_cast holder)) cap]
  simpa [M, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := M) (F := F) (f := f) (fun _ => (cap : ℝ)) hmeasurable
      (integrable_const _) hbound hlimit)

/-- At a fixed deterministic cap, the literal isolated arrival count before
the tagged queue wait is almost-everywhere strongly measurable. -/
theorem aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    AEStronglyMeasurable (fun z =>
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z : ℝ))
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let F : ℕ → MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun older z =>
      ((stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
        meanService i j (older : ℝ) cap z : ℕ) : ℝ)
  let f : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun z => (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
      meanService i j cap z : ℝ)
  have hcast : Measurable (fun q : ℕ => (q : ℝ)) := Measurable.of_discrete
  have hmeasurable : ∀ older, AEStronglyMeasurable (F older) M := by
    intro older
    exact (hcast.comp
      (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
        meanService i j (older : ℝ) cap).measurable).aestronglyMeasurable
  have hlimit : ∀ᵐ z ∂M, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [
      ae_exists_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_queueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j] with z hz
    rcases hz with ⟨cutoff, hcutoff, hz⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    dsimp [F, f]
    rw [stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply,
      hz (older : ℝ) (hN.trans (by exact_mod_cast holder)) cap]
  simpa [M, f] using
    (aestronglyMeasurable_of_tendsto_ae Filter.atTop hmeasurable hlimit)

/-- At a fixed deterministic cap, the literal isolated arrival count before
the tagged queue wait is integrable. -/
theorem integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    Integrable (fun z =>
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z : ℝ))
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  letI : IsProbabilityMeasure (multiclassPalmFutureMarkExternalMeasure arrivalRate i j) :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  have hmeas : AEStronglyMeasurable (fun z =>
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z : ℝ)) M := by
    simpa [M] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j cap)
  refine Integrable.mono' (integrable_const (cap : ℝ)) hmeas ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount_le_cap
    meanService i j cap z

/-- At a fixed deterministic cap, the literal marked work accumulated before
the tagged queue wait is integrable. -/
theorem integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    Integrable (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
      meanService i j cap)
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let ρ := multiclassPalmFutureMarkExternalMeasure arrivalRate i j
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M := ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  let reward : ℝ → ℝ := fun work => meanService j.1 * work
  letI : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hreward : Integrable reward μ := by
    dsimp [reward, μ]
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hcount : AEMeasurable (fun z =>
      (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z : ℝ)) M := by
    simpa [ρ, μ, M] using
      (aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j cap).aemeasurable
  have hterm : ∀ r : ℕ, Integrable (fun z :
      MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) =>
      if r < stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z then
        reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2) else 0) M := by
    intro r
    let B : Set (MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ)) :=
      {z | r < stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
        meanService i j cap z}
    let g : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
      B.indicator (fun z => reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2))
    have hB : NullMeasurableSet B M := by
      simpa only [B, Nat.cast_lt] using
        (nullMeasurableSet_lt (aemeasurable_const : AEMeasurable
          (fun _ : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) => (r : ℝ)) M)
          hcount)
    have hgmeas : AEStronglyMeasurable g M := by
      exact ((AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.integrable_state_coordinate
        ρ μ reward hreward r).aemeasurable.indicator₀ hB).aestronglyMeasurable
    have hcoord : Integrable (fun z :
        MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) =>
        reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2)) M := by
      simpa [M] using
        (AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.integrable_state_coordinate
          ρ μ reward hreward r)
    have hgint : Integrable g M := by
      refine Integrable.mono' hcoord.norm hgmeas ?_
      filter_upwards with z
      by_cases hz : z ∈ B
      · simp [g, B, hz]
      · simp [g, B, hz]
    refine hgint.congr ?_
    filter_upwards with z
    change B.indicator
        (fun z => reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2)) z = _
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      have hlt : r < stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z := hz
      simp [hlt]
    · rw [Set.indicator_of_notMem hz]
      have hnotlt : ¬ r < stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z := hz
      simp [hnotlt]
  simpa [ρ, μ, M, reward,
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork] using
    (MeasureTheory.integrable_finset_sum (Finset.range (cap + 1)) fun r _ => hterm r)

/-- The literal finite strict-before-wait marked-work sum is almost everywhere
strongly measurable under the factored selected-Palm law. -/
theorem aestronglyMeasurable_stationaryPriorityClassTaggedFutureMarkQueueWaitWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    AEStronglyMeasurable (stationaryPriorityClassTaggedFutureMarkQueueWaitWork
      meanService i j)
      ((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) := by
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  refine aestronglyMeasurable_of_tendsto_ae Filter.atTop
    (f := fun cap => stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
      meanService i j cap) ?_ ?_
  · intro cap
    simpa [M] using
      (integrable_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j cap).aestronglyMeasurable
  · filter_upwards with x
    exact tendsto_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
      meanService i j x

/-- The finite marked-IID compensation terms converge as the remote-past
cutoff tends to infinity to the literal capped work arriving before the
stationary tagged queue wait.  The fixed finite mark prefix supplies an
integrable dominator. -/
theorem tendsto_integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    Filter.Tendsto (fun older : ℕ =>
      ∫ z,
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j (older : ℝ) cap)
          (fun work : ℝ => meanService j.1 * work) cap z
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
      Filter.atTop
      (nhds (∫ z,
        stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
          meanService i j cap z
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))) := by
  let ρ := multiclassPalmFutureMarkExternalMeasure arrivalRate i j
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M := ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  letI : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  let reward : ℝ → ℝ := fun work => meanService j.1 * work
  let F : ℕ → MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun older z =>
      AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
        (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
          meanService i j (older : ℝ) cap)
        reward cap z
  let f : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork meanService i j cap
  let G : MulticlassPalmFutureMarkExternalCarrier i j × (ℕ → ℝ) → ℝ :=
    fun z => ∑ r ∈ Finset.range (cap + 1),
      ‖reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2)‖
  letI : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hreward_measurable : Measurable reward :=
    measurable_const.mul measurable_id
  have hreward_integrable : Integrable reward μ := by
    dsimp [reward, μ]
    exact (AppliedModelingLib.Probability.integrable_id_expMeasure (by norm_num)).const_mul _
  have hmeasurable : ∀ older, AEStronglyMeasurable (F older) M := by
    intro older
    exact (AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.measurable_truncatedStrictStoppedReward
        (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
          meanService i j (older : ℝ) cap)
        reward hreward_measurable cap).aestronglyMeasurable
  have hintegrableG : Integrable G M := by
    dsimp [G]
    apply MeasureTheory.integrable_finset_sum
    intro r _
    exact (AppliedModelingLib.Probability.IIDStream.StatePrefixStoppingIndex.integrable_state_coordinate
      ρ μ reward hreward_integrable r).norm
  have hbound : ∀ older, ∀ᵐ z ∂M, ‖F older z‖ ≤ G z := by
    intro older
    filter_upwards with z
    dsimp [F, G]
    calc
      ‖∑ r ∈ Finset.range (cap + 1),
          if r < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
            meanService i j (older : ℝ) cap z then
              reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2) else 0‖ ≤
          ∑ r ∈ Finset.range (cap + 1),
            ‖if r < stationaryPriorityClassTaggedFutureMarkCappedServiceStart
              meanService i j (older : ℝ) cap z then
                reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2) else 0‖ :=
        norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.range (cap + 1),
          ‖reward (AppliedModelingLib.Probability.IIDStream.coordinate r z.2)‖ := by
        apply Finset.sum_le_sum
        intro r _
        split <;> simp
  have hlimit : ∀ᵐ z ∂M, Filter.Tendsto (fun older : ℕ => F older z)
      Filter.atTop (nhds (f z)) := by
    filter_upwards [
      ae_exists_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_queueWaitCount
        arrivalRate meanService harrivalRate hmeanService hstable i j] with z hz
    rcases hz with ⟨cutoff, hcutoff, hz⟩
    rcases exists_nat_ge cutoff with ⟨N, hN⟩
    apply tendsto_nhds_of_eventually_eq
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro older holder
    dsimp [F, f, reward]
    unfold AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
    rw [stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex_apply,
      hz (older : ℝ) (hN.trans (by exact_mod_cast holder)) cap]
    rfl
  simpa [ρ, μ, M, F, f] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := M) (F := F) (f := f) G hmeasurable hintegrableG hbound hlimit)

/-- At every deterministic arrival-index cap, literal stationary-Palm work
from one isolated passive class before the tagged queue wait has expectation
its mean requirement times the expected literal capped arrival count. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork_eq_mean_mul_count
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) (cap : ℕ) :
    ∫ z, stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
      meanService i j cap z
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      (∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z : ℝ)
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))) *
        meanService j.1 := by
  let ρ := multiclassPalmFutureMarkExternalMeasure arrivalRate i j
  let μ : Measure ℝ := ProbabilityTheory.expMeasure (1 : ℝ)
  let M := ρ.prod (AppliedModelingLib.Probability.IIDStream.measure μ)
  letI : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_multiclassPalmFutureMarkExternalMeasure
      arrivalRate harrivalRate i j
  letI : IsProbabilityMeasure μ :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have hwork :=
    tendsto_integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      arrivalRate meanService harrivalRate hmeanService hstable i j cap
  have hcount :=
    tendsto_integral_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
      arrivalRate meanService harrivalRate hmeanService hstable i j cap
  have hfinite : ∀ older : ℕ,
      (∫ z,
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j (older : ℝ) cap)
          (fun work : ℝ => meanService j.1 * work) cap z ∂M) =
        (∫ z,
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
            meanService i j (older : ℝ) cap z : ℝ) ∂M) * meanService j.1 := by
    intro older
    calc
      (∫ z,
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j (older : ℝ) cap)
          (fun work : ℝ => meanService j.1 * work) cap z ∂M) =
          (∑ r ∈ Finset.range (cap + 1), M.real
            ((stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
              meanService i j (older : ℝ) cap).continuationEvent r)) * meanService j.1 := by
        simpa [ρ, μ, M] using
          (integral_truncatedStrictStoppedReward_stationaryPriorityClassTaggedFutureMarkCappedServiceStart
            meanService i j (older : ℝ) ρ cap)
      _ = (∫ z,
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
            meanService i j (older : ℝ) cap z : ℝ) ∂M) * meanService j.1 := by
        rw [integral_coe_stationaryPriorityClassTaggedFutureMarkCappedServiceStart_eq_sum
          meanService i j (older : ℝ) ρ cap]
  have hleft : Filter.Tendsto (fun older : ℕ =>
      ∫ z,
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j (older : ℝ) cap)
          (fun work : ℝ => meanService j.1 * work) cap z ∂M)
      Filter.atTop
      (nhds (∫ z, stationaryPriorityClassTaggedFutureMarkCappedQueueWaitWork
        meanService i j cap z ∂M)) := by
    simpa [ρ, μ, M] using hwork
  have hright : Filter.Tendsto (fun older : ℕ =>
      (∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedServiceStart
          meanService i j (older : ℝ) cap z : ℝ) ∂M) * meanService j.1)
      Filter.atTop
      (nhds ((∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z : ℝ) ∂M) * meanService j.1)) := by
    simpa [ρ, μ, M] using hcount.mul tendsto_const_nhds
  have hleft' : Filter.Tendsto (fun older : ℕ =>
      ∫ z,
        AppliedModelingLib.Probability.IIDStream.PredictableStatePrefixIndex.truncatedStrictStoppedReward
          (stationaryPriorityClassTaggedFutureMarkCappedServiceStartPredictableIndex
            meanService i j (older : ℝ) cap)
          (fun work : ℝ => meanService j.1 * work) cap z ∂M)
      Filter.atTop
      (nhds ((∫ z,
        (stationaryPriorityClassTaggedFutureMarkCappedQueueWaitCount
          meanService i j cap z : ℝ) ∂M) * meanService j.1)) := by
    apply hright.congr'
    exact Filter.Eventually.of_forall (fun older => (hfinite older).symm)
  simpa [ρ, μ, M] using tendsto_nhds_unique hleft hleft'

end

end AppliedModelingLib.Queueing
