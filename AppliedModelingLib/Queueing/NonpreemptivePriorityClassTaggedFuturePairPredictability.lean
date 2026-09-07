import AppliedModelingLib.Queueing.MulticlassPalmFuturePairPrefix
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedFixedReplayMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityClassTaggedDeterministicTimeLocality
import AppliedModelingLib.Queueing.NonpreemptivePriority

/-!
# Borel delayed-prefix service-start observables

For one isolated passive class, this module defines the Borel finite-replay
service-start observation obtained after retaining a visible IID
arrival-gap/work prefix and delaying the next passive arrival.  The observable
is a generic queueing API; the later endpoint argument identifies it with the
literal service start on the relevant good carrier.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory

noncomputable section

open scoped MeasureTheory

/-- A finite completion lookup is exact when the ledger contains a matching
record and every matching record has the same physical completion epoch. -/
private theorem nonpreemptivePriorityRecordedCompletionTime_eq_some_of_unique_completed
    {n : ℕ}
    (state : NonpreemptivePriorityWorkState n (NonpreemptivePriorityArrivalIndex n))
    (identifier : NonpreemptivePriorityArrivalIndex n) (completionTime : ℝ)
    (hcompleted : ∃ job, job.identifier = identifier ∧
      (job, completionTime) ∈ state.completed)
    (hunique : ∀ job otherCompletionTime, job.identifier = identifier →
      (job, otherCompletionTime) ∈ state.completed → otherCompletionTime = completionTime) :
    nonpreemptivePriorityRecordedCompletionTime state identifier = some completionTime := by
  classical
  unfold nonpreemptivePriorityRecordedCompletionTime
  have hsome : (state.completed.reverse.find?
      fun entry => decide (entry.1.identifier = identifier)).isSome := by
    rw [List.find?_isSome]
    rcases hcompleted with ⟨job, hidentifier, hmember⟩
    refine ⟨(job, completionTime), List.mem_reverse.mpr hmember, ?_⟩
    simp [hidentifier]
  cases hfind : state.completed.reverse.find?
      (fun entry => decide (entry.1.identifier = identifier)) with
  | none => simp [hfind] at hsome
  | some entry =>
      rcases entry with ⟨job, otherCompletionTime⟩
      have hpredicate := List.find?_some hfind
      have hmember := List.mem_reverse.mp (List.mem_of_find?_eq_some hfind)
      have htime : otherCompletionTime = completionTime :=
        hunique job otherCompletionTime (of_decide_eq_true hpredicate) hmember
      simp [htime]

/-- If the selected customer is already in positive service in the strict
causal state at `s`, later arrivals cannot change its finite right-closed
completion epoch.  The endpoint arrivals at `s` are admitted only after that
strict state, so this is the nonpreemptive continuation bridge used by the
delayed-prefix argument. -/
theorem stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_some_of_activeBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (s u residual : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hs : 0 ≤ s) (hsu : s ≤ u) (hresidual : 0 < residual)
    (hactive :
      (stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
        meanService i z s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual))
    (htarget : s + residual ≤ u) :
    stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some (s + residual) := by
  let strictState := stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon
    meanService i z s
  let boundary := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z s
  let after := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
    meanService i z s u
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let completionTime := s + residual
  have hstrictTime : strictState.currentTime = s := by
    simpa [strictState] using
      stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_currentTime_eq
        meanService i z s hs hgood
  have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime strictState := by
    simpa [tag, completionTime, hstrictTime] using
      nonpreemptivePriorityTaggedServiceSchedule_of_active strictState tag residual
        (by simpa [strictState, tag] using hactive) hresidual
  have hstateAtS : stationaryPriorityClassTaggedFinitePostArrivalState meanService i z s =
      runNonpreemptivePriorityArrivalTrace strictState boundary := by
    simpa [strictState, boundary] using
      stationaryPriorityClassTaggedFinitePostArrivalState_eq_run_beforeHorizon_atHorizon
        meanService i z s hs hgood
  have hstateAtU := stationaryPriorityClassTaggedFinitePostArrivalState_eq_advance_run_after
    meanService i z s u hgood hs hsu
  have hfinal : stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace strictState (boundary ++ after))) u
        (runNonpreemptivePriorityArrivalTrace strictState (boundary ++ after)) := by
    rw [hstateAtU, hstateAtS, runNonpreemptivePriorityArrivalTrace_append]
  have hrecordedTail : (tag, completionTime) ∈
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace strictState (boundary ++ after))) u
        (runNonpreemptivePriorityArrivalTrace strictState (boundary ++ after))).completed := by
    exact mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_taggedServiceSchedule
      u completionTime strictState (boundary ++ after) tag
      (by simpa [completionTime] using htarget) hschedule
  have hrecorded : (tag, completionTime) ∈
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u).completed := by
    rw [hfinal]
    exact hrecordedTail
  unfold stationaryPriorityClassTaggedFinitePostArrivalResponseTime
  apply nonpreemptivePriorityRecordedCompletionTime_eq_some_of_unique_completed
  · refine ⟨tag, ?_, hrecorded⟩
    simp [tag, stationaryPriorityClassTaggedJob]
  · intro job otherCompletionTime hidentifier hmember
    have hjob : job = tag := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finitePostArrivalState_of_identifier_eq
        meanService i z u job hgood
      · exact Or.inr (Or.inr ⟨otherCompletionTime, hmember⟩)
      · simpa [tag, stationaryPriorityClassTaggedJob] using hidentifier
    subst job
    apply completedAt_eq_of_mem_completed_of_jobMultiplicity_le_one
      (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u) tag
      otherCompletionTime completionTime
    · rw [show nonpreemptivePriorityWorkStateJobMultiplicity
          (stationaryPriorityClassTaggedFinitePostArrivalState meanService i z u) tag = 1 by
          simpa [tag] using
            nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFinitePostArrivalState
              meanService i z u hgood]
    · exact hmember
    · exact hrecorded

/-- The same active-service continuation statement for a two-sided finite
replay whose remote-past window has coalesced with the causal state. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_some_of_activeBeforeHorizon
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older s u residual : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i z (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i z))
    (hs : 0 ≤ s) (hsu : s ≤ u) (hresidual : 0 < residual)
    (hactive :
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual))
    (htarget : s + residual ≤ u) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime meanService i z older u =
      some (s + residual) := by
  have hstrict : stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older s =
      stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon meanService i z s := by
    exact stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_liveEquivalent
      meanService i z older s hequivalent
  have hcausal : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i z u =
      some (s + residual) := by
    apply stationaryPriorityClassTaggedFinitePostArrivalResponseTime_eq_some_of_activeBeforeHorizon
      meanService i z s u residual hgood hs hsu hresidual
    · simpa [hstrict] using hactive
    · exact htarget
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_liveEquivalent
    meanService i z older u hequivalent, hcausal]

/-- A two-sided strict replay can be continued by first admitting the boundary
arrivals at `s` and then the later right-closed ledger. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_advance_run_beforeHorizon_after
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older s u : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (holder : 0 ≤ older) (hs : 0 ≤ s) (hsu : s ≤ u) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older u =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
              meanService i z older s)
            (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z s ++
              canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u))) u
        (runNonpreemptivePriorityArrivalTrace
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
            meanService i z older s)
          (canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon meanService i z s ++
            canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter meanService i z s u)) := by
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let initial := admitNonpreemptivePriorityJob
    (clearNonpreemptivePriorityCompletionLedger preArrival)
    (stationaryPriorityClassTaggedJob meanService i z)
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z s
  let afterFront := runNonpreemptivePriorityArrivalTrace initial front
  let boundary := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z s
  let after := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
    meanService i z s u
  let tail := boundary ++ after
  have hinitialTime : initial.currentTime = 0 := by
    dsimp [initial]
    rw [admitNonpreemptivePriorityJob_currentTime]
    simpa [preArrival] using
      canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
        meanService i z (-older) 0 (neg_nonpos.mpr holder) hgood
  have hafterFrontTime : afterFront.currentTime ≤ s := by
    dsimp [afterFront, initial, front]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [hinitialTime]
      exact hs
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z s job hjob).le
  have htailTime : ∀ job ∈ tail, s ≤ job.arrivalTime := by
    intro job hjob
    rcases List.mem_append.mp (by simpa [tail] using hjob) with hboundary | hafter
    · exact (arrivalTime_eq_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
        meanService i z s hgood job (by simpa [boundary] using hboundary)).symm.le
    · exact (horizon_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
        meanService i z s u hgood job (by simpa [after] using hafter)).le
  have hcut := advance_runNonpreemptivePriorityArrivalTrace_cut
    afterFront tail s u hafterFrontTime hsu htailTime
  have hsplit : canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z u =
      front ++ tail := by
    calc
      canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z u =
          canonicalStationaryPriorityClassTaggedFutureArrivalJobs meanService i z s ++ after := by
            simpa [after] using
              canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_after
                meanService i z s u hgood hs hsu
      _ = (front ++ boundary) ++ after := by
            rw [canonicalStationaryPriorityClassTaggedFutureArrivalJobs_append_atHorizon
              meanService i z s hgood]
      _ = front ++ tail := by simp [tail, List.append_assoc]
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalState
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  dsimp only
  rw [hsplit, runNonpreemptivePriorityArrivalTrace_append]
  simpa [preArrival, initial, front, afterFront, boundary, after, tail] using hcut

/-- A strict two-sided finite replay reaches its queried physical horizon. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_currentTime_eq
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older s : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (holder : 0 ≤ older) (hs : 0 ≤ s) :
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older s).currentTime = s := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
  dsimp only
  let preArrival := canonicalStationaryPriorityClassTaggedFiniteWindowState
    meanService i z (-older) 0
  let initial := admitNonpreemptivePriorityJob
    (clearNonpreemptivePriorityCompletionLedger preArrival)
    (stationaryPriorityClassTaggedJob meanService i z)
  let front := canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
    meanService i z s
  have hinitialTime : initial.currentTime = 0 := by
    dsimp [initial]
    rw [admitNonpreemptivePriorityJob_currentTime]
    simpa [preArrival] using
      canonicalStationaryPriorityClassTaggedFiniteWindowState_currentTime_eq_right
        meanService i z (-older) 0 (neg_nonpos.mpr holder) hgood
  apply advanceNonpreemptivePriorityWorkState_currentTime_eq_target
  · apply runNonpreemptivePriorityArrivalTrace_currentTime_le
    · rw [hinitialTime]
      exact hs
    · intro job hjob
      exact (arrivalTime_lt_canonicalStationaryPriorityClassTaggedFutureArrivalJobsBeforeHorizon
        meanService i z s job (by simpa [front] using hjob)).le
  · exact le_rfl

/-- In a two-sided finite replay, a selected job already in positive service
at the strict clock completes at its scheduled epoch despite endpoint and
later arrivals.  Unlike the causal variant, this uses only the finite replay
itself and hence also applies to delayed-prefix representatives. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_some_of_activeBeforeHorizon_direct
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (z : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i)
    (older s u residual : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath z.1.1)
    (holder : 0 ≤ older) (hs : 0 ≤ s) (hsu : s ≤ u) (hresidual : 0 < residual)
    (hactive :
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual))
    (htarget : s + residual ≤ u) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime meanService i z older u =
      some (s + residual) := by
  let strictState := stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
    meanService i z older s
  let boundary := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAtHorizon
    meanService i z s
  let after := canonicalStationaryPriorityClassTaggedFutureArrivalJobsAfter
    meanService i z s u
  let tail := boundary ++ after
  let tag := stationaryPriorityClassTaggedJob meanService i z
  let completionTime := s + residual
  have hstrictTime : strictState.currentTime = s := by
    simpa [strictState] using
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_currentTime_eq
        meanService i z older s hgood holder hs
  have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime strictState := by
    simpa [tag, completionTime, hstrictTime] using
      nonpreemptivePriorityTaggedServiceSchedule_of_active strictState tag residual
        (by simpa [strictState, tag] using hactive) hresidual
  have hfinal : stationaryPriorityClassTaggedFiniteReplayPostArrivalState
      meanService i z older u =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace strictState tail)) u
        (runNonpreemptivePriorityArrivalTrace strictState tail) := by
    simpa [strictState, boundary, after, tail] using
      stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_advance_run_beforeHorizon_after
        meanService i z older s u hgood holder hs hsu
  have hrecordedTail : (tag, completionTime) ∈
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace strictState tail)) u
        (runNonpreemptivePriorityArrivalTrace strictState tail)).completed := by
    exact mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_taggedServiceSchedule
      u completionTime strictState tail tag (by simpa [completionTime] using htarget) hschedule
  have hrecorded : (tag, completionTime) ∈
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older u).completed := by
    rw [hfinal]
    exact hrecordedTail
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
  apply nonpreemptivePriorityRecordedCompletionTime_eq_some_of_unique_completed
  · refine ⟨tag, ?_, hrecorded⟩
    simp [tag, stationaryPriorityClassTaggedJob]
  · intro job otherCompletionTime hidentifier hmember
    have hjob : job = tag := by
      apply eq_stationaryPriorityClassTaggedJob_of_contains_finiteReplayPostArrivalState_of_identifier_eq
        meanService i z older u job hgood
      · exact Or.inr (Or.inr ⟨otherCompletionTime, hmember⟩)
      · simpa [tag, stationaryPriorityClassTaggedJob] using hidentifier
    subst job
    apply completedAt_eq_of_mem_completed_of_jobMultiplicity_le_one
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older u) tag
      otherCompletionTime completionTime
    · rw [show nonpreemptivePriorityWorkStateJobMultiplicity
          (stationaryPriorityClassTaggedFiniteReplayPostArrivalState meanService i z older u) tag = 1 by
          simpa [tag] using
            nonpreemptivePriorityWorkStateJobMultiplicity_stationaryPriorityClassTaggedFiniteReplayPostArrivalState
              meanService i z older u hgood]
    · exact hmember
    · exact hrecorded

/-- Reconstruct the full tagged input after retaining a finite prefix of one
passive class's future pair stream and delaying its next unseen arrival. -/
noncomputable def stationaryPriorityClassTaggedFuturePairDelayedSample
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ) (insertedGap : ℝ) :
    MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i :=
  multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    arrivalRate harrivalRate i j
    (multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, ((fun r : Finset.range N => x.2 r), insertedGap)))

/-- The finite-replay completion observation after retaining `N` visible
passive arrival-gap/work coordinates and inserting the specified next gap. -/
noncomputable def stationaryPriorityClassTaggedFuturePairDelayedCompletion
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older horizon insertedGap : ℝ) (N : ℕ) :
    MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) → ℝ :=
  fun x =>
    let z := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j
      (multiclassPalmFuturePairPrefixDelayedRepresentative i j N
        (x.1, (x.2, insertedGap)))
    (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i z older horizon).getD 0

/-- The delayed finite-replay completion observation is Borel in the external
factor and visible marked-renewal prefix. -/
theorem measurable_stationaryPriorityClassTaggedFuturePairDelayedCompletion
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older horizon insertedGap : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFuturePairDelayedCompletion
      arrivalRate meanService harrivalRate i j older horizon insertedGap N) := by
  let representative :
      MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) →
        MulticlassPalmFutureFactorCarrier i j :=
    fun x => multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, (x.2, insertedGap))
  have hrepresentative : Measurable representative := by
    apply measurable_multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      |>.comp
    exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hinput : Measurable (fun x :
      MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) =>
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j (representative x)) :=
    (measurable_multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j).comp hrepresentative
  exact (measurable_stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_getD
    meanService i older horizon).comp hinput

/-- The Borel service-start candidate induced by a delayed passive prefix.
When the finite replay has recorded the tag's completion by `horizon`, this
is that completion time minus the selected customer's declared service work. -/
noncomputable def stationaryPriorityClassTaggedFuturePairDelayedServiceStart
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older horizon insertedGap : ℝ) (N : ℕ) :
    MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) → ℝ :=
  fun x =>
    let factors := multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, (x.2, insertedGap))
    let z := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j factors
    stationaryPriorityClassTaggedFuturePairDelayedCompletion
      arrivalRate meanService harrivalRate i j older horizon insertedGap N x -
      stationaryPriorityClassTaggedWorkRequirement meanService i z

/-- The delayed-prefix service-start candidate is Borel. -/
theorem measurable_stationaryPriorityClassTaggedFuturePairDelayedServiceStart
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (older horizon insertedGap : ℝ) (N : ℕ) :
    Measurable (stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j older horizon insertedGap N) := by
  let representative :
      MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) →
        MulticlassPalmFutureFactorCarrier i j :=
    fun x => multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, (x.2, insertedGap))
  let input :
      MulticlassPalmFutureExternalCarrier i j × (Finset.range N → ℝ × ℝ) →
        MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i :=
    multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j ∘ representative
  have hrepresentative : Measurable representative := by
    apply measurable_multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      |>.comp
    exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have hinput : Measurable input :=
    (measurable_multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j).comp hrepresentative
  exact (measurable_stationaryPriorityClassTaggedFuturePairDelayedCompletion
    arrivalRate meanService harrivalRate i j older horizon insertedGap N).sub
      ((measurable_stationaryPriorityClassTaggedWorkRequirement meanService i).comp hinput)

/-- Under any product law for the external queueing data and one passive
IID arrival-gap/work stream, the next delayed-prefix arrival epoch cannot
equal the Borel delayed service-start observation.  The statement is indexed
by the number of visible earlier pairs, so `N = 0` includes the first passive
future arrival. -/
theorem measure_futureArrivalTime_eq_stationaryPriorityClassTaggedFuturePairDelayedServiceStart_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (ρ : Measure (MulticlassPalmFutureExternalCarrier i j))
    [IsProbabilityMeasure ρ]
    (older horizon insertedGap : ℝ) (N : ℕ) :
    (ρ.prod (Probability.IIDStream.measure
      ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
        (ProbabilityTheory.expMeasure (1 : ℝ)))))
      {x | Probability.PoissonProcess.arrivalTime N (fun r => (x.2 r).1) =
        stationaryPriorityClassTaggedFuturePairDelayedServiceStart
          arrivalRate meanService harrivalRate i j older horizon insertedGap N
          (x.1, fun r => x.2 r)} = 0 := by
  exact Probability.Queueing.measure_futureArrivalTime_eq_prefixFunction_zero
    ρ (harrivalRate j.1) N
    (stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j older horizon insertedGap N)
    (measurable_stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j older horizon insertedGap N)

/-- The preceding atomless delayed-prefix comparison transports through the
concrete selected-Palm future-factor map.  It is stated directly on the
selected-Palm input carrier so later queue arguments can bound their endpoint
event by this null set without treating the literal queue wait as Borel. -/
theorem measure_multiclassStationaryPoissonWorkClassTaggedFutureFactor_arrivalTime_eq_delayedServiceStart_zero
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (older horizon insertedGap : ℝ) (N : ℕ) :
    (Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
      {z | Probability.PoissonProcess.arrivalTime N
          (fun r => ((multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z).2 r).1) =
        stationaryPriorityClassTaggedFuturePairDelayedServiceStart
          arrivalRate meanService harrivalRate i j older horizon insertedGap N
          ((multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z).1,
            fun r => (multiclassStationaryPoissonWorkClassTaggedFutureFactor i j z).2 r)} = 0 := by
  letI : DecidableEq (Fin n) := Classical.decEq _
  let ρ : Measure (MulticlassPalmFutureExternalCarrier i j) :=
    ((Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)).prod
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ))).prod
      ((Measure.pi fun k : passiveClassComplement i j =>
        Probability.Queueing.stationaryPoissonWorkMeasure (arrivalRate k.1.1)).prod
        (((Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)).prod
          (ProbabilityTheory.expMeasure (1 : ℝ))).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))))
  let F := multiclassStationaryPoissonWorkClassTaggedFutureFactor i j
  let E : Set (MulticlassPalmFutureFactorCarrier i j) :=
    {x | Probability.PoissonProcess.arrivalTime N (fun r => (x.2 r).1) =
      stationaryPriorityClassTaggedFuturePairDelayedServiceStart
        arrivalRate meanService harrivalRate i j older horizon insertedGap N
        (x.1, fun r => x.2 r)}
  letI : ∀ k : passiveClassComplement i j,
      IsProbabilityMeasure (Probability.Queueing.stationaryPoissonWorkMeasure
        (arrivalRate k.1.1)) := by
    intro k
    exact Probability.Queueing.isProbabilityMeasure_stationaryPoissonWorkMeasure
      (harrivalRate k.1.1)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (arrivalRate i)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure
      (harrivalRate i)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.twoSidedInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_twoSidedInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (arrivalRate j.1)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (harrivalRate j.1)
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure (1 : ℝ)) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (arrivalRate j.1)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure
      (harrivalRate j.1)
  letI : IsProbabilityMeasure
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)) :=
    Probability.PoissonProcess.isProbabilityMeasure_exponentialInterarrivalMeasure (by norm_num)
  letI : IsProbabilityMeasure ρ := by
    dsimp [ρ]
    infer_instance
  have hzero : (ρ.prod (Probability.IIDStream.measure
      ((ProbabilityTheory.expMeasure (arrivalRate j.1)).prod
        (ProbabilityTheory.expMeasure (1 : ℝ))))) E = 0 := by
    simpa [E] using
      measure_futureArrivalTime_eq_stationaryPriorityClassTaggedFuturePairDelayedServiceStart_zero
        arrivalRate meanService harrivalRate i j ρ older horizon insertedGap N
  have hpreimage :
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
        (F ⁻¹' E) = 0 := by
    apply (multiclassStationaryPoissonWorkClassTaggedFutureFactor_measurePreserving
      arrivalRate harrivalRate i j).quasiMeasurePreserving.preimage_null
    simpa [ρ] using hzero
  simpa [F, E, Set.preimage, ρ] using hpreimage

/-- When a delayed-prefix replay has the same strict state at a service-start
clock as the original replay, its Borel completion-minus-work observation is
that clock.  The selected job is retained in the external factor, so its full
service requirement is unchanged by the delayed passive renewal tail. -/
theorem stationaryPriorityClassTaggedFuturePairDelayedServiceStart_apply_eq_of_active
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older s horizon residual : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap).1.1)
    (holder : 0 ≤ older) (hs : 0 ≤ s) (horizon_ge : s ≤ horizon)
    (hresidual : 0 < residual)
    (hstate : stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older s =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older s)
    (hactive :
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) older s).active =
        some (stationaryPriorityClassTaggedJob meanService i
          (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
            arrivalRate harrivalRate i j x), residual))
    (hresidual_eq : residual = stationaryPriorityClassTaggedWorkRequirement meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x))
    (htarget : s + residual ≤ horizon) :
    stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j older horizon insertedGap N
      (x.1, fun r : Finset.range N => x.2 r) = s := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    arrivalRate harrivalRate i j x
  let w := stationaryPriorityClassTaggedFuturePairDelayedSample
    arrivalRate harrivalRate i j x N insertedGap
  let y : MulticlassPalmFutureFactorCarrier i j :=
    multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, ((fun r : Finset.range N => x.2 r), insertedGap))
  have hy : w = multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j y := by
    rfl
  have htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w := by
    have hfst : x.1 = y.1 := by rfl
    have hselected : z.1 = w.1 := by
      simpa [z, hy] using
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
        arrivalRate harrivalRate i j x y hfst
    have harrival : stationaryPriorityClassTaggedArrival i z i 0 =
        stationaryPriorityClassTaggedArrival i w i 0 := by
      simp only [stationaryPriorityClassTaggedArrival,
        multiclassStationaryPoissonWorkClassTaggedArrival, dif_pos]
      exact congrArg (fun path : ℤ → ℝ =>
        Probability.PoissonProcess.candidatePalmArrival path 0)
        (congrArg Prod.fst hselected)
    have hwork : stationaryPriorityClassTaggedWorkRequirementAt meanService i z i 0 =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w i 0 := by
      simp only [stationaryPriorityClassTaggedWorkRequirementAt,
        multiclassStationaryPoissonWorkClassTaggedRequirementAt, dif_pos]
      exact congrArg (fun path : ℤ → ℝ => meanService i * path 0)
        (congrArg Prod.snd hselected)
    unfold stationaryPriorityClassTaggedJob
    rw [harrival, hwork]
  have hactivew :
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i w older s).active =
        some (stationaryPriorityClassTaggedJob meanService i w, residual) := by
    rw [← hstate, ← htag]
    simpa [z] using hactive
  have hresponse : stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i w older horizon = some (s + residual) := by
    exact stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_some_of_activeBeforeHorizon_direct
      meanService i w older s horizon residual hgood holder hs horizon_ge hresidual hactivew htarget
  have hwork : stationaryPriorityClassTaggedWorkRequirement meanService i w = residual := by
    calc
      stationaryPriorityClassTaggedWorkRequirement meanService i w =
          (stationaryPriorityClassTaggedJob meanService i w).serviceWork := by
            symm
            exact stationaryPriorityClassTaggedJob_serviceWork meanService i w
      _ = (stationaryPriorityClassTaggedJob meanService i z).serviceWork := by rw [← htag]
      _ = stationaryPriorityClassTaggedWorkRequirement meanService i z := by
            exact stationaryPriorityClassTaggedJob_serviceWork meanService i z
      _ = residual := hresidual_eq.symm
  change (stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime
      meanService i w older horizon).getD 0 -
      stationaryPriorityClassTaggedWorkRequirement meanService i w = s
  rw [hresponse, hwork]
  simp only [Option.getD_some]
  linarith

/-- The delayed-prefix Borel service-start observation also agrees with the
literal finite causal service start once the original two-sided replay has
coalesced with its causal past.  This packages the service-start timing fact
and the direct delayed replay continuation into the form used by the endpoint
no-tie comparison. -/
theorem stationaryPriorityClassTaggedFuturePairDelayedServiceStart_apply_eq_of_response_sub_service
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older s horizon completedAt : ℝ)
    (hgood : Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x).1.1)
    (hdelayedGood : Probability.PoissonProcess.suspensionGoodGapPath
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap).1.1)
    (hpositive : ∀ k m,
      0 < stationaryPriorityClassTaggedWorkRequirementAt meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) k m)
    (holder : 0 ≤ older) (hs : 0 ≤ s) (horizon_ge : s ≤ horizon)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState
      (canonicalStationaryPriorityClassTaggedFiniteWindowState meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) (-older) 0)
      (stationaryPriorityClassTaggedRemotePastState meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x)))
    (hstate : stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older s =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older s)
    (hstart : s = completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x))
    (hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) horizon = some completedAt) :
    stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j older horizon insertedGap N
      (x.1, fun r : Finset.range N => x.2 r) = s := by
  let z := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    arrivalRate harrivalRate i j x
  obtain ⟨residual, hresidualEq, hactive⟩ :=
    exists_active_stationaryPriorityClassTaggedFinitePostArrivalStateBeforeHorizon_of_response_sub_service
      meanService i z s horizon completedAt hgood hpositive hs horizon_ge
      (by simpa [z] using hstart) (by simpa [z] using hresponse)
  have hactiveReplay :
      (stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i z older s).active =
        some (stationaryPriorityClassTaggedJob meanService i z, residual) := by
    rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_liveEquivalent
      meanService i z older s (by simpa [z] using hequivalent)]
    exact hactive
  have hresidualPos : 0 < residual := by
    rw [hresidualEq]
    simpa [stationaryPriorityClassTaggedWorkRequirement_eq_fullCoordinate] using hpositive i 0
  have hcompletedLeHorizon : completedAt ≤ horizon := by
    exact stationaryPriorityClassTaggedFinitePostArrivalResponseTime_le_horizon_of_eq_some
      meanService i z horizon completedAt hgood hpositive (hs.trans horizon_ge)
        (by simpa [z] using hresponse)
  have htarget : s + residual ≤ horizon := by
    rw [hresidualEq]
    linarith
  exact stationaryPriorityClassTaggedFuturePairDelayedServiceStart_apply_eq_of_active
    arrivalRate meanService harrivalRate i j x N insertedGap older s horizon residual
    hdelayedGood holder hs horizon_ge hresidualPos
    (by simpa [z] using hstate)
    (by simpa [z] using hactiveReplay)
    (by simpa [z] using hresidualEq)
    htarget

/-- A strict finite tagged replay state is unchanged by delaying the next
unseen passive arrival when every isolated positive label that either replay
places before the deterministic horizon lies in the retained pair prefix. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_bound
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older t : ℝ) (ht : 0 ≤ t) (hgap : 0 < insertedGap)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hbound : ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) j.1 (Int.ofNat (r + 1)) < t ∨
        multiclassStationaryPoissonWorkClassTaggedArrival i
          (stationaryPriorityClassTaggedFuturePairDelayedSample
            arrivalRate harrivalRate i j x N insertedGap)
          j.1 (Int.ofNat (r + 1)) < t → r < N) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older t := by
  let y : MulticlassPalmFutureFactorCarrier i j :=
    multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, ((fun r : Finset.range N => x.2 r), insertedGap))
  let z := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    arrivalRate harrivalRate i j x
  let w := multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
    arrivalRate harrivalRate i j y
  have hfst : x.1 = y.1 := by
    rfl
  have hgoody : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ y.2).1, y.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
    simpa [y] using
      (multiclassPalmFuturePairPrefixDelayedRepresentative_mem_good
        i j x N insertedGap hgood hgap)
  have hgoodw : Probability.PoissonProcess.suspensionGoodGapPath w.1.1 := by
    have hselectedEq :=
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
        arrivalRate harrivalRate i j x y hfst
    change Probability.PoissonProcess.suspensionGoodGapPath
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j y).1.1
    rw [← hselectedEq]
    exact hselected
  have htag : stationaryPriorityClassTaggedJob meanService i z =
      stationaryPriorityClassTaggedJob meanService i w := by
    unfold stationaryPriorityClassTaggedJob stationaryPriorityClassTaggedArrival
      stationaryPriorityClassTaggedWorkRequirementAt
    rw [multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_ne
      arrivalRate harrivalRate i j x y i 0 (Ne.symm j.property) hfst,
      multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_ne
        arrivalRate harrivalRate i j x y i 0 (Ne.symm j.property) hfst]
  have harrival : ∀ (k : Fin n) (m : ℤ),
      multiclassStationaryPoissonWorkClassTaggedArrival i z k m < t ∨
        multiclassStationaryPoissonWorkClassTaggedArrival i w k m < t →
      multiclassStationaryPoissonWorkClassTaggedArrival i z k m =
        multiclassStationaryPoissonWorkClassTaggedArrival i w k m := by
    intro k m hbefore
    by_cases hkj : k = j.1
    · subst k
      cases m with
      | ofNat q =>
          cases q with
          | zero =>
              exact multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_nonpositive
                arrivalRate harrivalRate i j x y 0 hfst hgood hgoody (by norm_num)
          | succ r =>
              have hr : r < N := by
                simpa [z, w, y, stationaryPriorityClassTaggedFuturePairDelayedSample] using
                  hbound r hbefore
              apply multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_pairPrefix
                arrivalRate harrivalRate i j x y r ?_ hgood hgoody
              intro s hs
              exact (multiclassPalmFuturePairPrefixDelayedRepresentative_apply_eq_of_lt
                i j x N insertedGap s (lt_of_le_of_lt hs hr)).symm
      | negSucc r =>
          exact multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_nonpositive
            arrivalRate harrivalRate i j x y (Int.negSucc r) hfst hgood hgoody (by omega)
    · exact multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_eq_of_fst_eq_of_ne
        arrivalRate harrivalRate i j x y k m hkj hfst
  have hrequirement : ∀ (k : Fin n) (m : ℤ),
      multiclassStationaryPoissonWorkClassTaggedArrival i z k m < t ∨
        multiclassStationaryPoissonWorkClassTaggedArrival i w k m < t →
      stationaryPriorityClassTaggedWorkRequirementAt meanService i z k m =
        stationaryPriorityClassTaggedWorkRequirementAt meanService i w k m := by
    intro k m hbefore
    by_cases hkj : k = j.1
    · subst k
      cases m with
      | ofNat q =>
          cases q with
          | zero =>
              exact congrArg (fun a => meanService j.1 * a)
                (multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_nonpositive
                  arrivalRate harrivalRate i j x y 0 hfst (by norm_num))
          | succ r =>
              have hr : r < N := by
                simpa [z, w, y, stationaryPriorityClassTaggedFuturePairDelayedSample] using
                  hbound r hbefore
              rw [show stationaryPriorityClassTaggedWorkRequirementAt meanService i z
                    j.1 (Int.ofNat (r + 1)) = meanService j.1 * (x.2 r).2 by
                    exact congrArg (fun a => meanService j.1 * a)
                      (multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_ofNat_succ
                        arrivalRate harrivalRate i j x r),
                  show stationaryPriorityClassTaggedWorkRequirementAt meanService i w
                    j.1 (Int.ofNat (r + 1)) = meanService j.1 * (y.2 r).2 by
                    exact congrArg (fun a => meanService j.1 * a)
                      (multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_ofNat_succ
                        arrivalRate harrivalRate i j y r)]
              rw [multiclassPalmFuturePairPrefixDelayedRepresentative_apply_eq_of_lt
                i j x N insertedGap r hr]
      | negSucc r =>
          exact congrArg (fun a => meanService j.1 * a)
            (multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_nonpositive
              arrivalRate harrivalRate i j x y (Int.negSucc r) hfst (by omega))
    · exact congrArg (fun a => meanService k * a)
        (multiclassStationaryPoissonWorkClassTaggedRequirement_fromFutureFactors_eq_of_fst_eq_of_ne
          arrivalRate harrivalRate i j x y k m hkj hfst)
  change stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i z older t =
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i w older t
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon_eq_of_arrival_requirement_eq_of_lt
    meanService i z w older t ht hselected hgoodw htag harrival hrequirement

/-- The selected completion observation is unchanged under the same
delayed-prefix finite-state locality hypotheses. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_futurePairPrefixDelayed_of_bound
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older t : ℝ) (ht : 0 ≤ t) (hgap : 0 < insertedGap)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (hbound : ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) j.1 (Int.ofNat (r + 1)) < t ∨
        multiclassStationaryPoissonWorkClassTaggedArrival i
          (stationaryPriorityClassTaggedFuturePairDelayedSample
            arrivalRate harrivalRate i j x N insertedGap)
          j.1 (Int.ofNat (r + 1)) < t → r < N) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older t := by
  unfold stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
  rw [stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_bound
    arrivalRate meanService harrivalRate i j x N insertedGap older t ht hgap hselected hgood hbound]

/-- It is enough to bound the original pre-clock isolated labels and place
the delayed representative's first unseen label after the clock: strict
stationary arrival order then supplies the two-replay bound required by the
finite locality theorem. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_original_bound_of_next_gt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older t : ℝ) (ht : 0 ≤ t) (hgap : 0 < insertedGap)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (horiginalBound : ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) j.1 (Int.ofNat (r + 1)) < t → r < N)
    (hnext : t < multiclassStationaryPoissonWorkClassTaggedArrival i
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (N + 1))) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older t := by
  apply stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_bound
    arrivalRate meanService harrivalRate i j x N insertedGap older t ht hgap hselected hgood
  intro r hbefore
  rcases hbefore with horiginal | hdelayed
  · exact horiginalBound r horiginal
  · by_contra hr
    have hNr : N ≤ r := Nat.le_of_not_gt hr
    have hlabel : (Int.ofNat (N + 1) : ℤ) ≤ Int.ofNat (r + 1) := by
      exact Int.ofNat_le.mpr (Nat.succ_le_succ hNr)
    have hmonotone :=
      (strictMono_stationaryPriorityClassTaggedArrival_of_ne i j.1 j.property
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap)).monotone hlabel
    change multiclassStationaryPoissonWorkClassTaggedArrival i
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (N + 1)) ≤
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (r + 1)) at hmonotone
    linarith

/-- It is enough to bound the original pre-clock isolated labels and place
the delayed representative's first unseen label after the clock: strict
stationary arrival order then supplies the two-replay bound required by the
finite locality theorem. -/
theorem stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_futurePairPrefixDelayed_of_original_bound_of_next_gt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ)
    (insertedGap older t : ℝ) (ht : 0 ≤ t) (hgap : 0 < insertedGap)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1})
    (horiginalBound : ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) j.1 (Int.ofNat (r + 1)) < t → r < N)
    (hnext : t < multiclassStationaryPoissonWorkClassTaggedArrival i
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (N + 1))) :
    stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) older t := by
  apply stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_futurePairPrefixDelayed_of_bound
    arrivalRate meanService harrivalRate i j x N insertedGap older t ht hgap hselected hgood
  intro r hbefore
  rcases hbefore with horiginal | hdelayed
  · exact horiginalBound r horiginal
  · by_contra hr
    have hNr : N ≤ r := Nat.le_of_not_gt hr
    have hlabel : (Int.ofNat (N + 1) : ℤ) ≤ Int.ofNat (r + 1) := by
      exact Int.ofNat_le.mpr (Nat.succ_le_succ hNr)
    have hmonotone :=
      (strictMono_stationaryPriorityClassTaggedArrival_of_ne i j.1 j.property
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap)).monotone hlabel
    change multiclassStationaryPoissonWorkClassTaggedArrival i
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (N + 1)) ≤
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N insertedGap) j.1 (Int.ofNat (r + 1)) at hmonotone
    linarith

/-- For every deterministic clock, one can choose a positive integer inserted
gap whose delayed full-factor reconstruction places the next unseen isolated
passive arrival strictly after that clock. -/
theorem exists_nat_stationaryPriorityClassTaggedFuturePairDelayedSample_arrival_gt
    {n : ℕ} (arrivalRate : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j) (N : ℕ) (t : ℝ)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    ∃ M : ℕ, 0 < (M : ℝ) ∧
      t < multiclassStationaryPoissonWorkClassTaggedArrival i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N (M : ℝ)) j.1 (Int.ofNat (N + 1)) := by
  obtain ⟨M, hM, htime⟩ :=
    exists_nat_futurePairPrefixDelayed_arrivalTime_gt N
      (fun r : Finset.range N => x.2 r) t
  refine ⟨M, hM, ?_⟩
  let y : MulticlassPalmFutureFactorCarrier i j :=
    multiclassPalmFuturePairPrefixDelayedRepresentative i j N
      (x.1, ((fun r : Finset.range N => x.2 r), (M : ℝ)))
  have hgoody : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ y.2).1, y.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
    simpa [y] using
      (multiclassPalmFuturePairPrefixDelayedRepresentative_mem_good
        i j x N (M : ℝ) hgood hM)
  change t < multiclassStationaryPoissonWorkClassTaggedArrival i
    (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j y) j.1 (Int.ofNat (N + 1))
  rw [multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
    arrivalRate harrivalRate i j y N hgoody]
  simpa [y] using htime

/-- At every deterministic nonnegative clock, a good full pair factor has a
finite delayed-prefix representative with the same strict finite tagged
completion observation. -/
theorem exists_stationaryPriorityClassTaggedFuturePairDelayedSample_response_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j)
    (older t : ℝ) (ht : 0 ≤ t)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    ∃ N M : ℕ, 0 < (M : ℝ) ∧
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTimeBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N (M : ℝ)) older t := by
  obtain ⟨N, hbound⟩ :=
    exists_multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_prefix_bound
      arrivalRate harrivalRate i j x t hgood
  obtain ⟨M, hM, hnext⟩ :=
    exists_nat_stationaryPriorityClassTaggedFuturePairDelayedSample_arrival_gt
      arrivalRate harrivalRate i j x N t hgood
  refine ⟨N, M, hM, ?_⟩
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalResponseTime_eq_of_futurePairPrefixDelayed_of_original_bound_of_next_gt
    arrivalRate meanService harrivalRate i j x N (M : ℝ) older t ht hM hselected hgood
    hbound hnext

/-- At every deterministic nonnegative clock, a good full pair factor has a
finite delayed-prefix representative with the same strict finite replay
state. -/
theorem exists_stationaryPriorityClassTaggedFuturePairDelayedSample_state_eq
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureFactorCarrier i j)
    (older t : ℝ) (ht : 0 ≤ t)
    (hselected : Probability.PoissonProcess.suspensionGoodGapPath x.1.1.1)
    (hgood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1, x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1}) :
    ∃ N M : ℕ, 0 < (M : ℝ) ∧
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) older t =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N (M : ℝ)) older t := by
  obtain ⟨N, hbound⟩ :=
    exists_multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_prefix_bound
      arrivalRate harrivalRate i j x t hgood
  obtain ⟨M, hM, hnext⟩ :=
    exists_nat_stationaryPriorityClassTaggedFuturePairDelayedSample_arrival_gt
      arrivalRate harrivalRate i j x N t hgood
  refine ⟨N, M, hM, ?_⟩
  exact stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_original_bound_of_next_gt
    arrivalRate meanService harrivalRate i j x N (M : ℝ) older t ht hM hselected hgood
    hbound hnext

/-- Under the selected-Palm law, no positive labelled arrival from an
isolated passive class occurs exactly at the tagged customer's service-start
clock.  The proof does not require the literal queue wait to be Borel: a
hypothetical tie is covered by a countable family of Borel delayed-prefix
service-start graphs, each null by the fresh atomless arrival gap. -/
theorem ae_forall_stationaryPriorityClassTaggedPassiveFutureArrival_ne_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ N : ℕ,
        multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
          (Int.ofNat (N + 1)) ≠
          stationaryPriorityClassTaggedQueueWait meanService i z := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let F := multiclassStationaryPoissonWorkClassTaggedFutureFactor i j
  let E : ℕ → ℕ → ℕ → ℕ →
      Set (MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i) :=
    fun N M older horizon =>
      {z | Probability.PoissonProcess.arrivalTime N (fun r => (F z).2 r |>.1) =
        stationaryPriorityClassTaggedFuturePairDelayedServiceStart
          arrivalRate meanService harrivalRate i j (older : ℝ) (horizon : ℝ) (M : ℝ) N
          ((F z).1, fun r : Finset.range N => (F z).2 r)}
  have hE : ∀ N M older horizon, P (E N M older horizon) = 0 := by
    intro N M older horizon
    simpa [P, E, F] using
      (measure_multiclassStationaryPoissonWorkClassTaggedFutureFactor_arrivalTime_eq_delayedServiceStart_zero
        arrivalRate meanService harrivalRate i j (older : ℝ) (horizon : ℝ) (M : ℝ) N)
  have hnull : P (⋃ N, ⋃ M, ⋃ older, ⋃ horizon, E N M older horizon) = 0 := by
    apply measure_iUnion_null
    intro N
    apply measure_iUnion_null
    intro M
    apply measure_iUnion_null
    intro older
    exact measure_iUnion_null (fun horizon => hE N M older horizon)
  have hnot : ∀ᵐ z ∂P,
      z ∉ ⋃ N, ⋃ M, ⋃ older, ⋃ horizon, E N M older horizon := by
    simpa only [Set.mem_compl_iff] using (compl_mem_ae_iff.2 hnull)
  filter_upwards [hnot,
    ae_multiclassStationaryPoissonWorkClassTaggedGapPath_good
      arrivalRate harrivalRate i,
    ae_all_stationaryPriorityClassTaggedWorkRequirementAt_positive
      arrivalRate meanService harrivalRate hmeanService i,
    ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_exists_stationaryPriorityClassTaggedRemotePastState_liveCoalescence
      arrivalRate meanService harrivalRate hmeanService hstable i,
    ae_exists_stationaryPriorityClassTaggedResponseTime_eq_completionEpoch
      arrivalRate meanService harrivalRate hmeanService hstable i] with
      z hznot hselected hpositive hwait hcoalescence hcompletion
  intro N htie
  let x := F z
  have hfactor : multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
      arrivalRate harrivalRate i j x = z := by
    simpa [x, F] using
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_apply_factors
        arrivalRate harrivalRate i j z)
  have hfactorArrival : ∀ r : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j x) j.1 (Int.ofNat (r + 1)) =
        multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
          (Int.ofNat (r + 1)) := by
    intro r
    exact congrArg (fun w : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i =>
      multiclassStationaryPoissonWorkClassTaggedArrival i w j.1 (Int.ofNat (r + 1))) hfactor
  have hpairGood : Probability.PoissonProcess.equilibriumToSuspension
      ((MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ℕ x.2).1,
        x.1.2.2.1.1) ∈
        {p : (ℤ → ℝ) × ℝ |
          p ∈ Probability.PoissonProcess.suspensionCarrier ∧
            Probability.PoissonProcess.suspensionGoodGapPath p.1} := by
    simpa [x, F] using
      (multiclassStationaryPoissonWorkClassTaggedFutureFactor_mem_good i j z)
  rcases hcoalescence with ⟨cutoff, _, hcoalescence⟩
  rcases hcompletion with ⟨_, completedAt, _, hresponse, hresponseTail⟩
  rcases Filter.eventually_atTop.1 hresponseTail with ⟨responseCutoff, hresponseTail⟩
  let older : ℕ := Nat.ceil cutoff
  let horizon : ℕ := Nat.ceil (max responseCutoff
    (stationaryPriorityClassTaggedQueueWait meanService i z))
  have holder : cutoff ≤ (older : ℝ) := by
    dsimp [older]
    exact Nat.le_ceil cutoff
  have hresponseCutoff : responseCutoff ≤ (horizon : ℝ) := by
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hs : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z := hwait
  have hshorizon : stationaryPriorityClassTaggedQueueWait meanService i z ≤ (horizon : ℝ) := by
    exact le_trans (le_max_right _ _) (Nat.le_ceil _)
  have hfiniteResponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z (horizon : ℝ) = some completedAt :=
    hresponseTail (horizon : ℝ) hresponseCutoff
  have hstart : stationaryPriorityClassTaggedQueueWait meanService i z =
      completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    rw [stationaryPriorityClassTaggedQueueWait, hresponse]
  have horiginalBound : ∀ r,
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
        (Int.ofNat (r + 1)) < stationaryPriorityClassTaggedQueueWait meanService i z →
      r < N := by
    intro r hr
    by_contra hrnot
    have hNr : N ≤ r := Nat.le_of_not_gt hrnot
    have hlabel : (Int.ofNat (N + 1) : ℤ) ≤ Int.ofNat (r + 1) := by
      exact Int.ofNat_le.mpr (Nat.succ_le_succ hNr)
    have hmono :=
      (strictMono_stationaryPriorityClassTaggedArrival_of_ne i j.1 j.property z).monotone hlabel
    have htie' : stationaryPriorityClassTaggedArrival i z j.1
        (Int.ofNat (N + 1)) = stationaryPriorityClassTaggedQueueWait meanService i z := by
      simpa [stationaryPriorityClassTaggedArrival] using htie
    change multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
      (Int.ofNat (N + 1)) ≤
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
        (Int.ofNat (r + 1)) at hmono
    linarith
  obtain ⟨M, hMpos, hnext⟩ :=
    exists_nat_stationaryPriorityClassTaggedFuturePairDelayedSample_arrival_gt
      arrivalRate harrivalRate i j x N
      (stationaryPriorityClassTaggedQueueWait meanService i z) hpairGood
  have hstate : stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
      meanService i
      (multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
        arrivalRate harrivalRate i j x) (older : ℝ)
        (stationaryPriorityClassTaggedQueueWait meanService i z) =
      stationaryPriorityClassTaggedFiniteReplayPostArrivalStateBeforeHorizon
        meanService i
        (stationaryPriorityClassTaggedFuturePairDelayedSample
          arrivalRate harrivalRate i j x N (M : ℝ)) (older : ℝ)
        (stationaryPriorityClassTaggedQueueWait meanService i z) := by
    exact stationaryPriorityClassTaggedFiniteReplayPostArrivalState_eq_of_futurePairPrefixDelayed_of_original_bound_of_next_gt
      arrivalRate meanService harrivalRate i j x N (M : ℝ) (older : ℝ)
      (stationaryPriorityClassTaggedQueueWait meanService i z) hs hMpos
      (by simpa [x, F, multiclassStationaryPoissonWorkClassTaggedFutureFactor] using hselected)
      hpairGood
      (by
        intro r hr
        apply horiginalBound r
        rw [← hfactorArrival r]
        exact hr)
      hnext
  have hdelayedSelectedGood : Probability.PoissonProcess.suspensionGoodGapPath
      (stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N (M : ℝ)).1.1 := by
    let y : MulticlassPalmFutureFactorCarrier i j :=
      multiclassPalmFuturePairPrefixDelayedRepresentative i j N
        (x.1, ((fun r : Finset.range N => x.2 r), (M : ℝ)))
    have hy : stationaryPriorityClassTaggedFuturePairDelayedSample
        arrivalRate harrivalRate i j x N (M : ℝ) =
        multiclassStationaryPoissonWorkClassTaggedFromFutureFactors
          arrivalRate harrivalRate i j y := by
      rfl
    have hselectedEq :=
      multiclassStationaryPoissonWorkClassTaggedFromFutureFactors_selected_eq_of_fst_eq
        arrivalRate harrivalRate i j x y (by rfl)
    rw [hy, ← hselectedEq]
    simpa [hfactor] using hselected
  have hcandidate : stationaryPriorityClassTaggedFuturePairDelayedServiceStart
      arrivalRate meanService harrivalRate i j (older : ℝ) (horizon : ℝ) (M : ℝ) N
      (x.1, fun r : Finset.range N => x.2 r) =
      stationaryPriorityClassTaggedQueueWait meanService i z := by
    apply stationaryPriorityClassTaggedFuturePairDelayedServiceStart_apply_eq_of_response_sub_service
      arrivalRate meanService harrivalRate i j x N (M : ℝ) (older : ℝ)
      (stationaryPriorityClassTaggedQueueWait meanService i z) (horizon : ℝ) completedAt
    · simpa [hfactor] using hselected
    · exact hdelayedSelectedGood
    · simpa [hfactor] using hpositive
    · exact Nat.cast_nonneg older
    · exact hs
    · exact hshorizon
    · simpa [hfactor] using hcoalescence (older : ℝ) holder
    · exact hstate
    · simpa [hfactor] using hstart
    · simpa [hfactor] using hfiniteResponse
  apply hznot
  refine Set.mem_iUnion.2 ⟨N, ?_⟩
  refine Set.mem_iUnion.2 ⟨M, ?_⟩
  refine Set.mem_iUnion.2 ⟨older, ?_⟩
  refine Set.mem_iUnion.2 ⟨horizon, ?_⟩
  change Probability.PoissonProcess.arrivalTime N (fun r => (x.2 r).1) = _
  rw [← multiclassStationaryPoissonWorkClassTaggedArrival_fromFutureFactors_ofNat_succ
    arrivalRate harrivalRate i j x N hpairGood, hfactor, htie]
  exact hcandidate.symm

/-- The strict stopped-arrival index equals the physical right-closed
passive ledger cardinality whenever no passive arrival lies on the tagged
service-start boundary. -/
theorem stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rightClosedCard_of_forall_ne
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i})
    (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x))
    (hnoTie : ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
        (Int.ofNat (N + 1)) ≠
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)) :
    stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x =
      (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x))
        (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1).card := by
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let q := stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x
  let L := Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
    (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1
  have hle : q ≤ L.card := by
    simpa [q, L, z] using
      stationaryPriorityClassTaggedFutureMarkQueueWaitCount_le_rightClosedCard
        meanService i j x
  apply Nat.le_antisymm hle
  apply Nat.le_of_not_gt
  intro hlt
  have hLcard : L.card = Probability.PoissonProcess.suspensionBaseFutureCount
      (z.2 j).1 (stationaryPriorityClassTaggedQueueWait meanService i z) := by
    dsimp [L]
    exact Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
      (z.2 j).1 _ (by simpa [z] using hwait)
  have hqfuture : q < Probability.PoissonProcess.suspensionBaseFutureCount
      (z.2 j).1 (stationaryPriorityClassTaggedQueueWait meanService i z) := by
    rw [← hLcard]
    exact hlt
  have hL : L = (Finset.range
      (Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1
        (stationaryPriorityClassTaggedQueueWait meanService i z))).image
        (fun r => Int.ofNat (r + 1)) := by
    dsimp [L]
    exact Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_eq_futureCanonicalIndices
      (z.2 j).1 _ (by simpa [z] using hwait)
  have hqmem : Int.ofNat (q + 1) ∈ L := by
    rw [hL]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr hqfuture, rfl⟩
  have hqle : multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
      (Int.ofNat (q + 1)) ≤ stationaryPriorityClassTaggedQueueWait meanService i z := by
    have hmem := (Probability.PoissonProcess.mem_suspensionBaseArrivalIndicesRightClosed_iff
      0 (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1
      (Int.ofNat (q + 1))).mp hqmem
    simpa [stationaryPriorityClassTaggedArrival,
      multiclassStationaryPoissonWorkClassTaggedArrival, dif_neg j.2] using hmem.2
  have hqnot : ¬ multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
      (Int.ofNat (q + 1)) < stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [q, z, stationaryPriorityClassTaggedFutureMarkQueueWaitCount,
      stationaryPriorityClassTaggedArrival] using
      (Nat.find_spec (exists_stationaryPriorityClassTaggedFutureMarkArrival_not_lt_queueWait
        meanService i j x))
  have hqgt : stationaryPriorityClassTaggedQueueWait meanService i z <
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
        (Int.ofNat (q + 1)) :=
    lt_of_le_of_ne (not_lt.mp hqnot) (Ne.symm (by simpa [z] using hnoTie q))
  linarith

/-- On a no-simultaneous-arrival path, the factored strict stopped marked-work
sum is exactly the physical right-closed future-work ledger of the isolated
passive class. -/
theorem stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_futureAggregate_of_forall_ne
    {n : ℕ} (meanService : Fin n → ℝ) (i : Fin n)
    (j : {k : Fin n // k ≠ i}) (x : MulticlassPalmFutureMarkFactorCarrier i j)
    (hwait : 0 ≤ stationaryPriorityClassTaggedQueueWait meanService i
      ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x))
    (hnoTie : ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
        (Int.ofNat (N + 1)) ≠
        stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)) :
    stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x =
      stationaryPriorityTaggedFutureWorkAggregate meanService i
        ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
        (stationaryPriorityClassTaggedQueueWait meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)) := by
  classical
  let z := (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x
  let q := stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x
  let c := Probability.PoissonProcess.suspensionBaseFutureCount (z.2 j).1
    (stationaryPriorityClassTaggedQueueWait meanService i z)
  let f : ℕ → ℤ := fun r => Int.ofNat (r + 1)
  have hqcard : q = (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1).card := by
    simpa [q, z] using
      stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rightClosedCard_of_forall_ne
        meanService i j x (by simpa [z] using hwait) (by simpa [z] using hnoTie)
  have hcard : (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1).card = c := by
    dsimp [c]
    exact Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_card_eq_futureCount
      (z.2 j).1 _ (by simpa [z] using hwait)
  have hqc : q = c := hqcard.trans hcard
  have hledger : Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
      (stationaryPriorityClassTaggedQueueWait meanService i z) (z.2 j).1 =
      (Finset.range c).image f := by
    dsimp [c, f]
    exact Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed_zero_eq_futureCanonicalIndices
      (z.2 j).1 _ (by simpa [z] using hwait)
  rw [stationaryPriorityTaggedFutureWorkAggregate_of_ne meanService i j.1 j.2]
  unfold stationaryPriorityClassTaggedFutureMarkQueueWaitWork
  rw [show stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x = q by rfl,
    hqc]
  change (∑ r ∈ Finset.range c, meanService j.1 * x.2 r) =
    meanService j.1 *
      Probability.Queueing.stationaryPoissonWorkFutureAggregate (z.2 j)
        (stationaryPriorityClassTaggedQueueWait meanService i z)
  rw [Probability.Queueing.stationaryPoissonWorkFutureAggregate, hledger]
  dsimp [z]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [Probability.Queueing.stationaryPoissonWorkRequirement,
      multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_symm_futureMark]
  · intro a _ b _ hab
    exact Nat.add_right_cancel (Int.ofNat.inj hab)

/-- The factorized strict stopped marked-work sum agrees almost surely with
the physical future-work ledger of the isolated passive class. -/
theorem ae_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_futureAggregate
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x =
        stationaryPriorityTaggedFutureWorkAggregate meanService i
          ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x) j.1
          (stationaryPriorityClassTaggedQueueWait meanService i
            ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x)) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  have hback : MeasurePreserving e.symm M P := by
    exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j).symm e
  have hsource : ∀ᵐ z ∂P, ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
        (Int.ofNat (N + 1)) ≠ stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [P] using
      ae_forall_stationaryPriorityClassTaggedPassiveFutureArrival_ne_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j
  rw [← hback.map_eq] at hsource
  have hsource' : ∀ᵐ x ∂M, ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i (e.symm x) j.1
        (Int.ofNat (N + 1)) ≠ stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) := by
    exact ae_of_ae_map hback.measurable.aemeasurable hsource
  have hwaitSource : ∀ᵐ z ∂P,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [P] using
      (ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)
  rw [← hback.map_eq] at hwaitSource
  have hwait' : ∀ᵐ x ∂M,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) := by
    exact ae_of_ae_map hback.measurable.aemeasurable hwaitSource
  filter_upwards [hsource', hwait'] with x hnoTie hwait
  exact stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_futureAggregate_of_forall_ne
    meanService i j x hwait hnoTie

/-- The predictable strict stopped-arrival index and the physical
right-closed passive ledger have the same value almost surely. -/
theorem ae_stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rightClosedCard
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∀ᵐ x ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
      (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))),
      stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x =
        (Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
          (stationaryPriorityClassTaggedQueueWait meanService i
            ((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x))
          (((multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j).symm x).2 j).1).card := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  have hback : MeasurePreserving e.symm M P := by
    exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j).symm e
  have hsource : ∀ᵐ z ∂P, ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i z j.1
        (Int.ofNat (N + 1)) ≠ stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [P] using
      ae_forall_stationaryPriorityClassTaggedPassiveFutureArrival_ne_queueWait
        arrivalRate meanService harrivalRate hmeanService hstable i j
  rw [← hback.map_eq] at hsource
  have hsource' : ∀ᵐ x ∂M, ∀ N : ℕ,
      multiclassStationaryPoissonWorkClassTaggedArrival i (e.symm x) j.1
        (Int.ofNat (N + 1)) ≠ stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) := by
    exact ae_of_ae_map hback.measurable.aemeasurable hsource
  have hwaitSource : ∀ᵐ z ∂P,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [P] using
      (ae_nonneg_stationaryPriorityClassTaggedQueueWait
        arrivalRate meanService harrivalRate hmeanService hstable i)
  rw [← hback.map_eq] at hwaitSource
  have hwait' : ∀ᵐ x ∂M,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) := by
    exact ae_of_ae_map hback.measurable.aemeasurable hwaitSource
  filter_upwards [hsource', hwait'] with x hnoTie hwait
  exact stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rightClosedCard_of_forall_ne
    meanService i j x hwait hnoTie

/-- The expected predictable strict stopped-arrival count is the passive
arrival rate times the expected tagged queue wait.  The no-simultaneous-
arrival endpoint comparison transports the physical right-closed count law to
the stopped-index representation used by marked IID compensation. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rate_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      arrivalRate j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  have hback : MeasurePreserving e.symm M P := by
    exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j).symm e
  have hstrict : (fun x =>
      (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)) =ᵐ[M]
      fun x => ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i (e.symm x))
        ((e.symm x).2 j).1).card : ℝ) := by
    filter_upwards [ae_stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rightClosedCard
      arrivalRate meanService harrivalRate hmeanService hstable i j] with x hx
    exact_mod_cast hx
  have hwait : ∀ᵐ z ∂P,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i z := by
    simpa [P] using ae_nonneg_stationaryPriorityClassTaggedQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  rw [← hback.map_eq] at hwait
  have hwait' : ∀ᵐ x ∂M,
      0 ≤ stationaryPriorityClassTaggedQueueWait meanService i (e.symm x) := by
    exact ae_of_ae_map hback.measurable.aemeasurable hwait
  have hphysical : (fun x =>
      ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
        (stationaryPriorityClassTaggedQueueWait meanService i (e.symm x))
        ((e.symm x).2 j).1).card : ℝ)) =ᵐ[M]
      fun x => (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
        meanService i (e.symm x) j : ℝ) := by
    filter_upwards [hwait'] with x hx
    exact congrArg (fun q : ℕ => (q : ℝ))
      (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_card
        meanService i (e.symm x) j hx).symm
  calc
    ∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ) ∂M =
        ∫ x, ((Probability.PoissonProcess.suspensionBaseArrivalIndicesRightClosed 0
          (stationaryPriorityClassTaggedQueueWait meanService i (e.symm x))
          ((e.symm x).2 j).1).card : ℝ) ∂M := integral_congr_ae hstrict
    _ = ∫ x, (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
          meanService i (e.symm x) j : ℝ) ∂M := integral_congr_ae hphysical
    _ = ∫ z, (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
          meanService i z j : ℝ) ∂P := by
      simpa [Function.comp_def] using hback.hasLaw.integral_comp
        (f := fun z => (stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
          meanService i z j : ℝ))
        (integrable_stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait
          arrivalRate meanService harrivalRate hmeanService hstable i j).aestronglyMeasurable
    _ = arrivalRate j.1 * (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P) := by
      simpa [P] using
        integral_stationaryPriorityClassTaggedPassiveFutureCountThroughQueueWait_eq_rate_mul_integral
          arrivalRate meanService harrivalRate hmeanService hstable i j

/-- The expected marked work of one passive class admitted before the tagged
service start is its traffic intensity times the expected tagged queue wait. -/
theorem integral_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_rate_mul_mean_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ x, stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x
      ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
        (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
      arrivalRate j.1 * meanService j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  calc
    ∫ x, stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x
        ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
          (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))) =
        (∫ x, (stationaryPriorityClassTaggedFutureMarkQueueWaitCount meanService i j x : ℝ)
          ∂((multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
            (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ)))) * meanService j.1 :=
      integral_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_mean_mul_count
        arrivalRate meanService harrivalRate hmeanService hstable i j
    _ = (arrivalRate j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag)) * meanService j.1 := by
      rw [integral_stationaryPriorityClassTaggedFutureMarkQueueWaitCount_eq_rate_mul_integral
        arrivalRate meanService harrivalRate hmeanService hstable i j]
    _ = arrivalRate j.1 * meanService j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by ring

/-- The physical future-work ledger of one passive class through the tagged
queue wait has expectation equal to that class's traffic intensity times the
expected tagged queue wait. -/
theorem integral_stationaryPriorityTaggedFutureWorkAggregate_at_queueWait_eq_rate_mul_mean_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j.1
      (stationaryPriorityClassTaggedQueueWait meanService i z)
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      arrivalRate j.1 * meanService j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  have hback : MeasurePreserving e.symm M P := by
    exact (multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j).symm e
  calc
    ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j.1
        (stationaryPriorityClassTaggedQueueWait meanService i z) ∂P =
        ∫ x, stationaryPriorityTaggedFutureWorkAggregate meanService i (e.symm x) j.1
          (stationaryPriorityClassTaggedQueueWait meanService i (e.symm x)) ∂M := by
      symm
      simpa [Function.comp_def] using hback.hasLaw.integral_comp
        (f := fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j.1
          (stationaryPriorityClassTaggedQueueWait meanService i z))
        (aemeasurable_stationaryPriorityTaggedFutureWorkAggregate_of_ne_at_queueWait
          arrivalRate meanService harrivalRate hmeanService hstable i j.1 j.2).aestronglyMeasurable
    _ = ∫ x, stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j x ∂M := by
      apply integral_congr_ae
      filter_upwards [ae_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_futureAggregate
        arrivalRate meanService harrivalRate hmeanService hstable i j] with x hx
      exact hx.symm
    _ = arrivalRate j.1 * meanService j.1 *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P) := by
      simpa [P] using
        integral_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_rate_mul_mean_mul_integral
          arrivalRate meanService harrivalRate hmeanService hstable i j

/-- The physical future-work ledger of a passive class is integrable at the
tagged queue wait. -/
theorem integrable_stationaryPriorityTaggedFutureWorkAggregate_at_queueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) (j : {k : Fin n // k ≠ i}) :
    Integrable (fun z => stationaryPriorityTaggedFutureWorkAggregate meanService i z j.1
      (stationaryPriorityClassTaggedQueueWait meanService i z))
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let M := (multiclassPalmFutureMarkExternalMeasure arrivalRate i j).prod
    (Probability.PoissonProcess.exponentialInterarrivalMeasure (1 : ℝ))
  let e := multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv i j
  let g : MulticlassPalmFutureMarkFactorCarrier i j → ℝ :=
    stationaryPriorityClassTaggedFutureMarkQueueWaitWork meanService i j
  let f : MulticlassStationaryPoissonWorkClassTaggedSample (Fin n) i → ℝ := fun z =>
    stationaryPriorityTaggedFutureWorkAggregate meanService i z j.1
      (stationaryPriorityClassTaggedQueueWait meanService i z)
  have hforward : MeasurePreserving e P M := by
    exact multiclassStationaryPoissonWorkClassTaggedFutureMarkEquiv_measurePreserving_product
      arrivalRate harrivalRate i j
  have hg : Integrable g M := by
    simpa [g, M] using
      integrable_stationaryPriorityClassTaggedFutureMarkQueueWaitWork
        arrivalRate meanService harrivalRate hmeanService hstable i j
  have hcomp : Integrable (fun z => g (e z)) P := by
    simpa [Function.comp_def] using hforward.integrable_comp_of_integrable hg
  have heqM : (fun x => g x) =ᵐ[M] fun x => f (e.symm x) := by
    simpa [g, f, M, e] using
      ae_stationaryPriorityClassTaggedFutureMarkQueueWaitWork_eq_futureAggregate
        arrivalRate meanService harrivalRate hmeanService hstable i j
  rw [← hforward.map_eq] at heqM
  have heqP : (fun z => g (e z)) =ᵐ[P] f := by
    filter_upwards [ae_of_ae_map hforward.measurable.aemeasurable heqM] with z hz
    simpa [e] using hz
  exact hcomp.congr heqP

/-- The aggregate future work of all strictly higher-priority classes through
the tagged queue wait has expectation equal to strict priority load times the
expected tagged queue wait. -/
theorem integral_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait_eq_strictLoad_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      finitePriorityStrictLoad meanService arrivalRate i *
        (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  let W := ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P
  unfold stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
  rw [MeasureTheory.integral_finset_sum]
  · calc
      ∑ j ∈ Finset.univ.filter (fun j => j < i),
          ∫ z, stationaryPriorityTaggedFutureWorkAggregate meanService i z j
            (stationaryPriorityClassTaggedQueueWait meanService i z) ∂P =
          ∑ j ∈ Finset.univ.filter (fun j => j < i), arrivalRate j * meanService j * W := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := ne_of_lt (Finset.mem_filter.mp hj).2
        simpa [P, W] using
          integral_stationaryPriorityTaggedFutureWorkAggregate_at_queueWait_eq_rate_mul_mean_mul_integral
            arrivalRate meanService harrivalRate hmeanService hstable i ⟨j, hji⟩
      _ = finitePriorityStrictLoad meanService arrivalRate i * W := by
        rw [← Finset.sum_mul]
        simp only [finitePriorityStrictLoad, Finset.sum_filter]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j < i
        · simp [hji]
          ring
        · simp [hji]
  · intro j hj
    exact integrable_stationaryPriorityTaggedFutureWorkAggregate_at_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
      ⟨j, ne_of_lt (Finset.mem_filter.mp hj).2⟩

/-- Almost surely, the selected customer's literal queue wait equals the
pre-arrival active residual plus already-waiting urgent work and the stopped
strictly-higher-priority future-work aggregate.  The passive arrival endpoint
is harmless because the atomless no-tie theorem above rules out an arrival of
a strictly higher-priority class exactly at service start. -/
theorem ae_stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictFutureWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (hstable : ∑ j, arrivalRate j * meanService j < 1)
    (i : Fin n) :
    ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      stationaryPriorityClassTaggedQueueWait meanService i z =
        stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z := by
  have hnoTie : ∀ᵐ z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
      (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
      (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag,
      ∀ (j : {k : Fin n // k ≠ i}) (N : ℕ),
        multiclassStationaryPoissonWorkClassTaggedArrival i z j.1 (Int.ofNat (N + 1)) ≠
          stationaryPriorityClassTaggedQueueWait meanService i z := by
    rw [ae_all_iff]
    intro j
    exact ae_forall_stationaryPriorityClassTaggedPassiveFutureArrival_ne_queueWait
      arrivalRate meanService harrivalRate hmeanService hstable i j
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
      arrivalRate meanService harrivalRate hmeanService hstable i,
    hnoTie] with z hgood hpositive hcutoff hwait hcompletion hnoTie
  rcases hcompletion with ⟨_, completedAt, _, hresponseTime, hresponseTail⟩
  rcases Filter.eventually_atTop.1 hresponseTail with ⟨responseCutoff, hresponseTail⟩
  let u := max (stationaryPriorityClassTaggedQueueWait meanService i z) responseCutoff
  have hwait_le_u : stationaryPriorityClassTaggedQueueWait meanService i z ≤ u :=
    le_max_left _ _
  have hresponse : stationaryPriorityClassTaggedFinitePostArrivalResponseTime
      meanService i z u = some completedAt := by
    exact hresponseTail u (le_max_right _ _)
  have hstart : stationaryPriorityClassTaggedQueueWait meanService i z =
      completedAt - stationaryPriorityClassTaggedWorkRequirement meanService i z := by
    simp [stationaryPriorityClassTaggedQueueWait, hresponseTime]
  exact stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictFutureWork_of_response
    meanService i z u completedAt hgood hpositive hcutoff hwait hwait_le_u hstart hresponse hnoTie

/-- The finite aggregate of strictly higher-priority future work through the
selected queue-wait endpoint is integrable under strict total load. -/
theorem integrable_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    Integrable (stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i)
      (Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  unfold stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
  apply integrable_finset_sum
  intro j hj
  exact integrable_stationaryPriorityTaggedFutureWorkAggregate_at_queueWait
    arrivalRate meanService harrivalRate hmeanService hstable i
    ⟨j, ne_of_lt (Finset.mem_filter.mp hj).2⟩

/-- Integrating the literal tagged-service ledger yields the selected-Palm
mean-work identity.  The active-residual and urgent-waiting terms are left as
literal stationary-state expectations; their separate occupation calculation
is the remaining bridge to the closed finite priority formula. -/
theorem integral_stationaryPriorityClassTaggedQueueWait_eq_preArrivalTerms_add_strictLoad_mul_integral
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
      ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
        (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
        (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag =
      (∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) +
        (∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
          meanService i z ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) +
          finitePriorityStrictLoad meanService arrivalRate i *
            (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z
              ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
                (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
                (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) := by
  let P := (Probability.Palm.targetPassiveTaggedArrivalAtZero
    (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
    (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag
  have hactive : Integrable (stationaryPriorityClassTaggedPreArrivalActiveResidualWork
      meanService i) P := by
    simpa [P] using
      integrable_stationaryPriorityClassTaggedPreArrivalActiveResidualWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i
  have hwaiting : Integrable (stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
      meanService i) P := by
    simpa [P] using
      integrable_stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork_of_totalStable
        arrivalRate meanService harrivalRate hmeanService hstable i
  have hstrict : Integrable (stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
      meanService i) P := by
    simpa [P] using integrable_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i
  calc
    ∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P =
        ∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
          stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
            stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
      apply integral_congr_ae
      simpa [P] using ae_stationaryPriorityClassTaggedQueueWait_eq_preArrival_add_strictFutureWork
        arrivalRate meanService harrivalRate hmeanService hstable i
    _ = (∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂P) +
          (∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z ∂P) +
            ∫ z, stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
      calc
        ∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
            stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z +
              stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P =
            ∫ z, (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z +
              stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z) +
                stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
          apply integral_congr_ae
          filter_upwards with z
          ring
        _ = (∫ z, (stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i +
              stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i) z ∂P) +
                ∫ z, stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
          simpa only [Pi.add_apply] using integral_add (hactive.add hwaiting) hstrict
        _ = ((∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂P) +
              ∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
                meanService i z ∂P) +
                ∫ z, stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
          congr 2
          simpa only [Pi.add_apply] using integral_add hactive hwaiting
        _ = (∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂P) +
              (∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork
                meanService i z ∂P) +
                ∫ z, stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait meanService i z ∂P := by
          ring
    _ = (∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z ∂P) +
          (∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z ∂P) +
            finitePriorityStrictLoad meanService arrivalRate i *
              (∫ z, stationaryPriorityClassTaggedQueueWait meanService i z ∂P) := by
      rw [integral_stationaryPriorityClassTaggedStrictFutureWorkAtQueueWait_eq_strictLoad_mul_integral
        arrivalRate meanService harrivalRate hmeanService hstable i]

/-- The integrated tagged-service ledger in strict-priority-slack form. -/
theorem finitePriorityStrictSlack_mul_integral_stationaryPriorityClassTaggedQueueWait_eq_preArrivalTerms
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
      (∫ z, stationaryPriorityClassTaggedPreArrivalActiveResidualWork meanService i z
        ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
          (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
          (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag) +
        ∫ z, stationaryPriorityClassTaggedPreArrivalAtLeastAsUrgentWaitingWork meanService i z
          ∂(Probability.Palm.targetPassiveTaggedArrivalAtZero
            (Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero (harrivalRate i))
            (multiclassStationaryPoissonWorkRestLaw arrivalRate harrivalRate i)).Ptag := by
  have hledger :=
    integral_stationaryPriorityClassTaggedQueueWait_eq_preArrivalTerms_add_strictLoad_mul_integral
      arrivalRate meanService harrivalRate hmeanService hstable i
  unfold finitePriorityStrictSlack
  linarith

end

end AppliedModelingLib.Queueing
