import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionTimes

/-!
# Tagged completion-time lower bounds for nonpreemptive-priority traces

This module tracks the elementary fact that a distinguished job cannot be
recorded as complete before enough physical time has elapsed to provide its
own declared service work.  It is independent of a probability law and is
used by stationary tagged-queue constructions to make their queue-wait
horizons nonnegative.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- A distinguished job's completed record is no earlier than its service
requirement after `origin`; if it is currently active, its completion bound
includes its stored residual service. -/
def nonpreemptivePriorityTaggedCompletionLowerBound
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  origin ≤ state.currentTime ∧
    (∀ completedAt, (tag, completedAt) ∈ state.completed →
      origin + tag.serviceWork ≤ completedAt) ∧
    (∀ residual, state.active = some (tag, residual) →
      origin + tag.serviceWork ≤ state.currentTime + residual)

/-- At a service-decision epoch, a tag that has not yet completed and has
either not started or has just been started with its full declared work has
the current clock as a fresh completion lower-bound origin.  This small
reset lemma is used when a finite tagged trace reaches an intervening service
completion: it does not assume a stochastic model or a particular priority
rule. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_at_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hnotCompleted : ¬ ∃ completedAt, (tag, completedAt) ∈ state.completed)
    (hactive : ∀ residual, state.active = some (tag, residual) →
      residual = tag.serviceWork) :
    nonpreemptivePriorityTaggedCompletionLowerBound state.currentTime tag state := by
  constructor
  · exact le_rfl
  constructor
  · intro completedAt hcompleted
    exact (hnotCompleted ⟨completedAt, hcompleted⟩).elim
  · intro residual htag
    rw [hactive residual htag]

/-- Completing a different active job creates a new service-decision epoch
for the tag.  The tag has not completed at that epoch, and if dispatch starts
it then its residual is exactly its declared work; therefore the standard
completion lower bound can be restarted at the other job's completion time.
This is the deterministic strict-delay step used to show that a tag cannot
be merely waiting at `completion time - own service`. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_after_complete_other_at_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hstate : state.active = some active)
    (hother : active.1 ≠ tag)
    (hnotCompleted : ¬ ∃ completedAt, (tag, completedAt) ∈ state.completed) :
    nonpreemptivePriorityTaggedCompletionLowerBound
      (state.currentTime + active.2) tag
      (completeNonpreemptivePriorityWorkJob
        { state with currentTime := state.currentTime + active.2 }) := by
  classical
  let completedState : NonpreemptivePriorityWorkState n JobId :=
    { state with currentTime := state.currentTime + active.2 }
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { completedState with
      active := none
      completed := (active.1, completedState.currentTime) :: completedState.completed }
  have hcomplete :
      completeNonpreemptivePriorityWorkJob completedState =
        startNextNonpreemptivePriorityJob afterCompletion := by
    simp [completeNonpreemptivePriorityWorkJob, completedState, afterCompletion, hstate]
  have hledger :
      (completeNonpreemptivePriorityWorkJob completedState).completed =
        (active.1, completedState.currentTime) :: state.completed := by
    calc
      (completeNonpreemptivePriorityWorkJob completedState).completed =
          (startNextNonpreemptivePriorityJob afterCompletion).completed := by
            rw [hcomplete]
      _ = afterCompletion.completed :=
            completed_startNextNonpreemptivePriorityJob afterCompletion
      _ = (active.1, completedState.currentTime) :: state.completed := rfl
  have hnotCompletedAfter : ¬ ∃ completedAt,
      (tag, completedAt) ∈ (completeNonpreemptivePriorityWorkJob completedState).completed := by
    rintro ⟨completedAt, hcompleted⟩
    rw [hledger] at hcompleted
    rcases List.mem_cons.mp hcompleted with hnew | hold
    · apply hother
      exact (congrArg Prod.fst hnew).symm
    · apply hnotCompleted
      exact ⟨completedAt, by simpa [completedState] using hold⟩
  have hactiveAfter : ∀ residual,
      (completeNonpreemptivePriorityWorkJob completedState).active = some (tag, residual) →
        residual = tag.serviceWork := by
    intro residual htag
    rw [hcomplete] at htag
    have hafterActive : afterCompletion.active = none := rfl
    by_cases hwaiting : hasPriorityWaitingJob afterCompletion
    · let selected := nextPriorityWaitingClass afterCompletion hwaiting
      cases hhead : afterCompletion.waiting selected with
      | nil =>
          simp only [startNextNonpreemptivePriorityJob, hafterActive,
            dif_pos hwaiting, selected, hhead] at htag
          cases htag
      | cons head tail =>
          have hpair : (head, head.serviceWork) = (tag, residual) := by
            exact Option.some.inj (by
              simpa only [startNextNonpreemptivePriorityJob, hafterActive, dif_pos hwaiting,
                selected, hhead] using htag)
          have hjob : head = tag := congrArg Prod.fst hpair
          have hresidual : head.serviceWork = residual := congrArg Prod.snd hpair
          rw [← hresidual, hjob]
    · simp only [startNextNonpreemptivePriorityJob, hafterActive,
        dif_neg hwaiting] at htag
      cases htag
  have hbound :=
    nonpreemptivePriorityTaggedCompletionLowerBound_at_currentTime
      (completeNonpreemptivePriorityWorkJob completedState) tag hnotCompletedAfter hactiveAfter
  rw [completeNonpreemptivePriorityWorkJob_currentTime] at hbound
  simpa [completedState] using hbound

/-- Moving a state clock forward without changing its live jobs preserves the
tagged completion lower bound. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_timeUpdate
    {n : ℕ} {JobId : Type*}
    (origin target : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state)
    (htarget : state.currentTime ≤ target) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      { state with currentTime := target } := by
  constructor
  · exact hbound.1.trans htarget
  constructor
  · intro completedAt hcompleted
    exact hbound.2.1 completedAt (by simpa using hcompleted)
  · intro residual hactive
    have hprevious := hbound.2.2 residual (by simpa using hactive)
    linarith

/-- Enqueuing a different job changes neither the tagged active record nor
the completion ledger, so it preserves the tagged completion bound. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_enqueue
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag newJob : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (enqueueNonpreemptivePriorityJob state newJob) := by
  simpa [nonpreemptivePriorityTaggedCompletionLowerBound,
    enqueueNonpreemptivePriorityJob] using hbound

/-- Starting the next waiting job preserves the tagged completion lower
bound.  If the tag itself becomes active, its residual is exactly its full
declared service work and the state clock has not moved. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_startNext
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (startNextNonpreemptivePriorityJob state) := by
  classical
  constructor
  · rw [startNextNonpreemptivePriorityJob_currentTime]
    exact hbound.1
  constructor
  · intro completedAt hcompleted
    apply hbound.2.1 completedAt
    simpa [completed_startNextNonpreemptivePriorityJob] using hcompleted
  · intro residual hactive
    cases hstate : state.active with
    | some active =>
        have hactive' : state.active = some (tag, residual) := by
          simpa [startNextNonpreemptivePriorityJob, hstate] using hactive
        simpa [startNextNonpreemptivePriorityJob, hstate] using
          hbound.2.2 residual hactive'
    | none =>
        by_cases hwaiting : hasPriorityWaitingJob state
        · let selected := nextPriorityWaitingClass state hwaiting
          cases hhead : state.waiting selected with
          | nil =>
              simp [startNextNonpreemptivePriorityJob, hstate, hwaiting,
                selected, hhead] at hactive
          | cons head tail =>
              have hpair : (head, head.serviceWork) = (tag, residual) := by
                simpa [startNextNonpreemptivePriorityJob, hstate, hwaiting,
                  selected, hhead] using hactive
              have htag : head = tag := congrArg Prod.fst hpair
              have hresidual : head.serviceWork = residual := congrArg Prod.snd hpair
              rw [startNextNonpreemptivePriorityJob_currentTime]
              rw [← htag, ← hresidual]
              linarith [hbound.1]
        · simp [startNextNonpreemptivePriorityJob, hstate, hwaiting] at hactive

/-- Admitting a job distinct from the tag preserves the tagged completion
bound.  A newly active job in the formerly idle case cannot be the tag by the
displayed distinctness hypothesis. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_admit_of_ne
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag newJob : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state)
    (hnew : newJob ≠ tag) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (admitNonpreemptivePriorityJob state newJob) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonpreemptivePriorityTaggedCompletionLowerBound origin tag prepared := by
    simpa [prepared] using
      nonpreemptivePriorityTaggedCompletionLowerBound_startNext origin tag state hbound
  cases hactive : prepared.active with
  | none =>
      constructor
      · rw [admitNonpreemptivePriorityJob_currentTime]
        rw [← startNextNonpreemptivePriorityJob_currentTime state]
        simpa [prepared] using hprepared.1
      constructor
      · intro completedAt hcompleted
        apply hprepared.2.1 completedAt
        simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted
      · intro residual htag
        have hpair : (newJob, newJob.serviceWork) = (tag, residual) := by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using htag
        exact (hnew (congrArg Prod.fst hpair)).elim
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        (nonpreemptivePriorityTaggedCompletionLowerBound_enqueue
          origin tag newJob prepared hprepared)

/-- Starting the next waiting job only changes a resident job's location, so
it cannot create a new occurrence of a specified job. -/
theorem nonpreemptivePriorityWorkStateContainsJob_startNext_iff
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateContainsJob
      (startNextNonpreemptivePriorityJob state) job ↔
      nonpreemptivePriorityWorkStateContainsJob state job := by
  constructor
  · classical
    intro hcontains
    cases hactive : state.active with
    | some active =>
        simpa [nonpreemptivePriorityWorkStateContainsJob,
          startNextNonpreemptivePriorityJob, hactive] using hcontains
    | none =>
        by_cases hwaiting : hasPriorityWaitingJob state
        · let selected := nextPriorityWaitingClass state hwaiting
          cases hhead : state.waiting selected with
          | nil =>
              simpa [nonpreemptivePriorityWorkStateContainsJob,
                startNextNonpreemptivePriorityJob, hactive, hwaiting,
                selected, hhead] using hcontains
          | cons head tail =>
              rcases hcontains with hactiveJob | hwaitingJob | hcompleted
              · rcases hactiveJob with ⟨residual, hjob⟩
                have hpair : (head, head.serviceWork) = (job, residual) := by
                  simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hhead] using hjob
                right
                left
                refine ⟨selected, ?_⟩
                rw [hhead]
                exact List.mem_cons.mpr (Or.inl (congrArg Prod.fst hpair).symm)
              · rcases hwaitingJob with ⟨k, hjob⟩
                right
                left
                refine ⟨k, ?_⟩
                by_cases hk : k = selected
                · subst k
                  have htail : job ∈ tail := by
                    simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                      selected, hhead] using hjob
                  rw [hhead]
                  exact List.mem_cons.mpr (Or.inr htail)
                · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hhead, Function.update_of_ne hk] using hjob
              · exact Or.inr (Or.inr (by
                  simpa [completed_startNextNonpreemptivePriorityJob] using hcompleted))
        · simpa [nonpreemptivePriorityWorkStateContainsJob,
              startNextNonpreemptivePriorityJob, hactive, hwaiting] using hcontains
  · exact nonpreemptivePriorityWorkStateContainsJob_startNext state job

/-- A fresh tagged admission establishes the tagged completion lower bound:
the tag is either started with its full service requirement or joins a queue
whose active job is known to be different. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_admit_self_of_fresh
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (htime : origin ≤ state.currentTime)
    (hfresh : ¬ nonpreemptivePriorityWorkStateContainsJob state tag) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (admitNonpreemptivePriorityJob state tag) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hpreparedTime : origin ≤ prepared.currentTime := by
    rw [show prepared.currentTime = state.currentTime by
      simpa [prepared] using startNextNonpreemptivePriorityJob_currentTime state]
    exact htime
  have hpreparedFresh : ¬ nonpreemptivePriorityWorkStateContainsJob prepared tag := by
    intro hcontains
    apply hfresh
    exact (nonpreemptivePriorityWorkStateContainsJob_startNext_iff state tag).mp
      (by simpa [prepared] using hcontains)
  cases hactive : prepared.active with
  | none =>
      constructor
      · rw [admitNonpreemptivePriorityJob_currentTime]
        rw [← startNextNonpreemptivePriorityJob_currentTime state]
        simpa [prepared] using hpreparedTime
      constructor
      · intro completedAt hcompleted
        exact (hpreparedFresh (Or.inr (Or.inr ⟨completedAt, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted⟩))).elim
      · intro residual htag
        have hpair : (tag, tag.serviceWork) = (tag, residual) := by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using htag
        have hresidual : tag.serviceWork = residual := congrArg Prod.snd hpair
        rw [admitNonpreemptivePriorityJob_currentTime,
          ← startNextNonpreemptivePriorityJob_currentTime state]
        rw [← hresidual]
        linarith [hpreparedTime]
  | some active =>
      constructor
      · rw [admitNonpreemptivePriorityJob_currentTime]
        rw [← startNextNonpreemptivePriorityJob_currentTime state]
        simpa [prepared] using hpreparedTime
      constructor
      · intro completedAt hcompleted
        exact (hpreparedFresh (Or.inr (Or.inr ⟨completedAt, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted⟩))).elim
      · intro residual htag
        have htag' : prepared.active = some (tag, residual) := by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive,
            enqueueNonpreemptivePriorityJob] using htag
        exact (hpreparedFresh (Or.inl ⟨residual, htag'⟩)).elim

/-- Completing an active service after exactly its residual amount turns the
active tagged bound into a bound on the new completion record.  Dispatching a
successor then preserves that bound. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_complete_after_residual
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state)
    (hactive : state.active = some active)
    (hnonnegative : 0 ≤ active.2) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (completeNonpreemptivePriorityWorkJob
        { state with currentTime := state.currentTime + active.2 }) := by
  classical
  let completedState : NonpreemptivePriorityWorkState n JobId :=
    { state with currentTime := state.currentTime + active.2 }
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { completedState with active := none, completed :=
      (active.1, completedState.currentTime) :: completedState.completed }
  have hafter : nonpreemptivePriorityTaggedCompletionLowerBound origin tag afterCompletion := by
    constructor
    · dsimp [afterCompletion, completedState]
      linarith [hbound.1]
    constructor
    · intro completedAt hcompleted
      rw [show afterCompletion.completed =
          (active.1, completedState.currentTime) :: completedState.completed by rfl] at hcompleted
      rcases List.mem_cons.mp hcompleted with hnew | hold
      · have htag : tag = active.1 := congrArg Prod.fst hnew
        have htime : completedAt = completedState.currentTime := congrArg Prod.snd hnew
        have hactiveTag : state.active = some (tag, active.2) := by
          rw [hactive, htag]
        have hprevious := hbound.2.2 active.2 hactiveTag
        dsimp [completedState] at htime
        linarith
      · apply hbound.2.1 completedAt
        simpa [afterCompletion, completedState] using hold
    · intro residual htag
      simp [afterCompletion] at htag
  have hnext := nonpreemptivePriorityTaggedCompletionLowerBound_startNext
    origin tag afterCompletion hafter
  simpa [completeNonpreemptivePriorityWorkJob, completedState, afterCompletion,
    hactive] using hnext

/-- Bounded service evolution preserves the tagged completion lower bound
when all stored residual work is nonnegative.  The completion branch uses the
active residual exactly; the partial-service branch preserves the sum of the
clock and the tag residual. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (origin target : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag state)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              (nonpreemptivePriorityTaggedCompletionLowerBound_timeUpdate
                origin target tag state hbound htime)
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hbound
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              (nonpreemptivePriorityTaggedCompletionLowerBound_timeUpdate
                origin target tag state hbound htime)
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedBound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                simpa [completedState] using
                  (nonpreemptivePriorityTaggedCompletionLowerBound_complete_after_residual
                    origin tag state active hbound hactive (hwork.1 active hactive))
              have hcompletedWork : nonnegativeNonpreemptivePriorityResidualWork
                  completedState := by
                constructor
                · intro other hother
                  simpa [completedState] using hwork.1 other hother
                · intro j other hmember
                  simpa [completedState] using hwork.2 j other hmember
              have hnextWork : nonnegativeNonpreemptivePriorityResidualWork
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                exact nonnegativeNonpreemptivePriorityResidualWork_complete
                  completedState hcompletedWork
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState)
                hcompletedBound hnextWork
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using hind
            · constructor
              · have horigin : origin ≤ target :=
                  hbound.1.trans (le_of_lt (lt_of_not_ge htarget))
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] using horigin
              constructor
              · intro completedAt hcompleted
                apply hbound.2.1 completedAt
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] using hcompleted
              · intro residual htag
                have hpair : (active.1,
                    active.2 - (target - state.currentTime)) = (tag, residual) := by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using htag
                have htagEq : active.1 = tag := congrArg Prod.fst hpair
                have hresidual : active.2 - (target - state.currentTime) = residual :=
                  congrArg Prod.snd hpair
                have hactiveTag : state.active = some (tag, active.2) := by
                  have hactivePair : active = (tag, active.2) := by
                    apply Prod.ext
                    · exact htagEq
                    · rfl
                  rw [hactive]
                  rw [hactivePair]
                have hprevious := hbound.2.2 active.2 hactiveTag
                have hcurrent :
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).currentTime =
                      target := by
                  simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                rw [hcurrent, ← hresidual]
                linarith

/-- Replaying a finite list of arrivals that excludes the tag preserves its
completion-time lower bound.  Each replay step advances physical service and
then admits a different job, so the tagged ledger invariant is unchanged. -/
theorem nonpreemptivePriorityTaggedCompletionLowerBound_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionLowerBound origin tag initial)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork)
    (hjobsDistinct : ∀ job ∈ jobs, job ≠ tag) :
    nonpreemptivePriorityTaggedCompletionLowerBound origin tag
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hbound
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedBound :
          nonpreemptivePriorityTaggedCompletionLowerBound origin tag advanced := by
        simpa [advanced] using
          nonpreemptivePriorityTaggedCompletionLowerBound_advance
            (totalNonpreemptivePriorityWorkJobs initial) origin job.arrivalTime tag initial
            hbound hwork
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hjobWork : 0 ≤ job.serviceWork := hjobsWork job (by simp)
      have hjobDistinct : job ≠ tag := hjobsDistinct job (by simp)
      have hadmittedBound :
          nonpreemptivePriorityTaggedCompletionLowerBound origin tag admitted := by
        simpa [admitted] using
          nonpreemptivePriorityTaggedCompletionLowerBound_admit_of_ne
            origin tag job advanced hadvancedBound hjobDistinct
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork hjobWork
      have htailWork : ∀ other ∈ jobs, 0 ≤ other.serviceWork := by
        intro other hother
        exact hjobsWork other (by simp [hother])
      have htailDistinct : ∀ other ∈ jobs, other ≠ tag := by
        intro other hother
        exact hjobsDistinct other (by simp [hother])
      have htail := ih admitted hadmittedBound hadmittedWork htailWork htailDistinct
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using htail

end

end AppliedModelingLib.Queueing
