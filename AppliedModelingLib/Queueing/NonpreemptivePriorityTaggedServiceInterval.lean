import AppliedModelingLib.Queueing.NonpreemptivePriorityAdvanceSemigroup
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedCompletionBound

/-!
# Tagged service intervals in finite nonpreemptive-priority traces

Once a job is in positive service, nonpreemption fixes its physical completion
epoch: later admissions may join the queue but cannot interrupt the residual
service.  This file records that deterministic fact for finite arrival traces.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- A tag has a fixed service completion epoch when it has already completed,
or it is currently in strictly positive active service with the residual work
needed to reach that epoch. -/
def nonpreemptivePriorityTaggedServiceSchedule
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId) (completionTime : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  (tag, completionTime) ∈ state.completed ∨
    state.currentTime < completionTime ∧
    state.active = some (tag, completionTime - state.currentTime)

/-- Whenever the tagged job is active, its stored remaining work is no
greater than its declared service requirement.  This is a deterministic
provenance invariant: dispatch initializes the residual at the full work
requirement and service evolution can only decrease it. -/
def nonpreemptivePriorityTaggedResidualLeService
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∀ residual, state.active = some (tag, residual) → residual ≤ tag.serviceWork

/-- Dispatching the next job preserves the tagged residual upper bound.  If
the tag is newly dispatched, its residual is exactly its declared work. -/
theorem nonpreemptivePriorityTaggedResidualLeService_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (startNextNonpreemptivePriorityJob state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [nonpreemptivePriorityTaggedResidualLeService,
        startNextNonpreemptivePriorityJob, hactive] using hbound
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simp [nonpreemptivePriorityTaggedResidualLeService,
              startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
        | cons head tail =>
            intro residual htag
            have hpair : (head, head.serviceWork) = (tag, residual) := by
              exact Option.some.inj (by
                simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hhead] using htag)
            have hjob : head = tag := congrArg Prod.fst hpair
            have hresidual : head.serviceWork = residual := congrArg Prod.snd hpair
            rw [← hresidual, hjob]
      · simp [nonpreemptivePriorityTaggedResidualLeService,
          startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Completing the current job preserves the tagged residual upper bound.  A
newly dispatched tag is initialized with its full declared work. -/
theorem nonpreemptivePriorityTaggedResidualLeService_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hbound
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed :=
          (active.1, state.currentTime) :: state.completed }
      have hafter : nonpreemptivePriorityTaggedResidualLeService tag afterCompletion := by
        intro residual htag
        simp [afterCompletion] at htag
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using
        (nonpreemptivePriorityTaggedResidualLeService_startNext afterCompletion tag hafter)

/-- Advancing the queue through finitely many possible completions preserves
the tagged residual upper bound. -/
theorem nonpreemptivePriorityTaggedResidualLeService_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            simp [nonpreemptivePriorityTaggedResidualLeService,
              advanceNonpreemptivePriorityWorkState, htarget, hactive]
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hbound
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            simp [nonpreemptivePriorityTaggedResidualLeService,
              advanceNonpreemptivePriorityWorkState, htarget, hactive]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompleted : nonpreemptivePriorityTaggedResidualLeService tag
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                apply nonpreemptivePriorityTaggedResidualLeService_complete completedState tag
                intro residual htag
                simpa [completedState] using hbound residual htag
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState) hcompleted
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using hind
            · intro residual htag
              have hpair : (active.1,
                  active.2 - (target - state.currentTime)) = (tag, residual) := by
                exact Option.some.inj (by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using htag)
              have htagEq : active.1 = tag := congrArg Prod.fst hpair
              have hresidual : active.2 - (target - state.currentTime) = residual :=
                congrArg Prod.snd hpair
              have hprevious : active.2 ≤ tag.serviceWork := by
                have hactiveTag : state.active = some (tag, active.2) := by
                  have hactivePair : active = (tag, active.2) := by
                    exact Prod.ext htagEq rfl
                  rw [hactive, hactivePair]
                exact hbound active.2 hactiveTag
              have helapsed : 0 ≤ target - state.currentTime := by
                linarith
              rw [← hresidual]
              linarith

/-- Admitting a customer distinct from the tag preserves the tagged residual
upper bound. -/
theorem nonpreemptivePriorityTaggedResidualLeService_admit_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag newJob : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state)
    (hnew : newJob ≠ tag) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (admitNonpreemptivePriorityJob state newJob) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonpreemptivePriorityTaggedResidualLeService tag prepared := by
    simpa [prepared] using
      (nonpreemptivePriorityTaggedResidualLeService_startNext state tag hbound)
  cases hactive : prepared.active with
  | none =>
      intro residual htag
      have hpair : (newJob, newJob.serviceWork) = (tag, residual) := by
        exact Option.some.inj (by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using htag)
      exact (hnew (congrArg Prod.fst hpair)).elim
  | some active =>
      intro residual htag
      have htag' : prepared.active = some (tag, residual) := by
        simpa [admitNonpreemptivePriorityJob, prepared, hactive,
          enqueueNonpreemptivePriorityJob] using htag
      exact hprepared residual htag'

/-- A fresh tagged admission satisfies the residual upper bound.  If the
server is idle, dispatch starts the tag at its full declared work; otherwise
freshness rules out the tag already being active. -/
theorem nonpreemptivePriorityTaggedResidualLeService_admit_self_of_fresh
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hfresh : ¬ nonpreemptivePriorityWorkStateContainsJob state tag) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (admitNonpreemptivePriorityJob state tag) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hpreparedFresh : ¬ nonpreemptivePriorityWorkStateContainsJob prepared tag := by
    intro hcontains
    apply hfresh
    exact (nonpreemptivePriorityWorkStateContainsJob_startNext_iff state tag).mp
      (by simpa [prepared] using hcontains)
  cases hactive : prepared.active with
  | none =>
      intro residual htag
      have hpair : (tag, tag.serviceWork) = (tag, residual) := by
        exact Option.some.inj (by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using htag)
      have hresidual : tag.serviceWork = residual := congrArg Prod.snd hpair
      rw [← hresidual]
  | some active =>
      intro residual htag
      have htag' : prepared.active = some (tag, residual) := by
        simpa [admitNonpreemptivePriorityJob, prepared, hactive,
          enqueueNonpreemptivePriorityJob] using htag
      exact (hpreparedFresh (Or.inl ⟨residual, htag'⟩)).elim

/-- A finite arrival trace whose input records exclude the tag preserves the
tagged residual upper bound. -/
theorem nonpreemptivePriorityTaggedResidualLeService_run_of_forall_ne
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag initial)
    (hdistinct : ∀ job ∈ jobs, job ≠ tag) :
    nonpreemptivePriorityTaggedResidualLeService tag
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hbound
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : nonpreemptivePriorityTaggedResidualLeService tag advanced := by
        simpa [advanced] using
          (nonpreemptivePriorityTaggedResidualLeService_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial tag hbound)
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : nonpreemptivePriorityTaggedResidualLeService tag admitted := by
        simpa [admitted] using
          (nonpreemptivePriorityTaggedResidualLeService_admit_of_ne
            advanced tag job hadvanced (hdistinct job (by simp)))
      have htail : ∀ other ∈ jobs, other ≠ tag := by
        intro other hother
        exact hdistinct other (by simp [hother])
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted htail

/-- A job with strictly positive active residual work has the corresponding
fixed service completion epoch. -/
theorem nonpreemptivePriorityTaggedServiceSchedule_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (tag, residual))
    (hresidual : 0 < residual) :
    nonpreemptivePriorityTaggedServiceSchedule tag (state.currentTime + residual) state := by
  right
  constructor
  · linarith
  · rw [hactive]
    congr 1
    ring_nf

/-- A recorded completion survives every later admission, while a job already
in service remains active through the admission transition. -/
theorem nonpreemptivePriorityTaggedServiceSchedule_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag job : NonpreemptivePriorityJob n JobId) (completionTime : ℝ)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      (admitNonpreemptivePriorityJob state job) := by
  rcases hschedule with hcompleted | ⟨hcurrent, hactive⟩
  · left
    exact mem_completed_admitNonpreemptivePriorityJob state job tag completionTime hcompleted
  · right
    constructor
    · rw [admitNonpreemptivePriorityJob_currentTime]
      exact hcurrent
    · simpa [admitNonpreemptivePriorityJob,
        startNextNonpreemptivePriorityJob, hactive,
        enqueueNonpreemptivePriorityJob] using hactive

/-- A positive-fuel service evolution preserves a tagged completion schedule.
In the active case the tag either finishes at its scheduled epoch or remains
the active job with the correspondingly reduced residual work. -/
theorem nonpreemptivePriorityTaggedServiceSchedule_advance_succ
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target completionTime : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) := by
  classical
  rcases hschedule with hcompleted | ⟨hcurrent, hactive⟩
  · left
    exact mem_completed_advanceNonpreemptivePriorityWorkState
      (fuel + 1) target state tag completionTime hcompleted
  · by_cases htarget : target ≤ state.currentTime
    · right
      simpa [advanceNonpreemptivePriorityWorkState, htarget] using ⟨hcurrent, hactive⟩
    · by_cases hcomplete : completionTime ≤ target
      · left
        have hresidual : completionTime - state.currentTime ≤ target - state.currentTime := by
          linarith
        let completedState : NonpreemptivePriorityWorkState n JobId :=
          { state with currentTime := state.currentTime +
              (completionTime - state.currentTime) }
        let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
          { completedState with
            active := none,
            completed := (tag, completionTime) :: completedState.completed }
        have hactiveCompleted : completedState.active =
            some (tag, completionTime - state.currentTime) := by
          simpa [completedState] using hactive
        have hcompletedTime : completedState.currentTime = completionTime := by
          dsimp [completedState]
          ring
        have hcompleteState : completeNonpreemptivePriorityWorkJob completedState =
            startNextNonpreemptivePriorityJob afterCompletion := by
          simp [completeNonpreemptivePriorityWorkJob, hactiveCompleted,
            afterCompletion, hcompletedTime]
        have hnew : (tag, completionTime) ∈
            (completeNonpreemptivePriorityWorkJob completedState).completed := by
          rw [hcompleteState]
          exact mem_completed_startNextNonpreemptivePriorityJob
            afterCompletion tag completionTime (by simp [afterCompletion])
        have hpreserved := mem_completed_advanceNonpreemptivePriorityWorkState
          fuel target (completeNonpreemptivePriorityWorkJob completedState)
          tag completionTime hnew
        simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
          hresidual, completedState] using hpreserved
      · right
        have hpartial : ¬ (completionTime - state.currentTime ≤
            target - state.currentTime) := by
          intro hle
          exact hcomplete (by linarith)
        have hadvance :
            advanceNonpreemptivePriorityWorkState (fuel + 1) target state =
              { state with
                currentTime := target,
                active := some (tag, (completionTime - state.currentTime) -
                  (target - state.currentTime)) } := by
          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hpartial]
        rw [hadvance]
        constructor
        · exact lt_of_not_ge hcomplete
        · have hresidualEq : (completionTime - state.currentTime) -
              (target - state.currentTime) = completionTime - target := by
            ring
          simp [hresidualEq]

/-- If a scheduled completion lies no later than the requested target, a
positive-fuel service evolution records it. -/
theorem mem_completed_advanceNonpreemptivePriorityWorkState_of_taggedServiceSchedule
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target completionTime : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (htarget : completionTime ≤ target)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    (tag, completionTime) ∈
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).completed := by
  classical
  rcases hschedule with hcompleted | ⟨hcurrent, hactive⟩
  · exact mem_completed_advanceNonpreemptivePriorityWorkState
      (fuel + 1) target state tag completionTime hcompleted
  · have htargetCurrent : ¬ target ≤ state.currentTime := by
      linarith
    have hresidual : completionTime - state.currentTime ≤ target - state.currentTime := by
      linarith
    let completedState : NonpreemptivePriorityWorkState n JobId :=
      { state with currentTime := state.currentTime +
          (completionTime - state.currentTime) }
    let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
      { completedState with
        active := none,
        completed := (tag, completionTime) :: completedState.completed }
    have hactiveCompleted : completedState.active =
        some (tag, completionTime - state.currentTime) := by
      simpa [completedState] using hactive
    have hcompletedTime : completedState.currentTime = completionTime := by
      dsimp [completedState]
      ring
    have hcompleteState : completeNonpreemptivePriorityWorkJob completedState =
        startNextNonpreemptivePriorityJob afterCompletion := by
      simp [completeNonpreemptivePriorityWorkJob, hactiveCompleted,
        afterCompletion, hcompletedTime]
    have hnew : (tag, completionTime) ∈
        (completeNonpreemptivePriorityWorkJob completedState).completed := by
      rw [hcompleteState]
      exact mem_completed_startNextNonpreemptivePriorityJob
        afterCompletion tag completionTime (by simp [afterCompletion])
    have hpreserved := mem_completed_advanceNonpreemptivePriorityWorkState
      fuel target (completeNonpreemptivePriorityWorkJob completedState)
      tag completionTime hnew
    simpa [advanceNonpreemptivePriorityWorkState, htargetCurrent, hactive,
      hresidual, completedState] using hpreserved

/-- Processing one future arrival retains a tagged completion schedule. -/
theorem nonpreemptivePriorityTaggedServiceSchedule_advanceThenAdmit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag job : NonpreemptivePriorityJob n JobId) (completionTime : ℝ)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      (advanceThenAdmitNonpreemptivePriorityJob
        (totalNonpreemptivePriorityWorkJobs state) state job) := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  apply nonpreemptivePriorityTaggedServiceSchedule_admit
  rcases hschedule with hcompleted | ⟨hcurrent, hactive⟩
  · left
    exact mem_completed_advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs state) job.arrivalTime state tag completionTime hcompleted
  · have hcount : 0 < totalNonpreemptivePriorityWorkJobs state := by
      unfold totalNonpreemptivePriorityWorkJobs
      simp [hactive]
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount) with ⟨fuel, hfuel⟩
    rw [hfuel]
    exact nonpreemptivePriorityTaggedServiceSchedule_advance_succ
      fuel job.arrivalTime completionTime state tag (Or.inr ⟨hcurrent, hactive⟩)

/-- An arbitrary finite future arrival ledger cannot alter the scheduled
completion of a tag already in positive service. -/
theorem nonpreemptivePriorityTaggedServiceSchedule_run
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (completionTime : ℝ)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      (runNonpreemptivePriorityArrivalTrace state jobs) := by
  induction jobs generalizing state with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hschedule
  | cons job jobs ih =>
      rw [runNonpreemptivePriorityArrivalTrace]
      simp only [List.foldl_cons]
      exact ih
        (advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs state) state job)
        (nonpreemptivePriorityTaggedServiceSchedule_advanceThenAdmit
          state tag job completionTime hschedule)

/-- A scheduled tagged completion is recorded after any finite future arrival
ledger once the queried horizon reaches its fixed service epoch.  This is the
nonpreemptive fact that later admissions cannot change an active job's
completion time. -/
theorem mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_taggedServiceSchedule
    {n : ℕ} {JobId : Type*}
    (target completionTime : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (htarget : completionTime ≤ target)
    (hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state) :
    (tag, completionTime) ∈
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state jobs)) target
        (runNonpreemptivePriorityArrivalTrace state jobs)).completed := by
  let afterArrivals := runNonpreemptivePriorityArrivalTrace state jobs
  have hafter : nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedServiceSchedule_run state jobs tag completionTime hschedule
  rcases hafter with hcompleted | ⟨hcurrent, hactive⟩
  · exact mem_completed_advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs afterArrivals) target afterArrivals
      tag completionTime hcompleted
  · have hcount : 0 < totalNonpreemptivePriorityWorkJobs afterArrivals := by
      unfold totalNonpreemptivePriorityWorkJobs
      simp [hactive]
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount) with ⟨fuel, hfuel⟩
    rw [hfuel]
    exact mem_completed_advanceNonpreemptivePriorityWorkState_of_taggedServiceSchedule
      fuel target completionTime afterArrivals tag htarget (Or.inr ⟨hcurrent, hactive⟩)

/-- After any finite future arrival ledger, advancing to or beyond the fixed
service epoch records a tag that was initially in positive active service. -/
theorem mem_completed_advance_runNonpreemptivePriorityArrivalTrace_of_active
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (tag, residual))
    (hresidual : 0 < residual)
    (htarget : state.currentTime + residual ≤ target) :
    (tag, state.currentTime + residual) ∈
      (advanceNonpreemptivePriorityWorkState (fuel + 1) target
        (runNonpreemptivePriorityArrivalTrace state jobs)).completed := by
  let completionTime := state.currentTime + residual
  have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime
      (runNonpreemptivePriorityArrivalTrace state jobs) :=
    nonpreemptivePriorityTaggedServiceSchedule_run state jobs tag completionTime
      (nonpreemptivePriorityTaggedServiceSchedule_of_active state tag residual hactive hresidual)
  exact mem_completed_advanceNonpreemptivePriorityWorkState_of_taggedServiceSchedule
    fuel target completionTime (runNonpreemptivePriorityArrivalTrace state jobs)
      tag htarget hschedule

end

end AppliedModelingLib.Queueing
