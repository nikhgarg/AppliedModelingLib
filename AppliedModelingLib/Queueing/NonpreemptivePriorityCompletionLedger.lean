import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceRegeneration
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkload

/-!
# Completion-ledger preservation for finite nonpreemptive-priority queues

This module tracks one literal job through the deterministic finite priority
semantics.  A job may be active, waiting in its class FIFO list, or entered in
the completion ledger; every queue operation preserves that trichotomy.  The
result lets a later tagged-arrival construction turn an empty finite state into
an actual completion record rather than an aggregate-work assertion alone.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Reset the observational completion ledger while retaining the complete
live priority queue.  This does not alter any future service or admission
decision, and is useful when a new tagged observation begins at a specified
physical epoch. -/
def clearNonpreemptivePriorityCompletionLedger
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  { state with completed := [] }

/-- Clearing the observational ledger leaves the live queue unchanged. -/
theorem liveEquivalent_clearNonpreemptivePriorityCompletionLedger
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    liveEquivalentNonpreemptivePriorityWorkState
      (clearNonpreemptivePriorityCompletionLedger state) state := by
  exact ⟨rfl, rfl, rfl⟩

/-- The cleared ledger has no completion records. -/
theorem completed_clearNonpreemptivePriorityCompletionLedger
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    (clearNonpreemptivePriorityCompletionLedger state).completed = [] := rfl

/-- Once the historical completion records have been cleared, live-equivalent
priority states are definitionally the same finite queue state. -/
theorem clearNonpreemptivePriorityCompletionLedger_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    clearNonpreemptivePriorityCompletionLedger first =
      clearNonpreemptivePriorityCompletionLedger second := by
  rcases first with ⟨firstTime, firstActive, firstWaiting, firstCompleted⟩
  rcases second with ⟨secondTime, secondActive, secondWaiting, secondCompleted⟩
  rcases hequivalent with ⟨htime, hactive, hwaiting⟩
  change firstTime = secondTime at htime
  change firstActive = secondActive at hactive
  change firstWaiting = secondWaiting at hwaiting
  subst secondTime
  subst secondActive
  subst secondWaiting
  rfl

/-- Selecting the next waiting job only changes the live queue, not its
completion observations. -/
theorem completed_startNextNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    (startNextNonpreemptivePriorityJob state).completed = state.completed := by
  classical
  cases hactive : state.active with
  | some active => simp [startNextNonpreemptivePriorityJob, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil => simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
        | cons head tail =>
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
      · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Enqueuing a job leaves the completion observations unchanged. -/
theorem completed_enqueueNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (enqueueNonpreemptivePriorityJob state job).completed = state.completed := rfl

/-- Admission adds only a live customer and therefore retains the entire
completion ledger. -/
theorem completed_admitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (admitNonpreemptivePriorityJob state job).completed = state.completed := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : prepared.completed = state.completed := by
    simpa [prepared] using completed_startNextNonpreemptivePriorityJob state
  cases hactive : prepared.active with
  | none =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hprepared
  | some active =>
      rw [show (admitNonpreemptivePriorityJob state job).completed = prepared.completed by
        simp [admitNonpreemptivePriorityJob, prepared, hactive,
          completed_enqueueNonpreemptivePriorityJob]]
      exact hprepared

/-- A specified job is present in a finite priority state if it is active,
waiting in a class FIFO list, or has been recorded as completed. -/
def nonpreemptivePriorityWorkStateContainsJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) : Prop :=
  (∃ residual, state.active = some (job, residual)) ∨
    (∃ i, job ∈ state.waiting i) ∨
      ∃ time, (job, time) ∈ state.completed

/-- Starting the next waiting job only changes the live location of a job;
it never loses a job from the active/waiting/completed trichotomy. -/
theorem nonpreemptivePriorityWorkStateContainsJob_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateContainsJob
      (startNextNonpreemptivePriorityJob state) job := by
  classical
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
              startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead] using hcontains
        | cons head tail =>
            rcases hcontains with hactiveJob | hwaitingJob | hcompleted
            · rcases hactiveJob with ⟨residual, hjob⟩
              simp [hactive] at hjob
            · rcases hwaitingJob with ⟨j, hjob⟩
              by_cases hselected : j = selected
              · subst j
                rw [hhead] at hjob
                rcases List.mem_cons.mp hjob with hjob | hjob
                · subst job
                  left
                  refine ⟨head.serviceWork, ?_⟩
                  simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hhead]
                · right
                  left
                  refine ⟨selected, ?_⟩
                  simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hhead, hjob]
              · right
                left
                refine ⟨j, ?_⟩
                simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hhead, Function.update_of_ne hselected, hjob]
            · right
              right
              simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                selected, hhead] using hcompleted
      · simpa [nonpreemptivePriorityWorkStateContainsJob,
        startNextNonpreemptivePriorityJob, hactive, hwaiting] using hcontains

/-- Starting a waiting job never removes a prior completion record. -/
theorem mem_completed_startNextNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    (job, completedAt) ∈ (startNextNonpreemptivePriorityJob state).completed := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hcompleted
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
              selected, hhead] using hcompleted
        | cons head tail =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
              selected, hhead] using hcompleted
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hcompleted

/-- Enqueuing a new job retains all prior completion records. -/
theorem mem_completed_enqueueNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    (job, completedAt) ∈ (enqueueNonpreemptivePriorityJob state newJob).completed := by
  simpa [enqueueNonpreemptivePriorityJob] using hcompleted

/-- Admitting a new job retains all prior completion records. -/
theorem mem_completed_admitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    (job, completedAt) ∈ (admitNonpreemptivePriorityJob state newJob).completed := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : (job, completedAt) ∈ prepared.completed := by
    simpa [prepared] using
      mem_completed_startNextNonpreemptivePriorityJob state job completedAt hcompleted
  cases hactive : prepared.active with
  | none =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hprepared
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        mem_completed_enqueueNonpreemptivePriorityJob prepared newJob job completedAt hprepared

/-- Completing the active job and selecting a successor retains every prior
completion record. -/
theorem mem_completed_completeNonpreemptivePriorityWorkJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    (job, completedAt) ∈ (completeNonpreemptivePriorityWorkJob state).completed := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hcompleted
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : (job, completedAt) ∈ afterCompletion.completed := by
        change (job, completedAt) ∈ (active.1, state.currentTime) :: state.completed
        exact List.mem_cons.mpr (Or.inr hcompleted)
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using
        mem_completed_startNextNonpreemptivePriorityJob afterCompletion job completedAt hafter

/-- Enqueuing a customer preserves every job already present in the state. -/
theorem nonpreemptivePriorityWorkStateContainsJob_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateContainsJob
      (enqueueNonpreemptivePriorityJob state newJob) job := by
  rcases hcontains with hactive | hwaiting | hcompleted
  · left
    exact hactive
  · rcases hwaiting with ⟨j, hjob⟩
    right
    left
    by_cases hj : j = newJob.priority
    · subst j
      refine ⟨newJob.priority, ?_⟩
      rw [enqueueNonpreemptivePriorityJob_waiting_selected]
      exact List.mem_append_left _ hjob
    · refine ⟨j, ?_⟩
      rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state newJob j hj]
      exact hjob
  · right
    right
    exact hcompleted

/-- Enqueuing a job explicitly places that job in its class FIFO list. -/
theorem nonpreemptivePriorityWorkStateContainsJob_enqueue_self
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateContainsJob
      (enqueueNonpreemptivePriorityJob state job) job := by
  right
  left
  refine ⟨job.priority, ?_⟩
  rw [enqueueNonpreemptivePriorityJob_waiting_selected]
  simp

/-- Admitting a new job never loses a job already represented by the state. -/
theorem nonpreemptivePriorityWorkStateContainsJob_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateContainsJob
      (admitNonpreemptivePriorityJob state newJob) job := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonpreemptivePriorityWorkStateContainsJob prepared job := by
    simpa [prepared] using
      nonpreemptivePriorityWorkStateContainsJob_startNext state job hcontains
  cases hactive : prepared.active with
  | none =>
      rcases hprepared with hactiveJob | hwaitingJob | hcompleted
      · rcases hactiveJob with ⟨residual, hjob⟩
        simp [hactive] at hjob
      · rcases hwaitingJob with ⟨j, hjob⟩
        right
        left
        refine ⟨j, ?_⟩
        simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hjob
      · right
        right
        simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        nonpreemptivePriorityWorkStateContainsJob_enqueue prepared newJob job hprepared

/-- Admission explicitly inserts the newly admitted job into the state. -/
theorem nonpreemptivePriorityWorkStateContainsJob_admit_self
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateContainsJob
      (admitNonpreemptivePriorityJob state job) job := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  cases hactive : prepared.active with
  | none =>
      left
      refine ⟨job.serviceWork, ?_⟩
      simp [admitNonpreemptivePriorityJob, prepared, hactive]
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        nonpreemptivePriorityWorkStateContainsJob_enqueue_self prepared job

/-- Completing the active job and choosing the next one preserves every
literal job record. -/
theorem nonpreemptivePriorityWorkStateContainsJob_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateContainsJob
      (completeNonpreemptivePriorityWorkJob state) job := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hcontains
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : nonpreemptivePriorityWorkStateContainsJob afterCompletion job := by
        rcases hcontains with hactiveJob | hwaitingJob | hcompleted
        · rcases hactiveJob with ⟨residual, hjob⟩
          have hpair : active = (job, residual) := by
            exact Option.some.inj (hactive.symm.trans hjob)
          subst active
          right
          right
          refine ⟨state.currentTime, ?_⟩
          simp [afterCompletion]
        · right
          left
          rcases hwaitingJob with ⟨j, hjob⟩
          exact ⟨j, by simpa [afterCompletion] using hjob⟩
        · right
          right
          rcases hcompleted with ⟨time, hjob⟩
          exact ⟨time, by simp [afterCompletion, hjob]⟩
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using
        nonpreemptivePriorityWorkStateContainsJob_startNext afterCompletion job hafter

/-- Bounded service evolution retains any completion record already present. -/
theorem mem_completed_advanceNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    (job, completedAt) ∈
      (advanceNonpreemptivePriorityWorkState fuel target state).completed := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcompleted
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcompleted
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedState : (job, completedAt) ∈ completedState.completed := by
                simpa [completedState] using hcompleted
              have hnext : (job, completedAt) ∈
                  (completeNonpreemptivePriorityWorkJob completedState).completed := by
                exact mem_completed_completeNonpreemptivePriorityWorkJob
                  completedState job completedAt hcompletedState
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState) hnext
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using hind
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                using hcompleted

/-- Bounded service evolution preserves the location-or-completion record of
every job already in the finite state. -/
theorem nonpreemptivePriorityWorkStateContainsJob_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateContainsJob
      (advanceNonpreemptivePriorityWorkState fuel target state) job := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcontains
      · cases hactive : state.active with
        | none =>
            simpa [nonpreemptivePriorityWorkStateContainsJob,
              advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
        | some active =>
            simpa [nonpreemptivePriorityWorkStateContainsJob,
              advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcontains
      · cases hactive : state.active with
        | none =>
            simpa [nonpreemptivePriorityWorkStateContainsJob,
              advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAt : nonpreemptivePriorityWorkStateContainsJob completedAt job := by
                simpa [completedAt] using hcontains
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt)
                (nonpreemptivePriorityWorkStateContainsJob_complete
                  completedAt job hcompletedAt)
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedAt] using hind
            · rcases hcontains with hactiveJob | hwaitingJob | hcompleted
              · rcases hactiveJob with ⟨residual, hjob⟩
                have hpair : active = (job, residual) :=
                  Option.some.inj (hactive.symm.trans hjob)
                subst active
                simp [nonpreemptivePriorityWorkStateContainsJob,
                  advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
              · simpa [nonpreemptivePriorityWorkStateContainsJob,
                  advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                  using Or.inr (Or.inl hwaitingJob)
              · simpa [nonpreemptivePriorityWorkStateContainsJob,
                  advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                  using Or.inr (Or.inr hcompleted)

/-- Executing any finite list of further admissions preserves a previously
represented job's location-or-completion record. -/
theorem nonpreemptivePriorityWorkStateContainsJob_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob initial job) :
    nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace initial jobs) job := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hcontains
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      have hadvanced : nonpreemptivePriorityWorkStateContainsJob advanced job := by
        simpa [advanced] using nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial job hcontains
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadmitted : nonpreemptivePriorityWorkStateContainsJob admitted job := by
        simpa [admitted] using nonpreemptivePriorityWorkStateContainsJob_admit
          advanced newJob job hadvanced
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted

/-- Executing a finite future arrival trace retains all completion records
already present at the trace start. -/
theorem mem_completed_runNonpreemptivePriorityArrivalTrace
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ)
    (hcompleted : (job, completedAt) ∈ initial.completed) :
    (job, completedAt) ∈
      (runNonpreemptivePriorityArrivalTrace initial jobs).completed := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hcompleted
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      have hadvanced : (job, completedAt) ∈ advanced.completed := by
        simpa [advanced] using mem_completed_advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial job completedAt hcompleted
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadmitted : (job, completedAt) ∈ admitted.completed := by
        simpa [admitted] using mem_completed_admitNonpreemptivePriorityJob
          advanced newJob job completedAt hadvanced
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted

/-- A later finite queue state extends an earlier completion observation when
it retains the earlier ledger as a suffix and only prepends newly completed
jobs. -/
def nonpreemptivePriorityCompletionLedgerExtension
    {n : ℕ} {JobId : Type*}
    (earlier later : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∃ newlyCompleted, later.completed = newlyCompleted ++ earlier.completed

/-- Completion-ledger extension is reflexive. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_refl
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state state := by
  exact ⟨[], by simp⟩

/-- Completion-ledger extension composes along deterministic queue steps. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_trans
    {n : ℕ} {JobId : Type*}
    (first second third : NonpreemptivePriorityWorkState n JobId)
    (hfirst : nonpreemptivePriorityCompletionLedgerExtension first second)
    (hsecond : nonpreemptivePriorityCompletionLedgerExtension second third) :
    nonpreemptivePriorityCompletionLedgerExtension first third := by
  rcases hfirst with ⟨firstNew, hfirst⟩
  rcases hsecond with ⟨secondNew, hsecond⟩
  refine ⟨secondNew ++ firstNew, ?_⟩
  rw [hsecond, hfirst, List.append_assoc]

/-- Starting the next waiting job preserves the completion ledger exactly. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state
      (startNextNonpreemptivePriorityJob state) := by
  refine ⟨[], ?_⟩
  simp [completed_startNextNonpreemptivePriorityJob]

/-- Enqueuing a job preserves the completion ledger exactly. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state
      (enqueueNonpreemptivePriorityJob state job) := by
  refine ⟨[], ?_⟩
  simp [completed_enqueueNonpreemptivePriorityJob]

/-- Admission changes only the live queue and therefore preserves the
completion ledger exactly. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state
      (admitNonpreemptivePriorityJob state job) := by
  refine ⟨[], ?_⟩
  simp [completed_admitNonpreemptivePriorityJob]

/-- Completing the active job prepends at most that one new completion
record; all earlier observations remain intact. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using
        nonpreemptivePriorityCompletionLedgerExtension_refl state
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      refine ⟨[(active.1, state.currentTime)], ?_⟩
      calc
        (completeNonpreemptivePriorityWorkJob state).completed =
            (startNextNonpreemptivePriorityJob afterCompletion).completed := by
              simp [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion]
        _ = afterCompletion.completed :=
            completed_startNextNonpreemptivePriorityJob afterCompletion
        _ = [(active.1, state.currentTime)] ++ state.completed := rfl

/-- Bounded service evolution only prepends completion records. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityCompletionLedgerExtension state
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using
          nonpreemptivePriorityCompletionLedgerExtension_refl state
      · cases hactive : state.active with
        | none =>
            exact ⟨[], by simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]⟩
        | some active =>
            exact ⟨[], by simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]⟩
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using
          nonpreemptivePriorityCompletionLedgerExtension_refl state
      · cases hactive : state.active with
        | none =>
            exact ⟨[], by simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]⟩
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              let next := completeNonpreemptivePriorityWorkJob completedState
              have hstep : nonpreemptivePriorityCompletionLedgerExtension state next := by
                apply nonpreemptivePriorityCompletionLedgerExtension_trans state completedState next
                · exact ⟨[], by simp [completedState]⟩
                · exact nonpreemptivePriorityCompletionLedgerExtension_complete completedState
              have htail := ih next
              have htotal := nonpreemptivePriorityCompletionLedgerExtension_trans
                state next (advanceNonpreemptivePriorityWorkState fuel target next) hstep htail
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState, next] using htotal
            · exact ⟨[], by
                simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]⟩

/-- With a fixed completion-fuel budget, serving a queue to a later physical
time only prepends completion records to those already present at an earlier
time. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_advance_mono
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (earlier later : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hearlier : earlier ≤ later) :
    nonpreemptivePriorityCompletionLedgerExtension
      (advanceNonpreemptivePriorityWorkState fuel earlier state)
      (advanceNonpreemptivePriorityWorkState fuel later state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : earlier ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using
          nonpreemptivePriorityCompletionLedgerExtension_advance 0 later state
      · have htime : state.currentTime < earlier := lt_of_not_ge htarget
        have hlater : ¬ later ≤ state.currentTime := by
          exact not_le_of_gt (lt_of_lt_of_le htime hearlier)
        cases hactive : state.active with
        | none =>
            exact ⟨[], by
              simp [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive]⟩
        | some active =>
            exact ⟨[], by
              simp [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive]⟩
  | succ fuel ih =>
      classical
      by_cases htarget : earlier ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using
          nonpreemptivePriorityCompletionLedgerExtension_advance (fuel + 1) later state
      · have htime : state.currentTime < earlier := lt_of_not_ge htarget
        have hlater : ¬ later ≤ state.currentTime := by
          exact not_le_of_gt (lt_of_lt_of_le htime hearlier)
        cases hactive : state.active with
        | none =>
            exact ⟨[], by
              simp [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive]⟩
        | some active =>
            by_cases hcompleteEarlier : active.2 ≤ earlier - state.currentTime
            · have hcompleteLater : active.2 ≤ later - state.currentTime := by
                linarith
              let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              let next := completeNonpreemptivePriorityWorkJob completedState
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive,
                hcompleteEarlier, hcompleteLater, completedState, next] using
                ih next
            · by_cases hcompleteLater : active.2 ≤ later - state.currentTime
              · rcases nonpreemptivePriorityCompletionLedgerExtension_advance
                  (fuel + 1) later state with ⟨newlyCompleted, hnew⟩
                refine ⟨newlyCompleted, ?_⟩
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive,
                  hcompleteEarlier, hcompleteLater] using hnew
              · exact ⟨[], by
                  simp [advanceNonpreemptivePriorityWorkState, htarget, hlater, hactive,
                    hcompleteEarlier, hcompleteLater]⟩

/-- Executing a finite arrival trace only prepends completion observations to
the ledger present at its initial state. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityCompletionLedgerExtension initial
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil =>
      simpa [runNonpreemptivePriorityArrivalTrace] using
        nonpreemptivePriorityCompletionLedgerExtension_refl initial
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadvanced : nonpreemptivePriorityCompletionLedgerExtension initial advanced := by
        exact nonpreemptivePriorityCompletionLedgerExtension_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      have hadmitted : nonpreemptivePriorityCompletionLedgerExtension initial admitted := by
        exact nonpreemptivePriorityCompletionLedgerExtension_trans initial advanced admitted
          hadvanced (nonpreemptivePriorityCompletionLedgerExtension_admit advanced newJob)
      have htail := ih admitted
      have htotal := nonpreemptivePriorityCompletionLedgerExtension_trans initial admitted
        (runNonpreemptivePriorityArrivalTrace admitted jobs) hadmitted htail
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using htotal

/-- If all later arrivals occur at or after a cutoff, then the completion
ledger after the complete finite continuation extends the ledger observed at
that cutoff. -/
theorem nonpreemptivePriorityCompletionLedgerExtension_advance_run_from_cutoff
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (cutoff terminal : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (hcutoffTerminal : cutoff ≤ terminal)
    (hjobs : ∀ job ∈ jobs, cutoff ≤ job.arrivalTime) :
    nonpreemptivePriorityCompletionLedgerExtension
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) cutoff state)
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace state jobs)) := by
  cases jobs with
  | nil =>
      simpa [runNonpreemptivePriorityArrivalTrace] using
        nonpreemptivePriorityCompletionLedgerExtension_advance_mono
          (totalNonpreemptivePriorityWorkJobs state) cutoff terminal state hcutoffTerminal
  | cons first rest =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) first.arrivalTime state
      let admitted := admitNonpreemptivePriorityJob advanced first
      have hfirst : cutoff ≤ first.arrivalTime := hjobs first (by simp)
      have hadvanced : nonpreemptivePriorityCompletionLedgerExtension
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) cutoff state) advanced := by
        simpa [advanced] using
          nonpreemptivePriorityCompletionLedgerExtension_advance_mono
            (totalNonpreemptivePriorityWorkJobs state) cutoff first.arrivalTime state hfirst
      have hadmitted : nonpreemptivePriorityCompletionLedgerExtension
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) cutoff state) admitted := by
        exact nonpreemptivePriorityCompletionLedgerExtension_trans _ advanced admitted
          hadvanced (nonpreemptivePriorityCompletionLedgerExtension_admit advanced first)
      have htail : nonpreemptivePriorityCompletionLedgerExtension admitted
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace admitted rest)) terminal
            (runNonpreemptivePriorityArrivalTrace admitted rest)) := by
        exact nonpreemptivePriorityCompletionLedgerExtension_trans _
          (runNonpreemptivePriorityArrivalTrace admitted rest)
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace admitted rest)) terminal
            (runNonpreemptivePriorityArrivalTrace admitted rest))
          (nonpreemptivePriorityCompletionLedgerExtension_run admitted rest)
          (nonpreemptivePriorityCompletionLedgerExtension_advance
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace admitted rest)) terminal
            (runNonpreemptivePriorityArrivalTrace admitted rest))
      have htotal := nonpreemptivePriorityCompletionLedgerExtension_trans _ admitted _
        hadmitted htail
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using htotal

/-- In a positive-work state with zero total residual work, every represented
job must already occur in the completion ledger. -/
theorem exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (htotal : totalNonpreemptivePriorityResidualWork state = 0)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job) :
    ∃ time, (job, time) ∈ state.completed := by
  rcases active_eq_none_and_waiting_eq_nil_of_totalResidualWork_eq_zero
    state hpositive htotal with ⟨hactive, hwaiting⟩
  rcases hcontains with hactiveJob | hwaitingJob | hcompleted
  · rcases hactiveJob with ⟨residual, hjob⟩
    rw [hactive] at hjob
    simp at hjob
  · rcases hwaitingJob with ⟨i, hjob⟩
    rw [hwaiting i] at hjob
    simp at hjob
  · exact hcompleted

/-- If a represented job's finite continuation has emptied by a terminal
epoch, then the terminal completion ledger contains that job.  This is the
deterministic tagged-customer form of busy-period domination: later arrivals
may affect the completion time, but cannot let a still-live represented job
coexist with zero residual work. -/
theorem exists_completedTime_advance_run_of_totalResidualWork_eq_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (terminal : ℝ) (job : NonpreemptivePriorityJob n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hjobsPositive : ∀ other ∈ jobs, 0 < other.serviceWork)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job)
    (htotal : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace state jobs)) = 0) :
    ∃ completedAt,
      (job, completedAt) ∈
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
          (runNonpreemptivePriorityArrivalTrace state jobs)).completed := by
  apply exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
      (runNonpreemptivePriorityArrivalTrace state jobs)) job
  · exact positiveNonpreemptivePriorityResidualWork_advance
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
      (runNonpreemptivePriorityArrivalTrace state jobs)
      (positiveNonpreemptivePriorityResidualWork_run state jobs hpositive hjobsPositive)
  · exact htotal
  · exact nonpreemptivePriorityWorkStateContainsJob_advance
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace state jobs)) terminal
      (runNonpreemptivePriorityArrivalTrace state jobs) job
      (nonpreemptivePriorityWorkStateContainsJob_run state jobs job hcontains)

/-- If a tagged job is present before an arrival-free emptying epoch, then it
has a completion record after any later finite continuation.  The result uses
the literal service evolution up to the first later arrival; after that record
is created, the completion ledger is monotone under admissions and service. -/
theorem exists_completedTime_advance_run_of_empty_at_cutoff
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (cutoff terminal : ℝ)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId)
    (hcurrentCutoff : state.currentTime ≤ cutoff)
    (hcutoffTerminal : cutoff ≤ terminal)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) cutoff state) = 0)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job)
    (hjobs : ∀ other ∈ jobs, cutoff ≤ other.arrivalTime) :
    ∃ completedAt,
      (job, completedAt) ∈
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace state jobs))
          terminal
          (runNonpreemptivePriorityArrivalTrace state jobs)).completed := by
  cases jobs with
  | nil =>
      have hterminalZero : totalNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) terminal state) = 0 := by
        exact totalNonpreemptivePriorityResidualWork_advance_eq_zero_of_advance_eq_zero
          (totalNonpreemptivePriorityWorkJobs state) state cutoff terminal
          hcurrentCutoff hcutoffTerminal hpositive hwork le_rfl hcutoffZero
      have hterminalPositive : positiveNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) terminal state) := by
        exact positiveNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs state) terminal state hpositive
      have hterminalContains : nonpreemptivePriorityWorkStateContainsJob
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) terminal state) job := by
        exact nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs state) terminal state job hcontains
      simpa [runNonpreemptivePriorityArrivalTrace] using
        (exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) terminal state)
          job hterminalPositive hterminalZero hterminalContains)
  | cons first rest =>
      have hfirstCutoff : cutoff ≤ first.arrivalTime := hjobs first (by simp)
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) first.arrivalTime state
      have hadvancedZero : totalNonpreemptivePriorityResidualWork advanced = 0 := by
        dsimp [advanced]
        exact totalNonpreemptivePriorityResidualWork_advance_eq_zero_of_advance_eq_zero
          (totalNonpreemptivePriorityWorkJobs state) state cutoff first.arrivalTime
          hcurrentCutoff hfirstCutoff hpositive hwork le_rfl hcutoffZero
      have hadvancedPositive : positiveNonpreemptivePriorityResidualWork advanced := by
        dsimp [advanced]
        exact positiveNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs state) first.arrivalTime state hpositive
      have hadvancedContains : nonpreemptivePriorityWorkStateContainsJob advanced job := by
        dsimp [advanced]
        exact nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs state) first.arrivalTime state job hcontains
      rcases exists_completedTime_of_nonpreemptivePriorityWorkStateContainsJob_of_totalResidualWork_eq_zero
        advanced job hadvancedPositive hadvancedZero hadvancedContains with ⟨completedAt, hcompleted⟩
      let admitted := admitNonpreemptivePriorityJob advanced first
      have hadmitted : (job, completedAt) ∈ admitted.completed := by
        dsimp [admitted]
        exact mem_completed_admitNonpreemptivePriorityJob
          advanced first job completedAt hcompleted
      have hafter : (job, completedAt) ∈
          (runNonpreemptivePriorityArrivalTrace admitted rest).completed := by
        exact mem_completed_runNonpreemptivePriorityArrivalTrace
          admitted rest job completedAt hadmitted
      have hterminal : (job, completedAt) ∈
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs
              (runNonpreemptivePriorityArrivalTrace admitted rest))
            terminal
            (runNonpreemptivePriorityArrivalTrace admitted rest)).completed := by
        exact mem_completed_advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace admitted rest))
          terminal (runNonpreemptivePriorityArrivalTrace admitted rest)
          job completedAt hafter
      refine ⟨completedAt, ?_⟩
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using hterminal

end

end AppliedModelingLib.Queueing
