import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionLedger

/-!
# Completion-time bounds for finite nonpreemptive-priority queues

The completion ledger records physical service-completion epochs.  This module
proves the elementary but essential temporal invariant that every recorded
epoch lies at or before the state clock.  Later FIFO and workload arguments use
this to turn a persistent predecessor disposition into a time-ordered
completion fact.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Every completion record in the observational ledger is timestamped no
later than the physical clock of the finite queue state. -/
def nonpreemptivePriorityCompletionTimesLeCurrentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∀ (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ),
    (job, completedAt) ∈ state.completed → completedAt ≤ state.currentTime

/-- A finite replay started at `origin` has not moved its clock backwards, and
every completion recorded since that observational origin is strictly later
than it.  Clearing a historical ledger establishes the second clause; strict
positive residual work is what preserves it through subsequent service
evolution. -/
def nonpreemptivePriorityCompletionTimesAfter
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  origin ≤ state.currentTime ∧
    ∀ (job : NonpreemptivePriorityJob n JobId) (completedAt : ℝ),
      (job, completedAt) ∈ state.completed → origin < completedAt

/-- Resetting the observational ledger retains the physical clock and hence
starts a fresh completion-time origin. -/
theorem nonpreemptivePriorityCompletionTimesAfter_clear
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hclock : origin ≤ state.currentTime) :
    nonpreemptivePriorityCompletionTimesAfter origin
      (clearNonpreemptivePriorityCompletionLedger state) := by
  constructor
  · simpa [clearNonpreemptivePriorityCompletionLedger] using hclock
  · intro job completedAt hcompleted
    simp [clearNonpreemptivePriorityCompletionLedger] at hcompleted

/-- Admission does not alter already-recorded completion epochs or the
physical clock. -/
theorem nonpreemptivePriorityCompletionTimesAfter_admit
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (newJob : NonpreemptivePriorityJob n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesAfter origin state) :
    nonpreemptivePriorityCompletionTimesAfter origin
      (admitNonpreemptivePriorityJob state newJob) := by
  constructor
  · rw [admitNonpreemptivePriorityJob_currentTime]
    exact htimes.1
  · intro job completedAt hcompleted
    apply htimes.2 job completedAt
    simpa [completed_admitNonpreemptivePriorityJob] using hcompleted

/-- Completing at a clock strictly after the observational origin preserves
the origin-relative ledger invariant. -/
theorem nonpreemptivePriorityCompletionTimesAfter_complete
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesAfter origin state)
    (hcurrent : origin < state.currentTime) :
    nonpreemptivePriorityCompletionTimesAfter origin
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using htimes
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hledger : (completeNonpreemptivePriorityWorkJob state).completed =
          (active.1, state.currentTime) :: state.completed := by
        calc
          (completeNonpreemptivePriorityWorkJob state).completed =
              (startNextNonpreemptivePriorityJob afterCompletion).completed := by
                simp [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion]
          _ = afterCompletion.completed :=
              completed_startNextNonpreemptivePriorityJob afterCompletion
          _ = (active.1, state.currentTime) :: state.completed := rfl
      constructor
      · rw [completeNonpreemptivePriorityWorkJob_currentTime]
        exact htimes.1
      · intro job completedAt hcompleted
        rw [hledger] at hcompleted
        rcases List.mem_cons.mp hcompleted with hnew | hold
        · have hjob : job = active.1 := congrArg Prod.fst hnew
          have htime : completedAt = state.currentTime := congrArg Prod.snd hnew
          subst job
          subst completedAt
          exact hcurrent
        · exact htimes.2 job completedAt hold

/-- Bounded service evolution preserves completion times strictly after an
observational origin whenever all remaining work is strictly positive. -/
theorem nonpreemptivePriorityCompletionTimesAfter_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target origin : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : positiveNonpreemptivePriorityResidualWork state)
    (htimes : nonpreemptivePriorityCompletionTimesAfter origin state) :
    nonpreemptivePriorityCompletionTimesAfter origin
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using htimes
      · cases hactive : state.active with
        | none =>
            constructor
            · simp only [advanceNonpreemptivePriorityWorkState, htarget, hactive]
              exact htimes.1.trans (le_of_lt (lt_of_not_ge htarget))
            · intro job completedAt hcompleted
              apply htimes.2 job completedAt
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using htimes
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using htimes
      · have hcurrentTarget : state.currentTime < target := lt_of_not_ge htarget
        cases hactive : state.active with
        | none =>
            constructor
            · simp only [advanceNonpreemptivePriorityWorkState, htarget, hactive]
              exact htimes.1.trans hcurrentTarget.le
            · intro job completedAt hcompleted
              apply htimes.2 job completedAt
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedTimes : nonpreemptivePriorityCompletionTimesAfter origin
                  completedState := by
                constructor
                · dsimp [completedState]
                  exact htimes.1.trans (by linarith [hwork.1 active hactive])
                · intro job completedAt hcompleted
                  exact htimes.2 job completedAt (by
                    simpa [completedState] using hcompleted)
              have hcompletedClock : origin < completedState.currentTime := by
                dsimp [completedState]
                linarith [htimes.1, hwork.1 active hactive]
              have hnextTimes : nonpreemptivePriorityCompletionTimesAfter origin
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                exact nonpreemptivePriorityCompletionTimesAfter_complete
                  origin completedState hcompletedTimes hcompletedClock
              have hnextWork : positiveNonpreemptivePriorityResidualWork
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                apply positiveNonpreemptivePriorityResidualWork_complete completedState
                constructor
                · intro other hother
                  simpa [completedState] using hwork.1 other hother
                · intro j other hmember
                  simpa [completedState] using hwork.2 j other hmember
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using
                ih (completeNonpreemptivePriorityWorkJob completedState) hnextWork hnextTimes
            · constructor
              · simp only [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                exact htimes.1.trans hcurrentTarget.le
              · intro job completedAt hcompleted
                apply htimes.2 job completedAt
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
                  hcompleted

/-- A finite chronological trace preserves the origin-relative completion
invariant when each arriving job has strictly positive service work. -/
theorem nonpreemptivePriorityCompletionTimesAfter_run
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hinitial : positiveNonpreemptivePriorityResidualWork initial)
    (htimes : nonpreemptivePriorityCompletionTimesAfter origin initial)
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    nonpreemptivePriorityCompletionTimesAfter origin
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using htimes
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedWork : positiveNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using positiveNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hinitial
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesAfter origin advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesAfter_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime origin initial hinitial htimes
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmittedWork : positiveNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using positiveNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork (hjobs job (by simp))
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesAfter origin admitted := by
        simpa [admitted] using nonpreemptivePriorityCompletionTimesAfter_admit
          origin advanced job hadvancedTimes
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmittedWork hadmittedTimes
          (fun other hother => hjobs other (by simp [hother]))

/-- Selecting a waiting job changes neither the ledger nor the physical
clock, so it preserves completion-time bounds. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (startNextNonpreemptivePriorityJob state) := by
  intro job completedAt hcompleted
  rw [show (startNextNonpreemptivePriorityJob state).currentTime = state.currentTime by
    exact startNextNonpreemptivePriorityJob_currentTime state]
  apply htimes job completedAt
  simpa [completed_startNextNonpreemptivePriorityJob] using hcompleted

/-- Tail admission changes neither the ledger nor the physical clock, so it
preserves completion-time bounds. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob : NonpreemptivePriorityJob n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (enqueueNonpreemptivePriorityJob state newJob) := by
  intro job completedAt hcompleted
  change completedAt ≤ state.currentTime
  exact htimes job completedAt (by
    simpa [enqueueNonpreemptivePriorityJob] using hcompleted)

/-- Completing the active job appends a record at exactly the current clock;
all older records retain their previously proved time bound. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using htimes
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hledger : (completeNonpreemptivePriorityWorkJob state).completed =
          (active.1, state.currentTime) :: state.completed := by
        calc
          (completeNonpreemptivePriorityWorkJob state).completed =
              (startNextNonpreemptivePriorityJob afterCompletion).completed := by
                simp [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion]
          _ = afterCompletion.completed :=
              completed_startNextNonpreemptivePriorityJob afterCompletion
          _ = (active.1, state.currentTime) :: state.completed := rfl
      intro job completedAt hcompleted
      rw [hledger] at hcompleted
      rcases List.mem_cons.mp hcompleted with hnew | hold
      · have hjob : job = active.1 := congrArg Prod.fst hnew
        have htime : completedAt = state.currentTime := congrArg Prod.snd hnew
        subst job
        subst completedAt
        rw [completeNonpreemptivePriorityWorkJob_currentTime]
      · rw [completeNonpreemptivePriorityWorkJob_currentTime]
        exact htimes job completedAt hold

/-- Admission changes neither the ledger nor the physical clock, so it
preserves completion-time bounds. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob : NonpreemptivePriorityJob n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (admitNonpreemptivePriorityJob state newJob) := by
  intro job completedAt hcompleted
  rw [show (admitNonpreemptivePriorityJob state newJob).currentTime = state.currentTime by
    exact admitNonpreemptivePriorityJob_currentTime state newJob]
  apply htimes job completedAt
  simpa [completed_admitNonpreemptivePriorityJob] using hcompleted

/-- Advancing a nonnegative-work queue preserves the fact that all recorded
completion epochs are in its physical past. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using htimes
      · have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
        cases hactive : state.active with
        | none =>
            intro job completedAt hcompleted
            have hbound : completedAt ≤ target := (htimes job completedAt (by
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted)).trans htime
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hbound
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using htimes
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using htimes
      · have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
        cases hactive : state.active with
        | none =>
            intro job completedAt hcompleted
            have hbound : completedAt ≤ target := (htimes job completedAt (by
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcompleted)).trans htime
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hbound
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedWork : nonnegativeNonpreemptivePriorityResidualWork completedState := by
                constructor
                · intro other hother
                  simpa [completedState] using hwork.1 other hother
                · intro j other hmember
                  simpa [completedState] using hwork.2 j other hmember
              have hcompletedTimes :
                  nonpreemptivePriorityCompletionTimesLeCurrentTime completedState := by
                intro job completedAt hcompleted
                change completedAt ≤ state.currentTime + active.2
                have hbound : completedAt ≤ state.currentTime :=
                  htimes job completedAt (by simpa [completedState] using hcompleted)
                have hresidual : 0 ≤ active.2 := hwork.1 active hactive
                linarith
              have hnextWork : nonnegativeNonpreemptivePriorityResidualWork
                  (completeNonpreemptivePriorityWorkJob completedState) :=
                nonnegativeNonpreemptivePriorityResidualWork_complete completedState hcompletedWork
              have hnextTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime
                  (completeNonpreemptivePriorityWorkJob completedState) :=
                nonpreemptivePriorityCompletionTimesLeCurrentTime_complete
                  completedState hcompletedTimes
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using
                ih (completeNonpreemptivePriorityWorkJob completedState) hnextWork hnextTimes
            · intro job completedAt hcompleted
              have hbound : completedAt ≤ target := (htimes job completedAt (by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] using hcompleted)).trans htime
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete] using hbound

/-- A chronological finite replay with nonnegative service marks preserves
completion-time bounds. -/
theorem nonpreemptivePriorityCompletionTimesLeCurrentTime_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hjobs : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonpreemptivePriorityCompletionTimesLeCurrentTime
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using htimes
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork htimes
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork (hjobs job (by simp))
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime admitted := by
        simpa [admitted] using
          nonpreemptivePriorityCompletionTimesLeCurrentTime_admit advanced job hadvancedTimes
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using
        ih admitted hadmittedWork hadmittedTimes
          (fun other hother => hjobs other (by simp [hother]))

/-- Appending an arrival exactly at a queried horizon cannot change the
completion ledger observed at that horizon.  Its service requirement remains
live work after the observation and is therefore irrelevant to the recorded
completion times. -/
theorem completed_advance_run_append_singleton_at_arrival
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId) (fuel : ℕ) (target : ℝ)
    (hclock : (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ target)
    (harrival : job.arrivalTime = target) :
    (advanceNonpreemptivePriorityWorkState fuel target
      (runNonpreemptivePriorityArrivalTrace initial (front ++ [job]))).completed =
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace initial front)) target
        (runNonpreemptivePriorityArrivalTrace initial front)).completed := by
  rw [runNonpreemptivePriorityArrivalTrace_append]
  simp only [runNonpreemptivePriorityArrivalTrace, List.foldl_cons,
    List.foldl_nil, advanceThenAdmitNonpreemptivePriorityJob]
  rw [harrival]
  let frontState := runNonpreemptivePriorityArrivalTrace initial front
  let advanced := advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs frontState) target frontState
  let admitted := admitNonpreemptivePriorityJob advanced job
  have hadvancedClock : advanced.currentTime = target := by
    dsimp [advanced]
    exact advanceNonpreemptivePriorityWorkState_currentTime_eq_target
      (totalNonpreemptivePriorityWorkJobs frontState) target frontState (by
        simpa [frontState] using hclock) le_rfl
  have hadmittedClock : admitted.currentTime = target := by
    rw [show admitted.currentTime = advanced.currentTime by
      exact admitNonpreemptivePriorityJob_currentTime advanced job]
    exact hadvancedClock
  change (advanceNonpreemptivePriorityWorkState fuel target admitted).completed =
    advanced.completed
  have hadvance : advanceNonpreemptivePriorityWorkState fuel target admitted = admitted := by
    cases fuel with
    | zero => simp [advanceNonpreemptivePriorityWorkState, hadmittedClock]
    | succ fuel => simp [advanceNonpreemptivePriorityWorkState, hadmittedClock]
  rw [hadvance]
  exact completed_admitNonpreemptivePriorityJob advanced job

/-- Consequently, replacing the full data of an arrival at the queried
horizon, including its service requirement, leaves all already-recorded
completion times unchanged. -/
theorem completed_advance_run_append_singleton_at_arrival_congr
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front : List (NonpreemptivePriorityJob n JobId))
    (first second : NonpreemptivePriorityJob n JobId) (fuel : ℕ) (target : ℝ)
    (hclock : (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ target)
    (hfirst : first.arrivalTime = target) (hsecond : second.arrivalTime = target) :
    (advanceNonpreemptivePriorityWorkState fuel target
      (runNonpreemptivePriorityArrivalTrace initial (front ++ [first]))).completed =
      (advanceNonpreemptivePriorityWorkState fuel target
        (runNonpreemptivePriorityArrivalTrace initial (front ++ [second]))).completed := by
  rw [completed_advance_run_append_singleton_at_arrival initial front first fuel target
    hclock hfirst,
    completed_advance_run_append_singleton_at_arrival initial front second fuel target
      hclock hsecond]

/-- Once a finite queue trace has reached a physical horizon, processing any
finite list of arrivals at exactly that same horizon leaves its completion
ledger unchanged. -/
theorem completed_run_of_all_arrivalTime_eq_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (hcurrent : state.currentTime = target)
    (harrival : ∀ job ∈ jobs, job.arrivalTime = target) :
    (runNonpreemptivePriorityArrivalTrace state jobs).completed = state.completed := by
  induction jobs generalizing state with
  | nil => rfl
  | cons job jobs ih =>
      have hjob : job.arrivalTime = target := harrival job (by simp)
      have htarget : job.arrivalTime ≤ state.currentTime := by
        rw [hjob, hcurrent]
      have hadvance : advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs state) job.arrivalTime state = state := by
        cases totalNonpreemptivePriorityWorkJobs state <;>
          simp [advanceNonpreemptivePriorityWorkState, htarget]
      have hstep : advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs state) state job =
          admitNonpreemptivePriorityJob state job := by
        simp only [advanceThenAdmitNonpreemptivePriorityJob, hadvance]
      change (runNonpreemptivePriorityArrivalTrace
        (advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs state) state job) jobs).completed =
        state.completed
      rw [hstep]
      calc
        (runNonpreemptivePriorityArrivalTrace
          (admitNonpreemptivePriorityJob state job) jobs).completed =
            (admitNonpreemptivePriorityJob state job).completed := by
              apply ih
              · rw [admitNonpreemptivePriorityJob_currentTime]
                exact hcurrent
              · intro later hlater
                exact harrival later (by simp [hlater])
        _ = state.completed := completed_admitNonpreemptivePriorityJob state job

/-- A finite run consisting only of arrivals at its initial clock remains at
that same physical clock. -/
theorem run_currentTime_eq_of_all_arrivalTime_eq_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (hcurrent : state.currentTime = target)
    (harrival : ∀ job ∈ jobs, job.arrivalTime = target) :
    (runNonpreemptivePriorityArrivalTrace state jobs).currentTime = target := by
  induction jobs generalizing state with
  | nil => exact hcurrent
  | cons job jobs ih =>
      have hjob : job.arrivalTime = target := harrival job (by simp)
      have htarget : job.arrivalTime ≤ state.currentTime := by
        rw [hjob, hcurrent]
      have hadvance : advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs state) job.arrivalTime state = state := by
        cases totalNonpreemptivePriorityWorkJobs state <;>
          simp [advanceNonpreemptivePriorityWorkState, htarget]
      have hstep : advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs state) state job =
          admitNonpreemptivePriorityJob state job := by
        simp only [advanceThenAdmitNonpreemptivePriorityJob, hadvance]
      change (runNonpreemptivePriorityArrivalTrace
        (advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs state) state job) jobs).currentTime = target
      rw [hstep]
      apply ih
      · rw [admitNonpreemptivePriorityJob_currentTime]
        exact hcurrent
      · intro later hlater
        exact harrival later (by simp [hlater])

/-- If a chronological trace is extended by any finite batch of arrivals at
its queried horizon, its completion ledger at that horizon is exactly the
ledger obtained by advancing only the earlier trace to the horizon. -/
theorem completed_advance_run_append_of_all_arrivalTime_eq_target
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (hclock : (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ target)
    (harrival : ∀ job ∈ tail, job.arrivalTime = target) :
    (advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace initial (front ++ tail))) target
      (runNonpreemptivePriorityArrivalTrace initial (front ++ tail))).completed =
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace initial front)) target
        (runNonpreemptivePriorityArrivalTrace initial front)).completed := by
  cases tail with
  | nil => simp
  | cons job tail =>
      have hjob : job.arrivalTime = target := harrival job (by simp)
      let frontState := runNonpreemptivePriorityArrivalTrace initial front
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs frontState) target frontState
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadvancedClock : advanced.currentTime = target := by
        dsimp [advanced]
        exact advanceNonpreemptivePriorityWorkState_currentTime_eq_target
          (totalNonpreemptivePriorityWorkJobs frontState) target frontState (by
            simpa [frontState] using hclock) le_rfl
      have hadmittedClock : admitted.currentTime = target := by
        rw [show admitted.currentTime = advanced.currentTime by
          exact admitNonpreemptivePriorityJob_currentTime advanced job]
        exact hadvancedClock
      have htail : ∀ later ∈ tail, later.arrivalTime = target := by
        intro later hlater
        exact harrival later (by simp [hlater])
      have hrunClock :
          (runNonpreemptivePriorityArrivalTrace admitted tail).currentTime = target :=
        run_currentTime_eq_of_all_arrivalTime_eq_currentTime admitted tail target
          hadmittedClock htail
      have hrunCompleted :
          (runNonpreemptivePriorityArrivalTrace admitted tail).completed = admitted.completed :=
        completed_run_of_all_arrivalTime_eq_currentTime admitted tail target
          hadmittedClock htail
      have hadvanceFinal : advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace admitted tail)) target
          (runNonpreemptivePriorityArrivalTrace admitted tail) =
          runNonpreemptivePriorityArrivalTrace admitted tail := by
        cases totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace admitted tail) <;>
          simp [advanceNonpreemptivePriorityWorkState, hrunClock]
      have hsplit : runNonpreemptivePriorityArrivalTrace initial
          (front ++ job :: tail) =
          runNonpreemptivePriorityArrivalTrace admitted tail := by
        rw [runNonpreemptivePriorityArrivalTrace_append]
        simp only [runNonpreemptivePriorityArrivalTrace, List.foldl_cons,
          advanceThenAdmitNonpreemptivePriorityJob]
        rw [hjob]
        rfl
      rw [hsplit, hadvanceFinal, hrunCompleted,
        completed_admitNonpreemptivePriorityJob]

end

end AppliedModelingLib.Queueing
