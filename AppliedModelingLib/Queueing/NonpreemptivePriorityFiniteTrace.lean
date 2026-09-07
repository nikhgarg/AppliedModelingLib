import AppliedModelingLib.Queueing.NonpreemptivePriorityDynamics

/-!
# Finite nonpreemptive-priority queue traces

This module gives an executable deterministic queue semantics for a finite
trace of class-labelled jobs with real arrival times and processing work.  A
server always finishes its active job, then starts the earliest nonempty
priority class; jobs within one class are stored in FIFO order.  The model is
deliberately independent of any probability law.  It is the finite execution
layer used by a future remote-past stationary construction.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

noncomputable section

/-- A finite-trace customer, retaining its identifier, declared class,
physical arrival time, and required service work. -/
structure NonpreemptivePriorityJob (n : ℕ) (JobId : Type*) where
  identifier : JobId
  priority : Fin n
  arrivalTime : ℝ
  serviceWork : ℝ

/-- A work-level queue state.  The active pair stores the currently served
job and its residual work; `waiting` consists of one FIFO list per class; and
`completed` records each completed job with its physical completion time. -/
structure NonpreemptivePriorityWorkState (n : ℕ) (JobId : Type*) where
  currentTime : ℝ
  active : Option (NonpreemptivePriorityJob n JobId × ℝ)
  waiting : Fin n → List (NonpreemptivePriorityJob n JobId)
  completed : List (NonpreemptivePriorityJob n JobId × ℝ)

/-- Two finite trace states have the same live queue when they agree on the
physical clock, the job currently in service, and every class-FIFO list.  The
completion ledger is deliberately excluded: it records past observations but
does not affect any subsequent queue evolution. -/
def liveEquivalentNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId) : Prop :=
  first.currentTime = second.currentTime ∧
    first.active = second.active ∧ first.waiting = second.waiting

/-- The total number of waiting jobs. -/
def totalPriorityWaitingJobs
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : ℕ :=
  ∑ i, (state.waiting i).length

/-- The total number of jobs currently resident in the queue, including an
active job if one exists. -/
def totalNonpreemptivePriorityWorkJobs
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : ℕ :=
  (match state.active with | none => 0 | some _ => 1) +
    totalPriorityWaitingJobs state

/-- A waiting job exists in at least one priority class. -/
def hasPriorityWaitingJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∃ i, 0 < (state.waiting i).length

/-- The queue-state invariant that every waiting list contains jobs of its
declared priority class.  It rules out malformed externally supplied states
and is preserved by the admission operation below. -/
def hasClassConsistentWaiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∀ (i : Fin n) (job : NonpreemptivePriorityJob n JobId),
    job ∈ state.waiting i → job.priority = i

/-- The highest priority class with a waiting job. -/
noncomputable def nextPriorityWaitingClass
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwaiting : hasPriorityWaitingJob state) : Fin n :=
  nextNonpreemptivePriority (fun i => (state.waiting i).length) hwaiting

/-- Appending a job at the tail of its class-FIFO list. -/
noncomputable def enqueueNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  by
    classical
    exact { state with waiting := (Function.update state.waiting job.priority
      (state.waiting job.priority ++ [job])) }

/-- If the server is idle and work is waiting, start the head job of the
highest-priority nonempty class.  A busy server is left unchanged, which is
the nonpreemption condition. -/
noncomputable def startNextNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  by
    classical
    exact match state.active with
    | some _ => state
    | none =>
        if hwaiting : hasPriorityWaitingJob state then
          let i := nextPriorityWaitingClass state hwaiting
          match state.waiting i with
          | [] => state
          | job :: tail =>
              { state with
                active := some (job, job.serviceWork)
                waiting := Function.update state.waiting i tail }
        else state

/-- An arrival joins service immediately only when the server is idle after
starting any previously waiting work; otherwise it joins the tail of its own
class-FIFO list. -/
noncomputable def admitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  by
    classical
    let prepared := startNextNonpreemptivePriorityJob state
    exact match prepared.active with
    | none => { prepared with active := some (job, job.serviceWork) }
    | some _ => enqueueNonpreemptivePriorityJob prepared job

/-- Complete the active job at the current physical time and immediately
start the highest-priority waiting job, if one exists. -/
noncomputable def completeNonpreemptivePriorityWorkJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  by
    classical
    exact match state.active with
    | none => state
    | some (job, _) =>
        startNextNonpreemptivePriorityJob
          { state with active := none, completed := (job, state.currentTime) :: state.completed }

/-- Advance a finite queue state to a target time, processing at most `fuel`
service completions.  With enough fuel to cover the currently resident jobs,
this is the literal nonpreemptive service evolution up to that time. -/
noncomputable def advanceNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*} :
    ℕ → ℝ → NonpreemptivePriorityWorkState n JobId →
      NonpreemptivePriorityWorkState n JobId
  | 0, target, state =>
      if htarget : target ≤ state.currentTime then state
      else match state.active with
      | none => { state with currentTime := target }
      | some _ => state
  | fuel + 1, target, state =>
      if htarget : target ≤ state.currentTime then state
      else match state.active with
      | none => { state with currentTime := target }
      | some (job, residual) =>
          if hcomplete : residual ≤ target - state.currentTime then
            advanceNonpreemptivePriorityWorkState fuel target
              (completeNonpreemptivePriorityWorkJob
                { state with currentTime := state.currentTime + residual })
          else
            { state with
              currentTime := target
              active := some (job, residual - (target - state.currentTime)) }

/-- Admit one job at its stated time after processing the preceding service
evolution.  The caller supplies a fuel bound for jobs already resident before
the arrival; an arrival-sorted finite trace supplies such bounds inductively. -/
noncomputable def advanceThenAdmitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  admitNonpreemptivePriorityJob
    (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime state) job

/-- Execute a finite, chronologically supplied list of arrivals.  The list
order is the tie convention if two jobs are presented at the same epoch. -/
noncomputable def runNonpreemptivePriorityArrivalTrace
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    NonpreemptivePriorityWorkState n JobId :=
  jobs.foldl (fun state job =>
    advanceThenAdmitNonpreemptivePriorityJob
      (totalNonpreemptivePriorityWorkJobs state) state job) initial

/-- Executing a concatenated arrival list is exactly executing its prefix and
then continuing the suffix from the resulting queue state. -/
theorem runNonpreemptivePriorityArrivalTrace_append
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front suffix : List (NonpreemptivePriorityJob n JobId)) :
    runNonpreemptivePriorityArrivalTrace initial (front ++ suffix) =
      runNonpreemptivePriorityArrivalTrace
        (runNonpreemptivePriorityArrivalTrace initial front) suffix := by
  unfold runNonpreemptivePriorityArrivalTrace
  rw [List.foldl_append]

/-- The live-queue relation is reflexive. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_refl
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    liveEquivalentNonpreemptivePriorityWorkState state state := by
  exact ⟨rfl, rfl, rfl⟩

/-- Adding a waiting job respects the live queue relation. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_enqueue
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (enqueueNonpreemptivePriorityJob first job)
      (enqueueNonpreemptivePriorityJob second job) := by
  classical
  rcases first with ⟨firstTime, firstActive, firstWaiting, firstCompleted⟩
  rcases second with ⟨secondTime, secondActive, secondWaiting, secondCompleted⟩
  rcases hequivalent with ⟨htime, hactive, hwaiting⟩
  change firstTime = secondTime at htime
  change firstActive = secondActive at hactive
  change firstWaiting = secondWaiting at hwaiting
  subst secondTime
  subst secondActive
  subst secondWaiting
  exact ⟨rfl, rfl, rfl⟩

/-- Whether work is waiting depends only on the family of class-FIFO lists. -/
theorem hasPriorityWaitingJob_iff_of_waiting_eq
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hwaiting : first.waiting = second.waiting) :
    hasPriorityWaitingJob first ↔ hasPriorityWaitingJob second := by
  unfold hasPriorityWaitingJob
  simpa [hwaiting]

/-- The selected priority class depends only on the live waiting lists, not
on the completion ledger. -/
theorem nextPriorityWaitingClass_eq_of_waiting_eq
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hwaiting : first.waiting = second.waiting)
    (hfirst : hasPriorityWaitingJob first)
    (hsecond : hasPriorityWaitingJob second) :
    nextPriorityWaitingClass first hfirst = nextPriorityWaitingClass second hsecond := by
  unfold nextPriorityWaitingClass
  simp only [hwaiting]

/-- Selecting the next priority job depends only on the live queue. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_startNext
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (startNextNonpreemptivePriorityJob first)
      (startNextNonpreemptivePriorityJob second) := by
  classical
  rcases hequivalent with ⟨htime, hactive, hwaiting⟩
  cases hfirst : first.active with
  | some active =>
      have hsecond : second.active = some active := by
        rw [← hactive, hfirst]
      simpa [startNextNonpreemptivePriorityJob, hfirst, hsecond] using
        (show liveEquivalentNonpreemptivePriorityWorkState first second from
          ⟨htime, hactive, hwaiting⟩)
  | none =>
      have hsecond : second.active = none := by
        rw [← hactive, hfirst]
      by_cases hfirstWaiting : hasPriorityWaitingJob first
      · have hsecondWaiting : hasPriorityWaitingJob second :=
          (hasPriorityWaitingJob_iff_of_waiting_eq hwaiting).mp hfirstWaiting
        have hselected :
            nextPriorityWaitingClass first hfirstWaiting =
              nextPriorityWaitingClass second hsecondWaiting :=
          nextPriorityWaitingClass_eq_of_waiting_eq hwaiting hfirstWaiting hsecondWaiting
        cases hhead : first.waiting (nextPriorityWaitingClass first hfirstWaiting) with
        | nil =>
            have hheadSecond :
                second.waiting (nextPriorityWaitingClass second hsecondWaiting) = [] := by
              calc
                second.waiting (nextPriorityWaitingClass second hsecondWaiting) =
                    second.waiting (nextPriorityWaitingClass first hfirstWaiting) := by
                      rw [hselected]
                _ = first.waiting (nextPriorityWaitingClass first hfirstWaiting) := by
                      rw [hwaiting]
                _ = [] := hhead
            simp [startNextNonpreemptivePriorityJob, hfirst, hsecond,
              hfirstWaiting, hsecondWaiting, hhead, hheadSecond]
            exact ⟨htime, hactive, hwaiting⟩
        | cons job tail =>
            have hheadSecond :
                second.waiting (nextPriorityWaitingClass second hsecondWaiting) = job :: tail := by
              calc
                second.waiting (nextPriorityWaitingClass second hsecondWaiting) =
                    second.waiting (nextPriorityWaitingClass first hfirstWaiting) := by
                      rw [hselected]
                _ = first.waiting (nextPriorityWaitingClass first hfirstWaiting) := by
                      rw [hwaiting]
                _ = job :: tail := hhead
            simp [startNextNonpreemptivePriorityJob, hfirst, hsecond,
              hfirstWaiting, hsecondWaiting, hheadSecond, hselected,
              htime, hwaiting]
            exact ⟨rfl, rfl, by congr 1⟩
      · have hsecondWaiting : ¬ hasPriorityWaitingJob second := by
          intro hwaitingSecond
          exact hfirstWaiting
            ((hasPriorityWaitingJob_iff_of_waiting_eq hwaiting).mpr hwaitingSecond)
        simpa [startNextNonpreemptivePriorityJob, hfirst, hsecond,
          hfirstWaiting, hsecondWaiting] using
          (show liveEquivalentNonpreemptivePriorityWorkState first second from
            ⟨htime, hactive, hwaiting⟩)

/-- Admitting one common arrival respects the live queue relation. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_admit
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (admitNonpreemptivePriorityJob first job)
      (admitNonpreemptivePriorityJob second job) := by
  classical
  have hprepared := liveEquivalentNonpreemptivePriorityWorkState_startNext
    first second hequivalent
  cases hfirst : (startNextNonpreemptivePriorityJob first).active with
  | none =>
      have hsecond : (startNextNonpreemptivePriorityJob second).active = none := by
        rw [← hprepared.2.1, hfirst]
      unfold admitNonpreemptivePriorityJob
      dsimp
      rw [hfirst, hsecond]
      exact ⟨hprepared.1, rfl, hprepared.2.2⟩
  | some active =>
      have hsecond : (startNextNonpreemptivePriorityJob second).active = some active := by
        rw [← hprepared.2.1, hfirst]
      unfold admitNonpreemptivePriorityJob
      dsimp
      rw [hfirst, hsecond]
      exact liveEquivalentNonpreemptivePriorityWorkState_enqueue
        (startNextNonpreemptivePriorityJob first)
        (startNextNonpreemptivePriorityJob second) job hprepared

/-- Completing the common active job and selecting the next job respects the
live queue relation, regardless of the two completion-ledger histories. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_complete
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (completeNonpreemptivePriorityWorkJob first)
      (completeNonpreemptivePriorityWorkJob second) := by
  classical
  rcases hequivalent with ⟨htime, hactive, hwaiting⟩
  cases hfirst : first.active with
  | none =>
      have hsecond : second.active = none := by
        rw [← hactive, hfirst]
      simpa [completeNonpreemptivePriorityWorkJob, hfirst, hsecond] using
        (show liveEquivalentNonpreemptivePriorityWorkState first second from
          ⟨htime, hactive, hwaiting⟩)
  | some active =>
      have hsecond : second.active = some active := by
        rw [← hactive, hfirst]
      unfold completeNonpreemptivePriorityWorkJob
      rw [hfirst, hsecond]
      apply liveEquivalentNonpreemptivePriorityWorkState_startNext
      exact ⟨htime, rfl, hwaiting⟩

/-- Bounded nonpreemptive service evolution depends only on the live queue. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (first second : NonpreemptivePriorityWorkState n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState fuel target first)
      (advanceNonpreemptivePriorityWorkState fuel target second) := by
  induction fuel generalizing first second with
  | zero =>
      rcases hequivalent with ⟨htime, hactive, hwaiting⟩
      by_cases htarget : target ≤ first.currentTime
      · have htargetSecond : target ≤ second.currentTime := by
          rwa [← htime]
        simpa [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond] using
          (show liveEquivalentNonpreemptivePriorityWorkState first second from
            ⟨htime, hactive, hwaiting⟩)
      · have htargetSecond : ¬ target ≤ second.currentTime := by
          simpa [htime] using htarget
        cases hfirst : first.active with
        | none =>
            have hsecond : second.active = none := by
              rw [← hactive, hfirst]
            simp [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond,
              hfirst, hsecond, liveEquivalentNonpreemptivePriorityWorkState, hwaiting]
        | some active =>
            have hsecond : second.active = some active := by
              rw [← hactive, hfirst]
            simpa [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond,
              hfirst, hsecond] using
              (show liveEquivalentNonpreemptivePriorityWorkState first second from
                ⟨htime, hactive, hwaiting⟩)
  | succ fuel ih =>
      rcases hequivalent with ⟨htime, hactive, hwaiting⟩
      by_cases htarget : target ≤ first.currentTime
      · have htargetSecond : target ≤ second.currentTime := by
          rwa [← htime]
        simpa [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond] using
          (show liveEquivalentNonpreemptivePriorityWorkState first second from
            ⟨htime, hactive, hwaiting⟩)
      · have htargetSecond : ¬ target ≤ second.currentTime := by
          simpa [htime] using htarget
        cases hfirst : first.active with
        | none =>
            have hsecond : second.active = none := by
              rw [← hactive, hfirst]
            simp [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond,
              hfirst, hsecond, liveEquivalentNonpreemptivePriorityWorkState, hwaiting]
        | some active =>
            have hsecond : second.active = some active := by
              rw [← hactive, hfirst]
            by_cases hcomplete : active.2 ≤ target - first.currentTime
            · have hcompleteSecond : active.2 ≤ target - second.currentTime := by
                rwa [← htime]
              have hcompleted :
                  liveEquivalentNonpreemptivePriorityWorkState
                    (completeNonpreemptivePriorityWorkJob
                      { first with currentTime := first.currentTime + active.2 })
                    (completeNonpreemptivePriorityWorkJob
                      { second with currentTime := second.currentTime + active.2 }) := by
                apply liveEquivalentNonpreemptivePriorityWorkState_complete
                exact ⟨by linarith, hactive, hwaiting⟩
              simpa [advanceNonpreemptivePriorityWorkState, htarget, htargetSecond,
                hfirst, hsecond, hcomplete, hcompleteSecond] using ih _ _ hcompleted
            · have hcompleteSecond : ¬ active.2 ≤ target - second.currentTime := by
                simpa [htime] using hcomplete
              simp [advanceNonpreemptivePriorityWorkState, htargetSecond,
                hfirst, hsecond, hcompleteSecond,
                liveEquivalentNonpreemptivePriorityWorkState, htime, hwaiting]

/-- Live-equivalent states have the same number of resident jobs, so the
finite completion-fuel bound chosen by a trace is history-independent. -/
theorem totalNonpreemptivePriorityWorkJobs_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    totalNonpreemptivePriorityWorkJobs first = totalNonpreemptivePriorityWorkJobs second := by
  unfold totalNonpreemptivePriorityWorkJobs totalPriorityWaitingJobs
  rw [hequivalent.2.1, hequivalent.2.2]

/-- Advancing to, and admitting, one common physical arrival respects the
live queue relation. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_advanceThenAdmit
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (first second : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceThenAdmitNonpreemptivePriorityJob fuel first job)
      (advanceThenAdmitNonpreemptivePriorityJob fuel second job) := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  apply liveEquivalentNonpreemptivePriorityWorkState_admit
  exact liveEquivalentNonpreemptivePriorityWorkState_advance fuel job.arrivalTime
    first second hequivalent

/-- Two traces fed the same ordered arrivals evolve through the same live
queue, even when their completion ledgers record different earlier history. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_run
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (runNonpreemptivePriorityArrivalTrace first jobs)
      (runNonpreemptivePriorityArrivalTrace second jobs) := by
  induction jobs generalizing first second with
  | nil =>
      simpa [runNonpreemptivePriorityArrivalTrace] using hequivalent
  | cons job jobs ih =>
      have hcount : totalNonpreemptivePriorityWorkJobs first =
          totalNonpreemptivePriorityWorkJobs second :=
        totalNonpreemptivePriorityWorkJobs_eq_of_liveEquivalent hequivalent
      have hnext := liveEquivalentNonpreemptivePriorityWorkState_advanceThenAdmit
        (totalNonpreemptivePriorityWorkJobs first) first second job hequivalent
      have hnext' : liveEquivalentNonpreemptivePriorityWorkState
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs first) first job)
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs second) second job) := by
        rw [← hcount]
        exact hnext
      simpa [runNonpreemptivePriorityArrivalTrace] using ih _ _ hnext'

/-- Common future arrivals followed by common bounded service preserve live
queue equivalence. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_runThenAdvance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (first second : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState
      (advanceNonpreemptivePriorityWorkState fuel target
        (runNonpreemptivePriorityArrivalTrace first jobs))
      (advanceNonpreemptivePriorityWorkState fuel target
        (runNonpreemptivePriorityArrivalTrace second jobs)) := by
  apply liveEquivalentNonpreemptivePriorityWorkState_advance
  exact liveEquivalentNonpreemptivePriorityWorkState_run first second jobs hequivalent

/-- The live-queue relation is symmetric. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_symm
    {n : ℕ} {JobId : Type*}
    {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    liveEquivalentNonpreemptivePriorityWorkState second first := by
  exact ⟨hequivalent.1.symm, hequivalent.2.1.symm, hequivalent.2.2.symm⟩

/-- The live-queue relation is transitive. -/
theorem liveEquivalentNonpreemptivePriorityWorkState_trans
    {n : ℕ} {JobId : Type*}
    {first second third : NonpreemptivePriorityWorkState n JobId}
    (hfirst : liveEquivalentNonpreemptivePriorityWorkState first second)
    (hsecond : liveEquivalentNonpreemptivePriorityWorkState second third) :
    liveEquivalentNonpreemptivePriorityWorkState first third := by
  exact ⟨hfirst.1.trans hsecond.1, hfirst.2.1.trans hsecond.2.1,
    hfirst.2.2.trans hsecond.2.2⟩

/-- A completion never changes the physical time itself. -/
theorem completeNonpreemptivePriorityWorkJob_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    (completeNonpreemptivePriorityWorkJob state).currentTime = state.currentTime := by
  classical
  unfold completeNonpreemptivePriorityWorkJob
  split
  · rfl
  · unfold startNextNonpreemptivePriorityJob
    dsimp
    split
    · split <;> rfl
    · rfl

/-- Selecting a waiting job changes neither the physical clock nor the
completed-job ledger time. -/
theorem startNextNonpreemptivePriorityJob_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    (startNextNonpreemptivePriorityJob state).currentTime = state.currentTime := by
  classical
  unfold startNextNonpreemptivePriorityJob
  dsimp
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- Admission preserves the physical clock. -/
theorem admitNonpreemptivePriorityJob_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (admitNonpreemptivePriorityJob state job).currentTime = state.currentTime := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : prepared.currentTime = state.currentTime := by
    simpa [prepared] using startNextNonpreemptivePriorityJob_currentTime state
  cases hactive : prepared.active with
  | none =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hprepared
  | some active =>
      have houtput :
          (admitNonpreemptivePriorityJob state job).currentTime = prepared.currentTime := by
        simp [admitNonpreemptivePriorityJob, prepared, hactive,
          enqueueNonpreemptivePriorityJob]
      exact houtput.trans hprepared

/-- Service evolution cannot move the clock beyond a common upper bound that
already bounds both the input state and the requested target time. -/
theorem advanceNonpreemptivePriorityWorkState_currentTime_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target bound : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hstate : state.currentTime ≤ bound) (htarget : target ≤ bound) :
    (advanceNonpreemptivePriorityWorkState fuel target state).currentTime ≤ bound := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htargetState : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htargetState] using hstate
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htargetState, hactive] using htarget
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htargetState, hactive] using hstate
  | succ fuel ih =>
      classical
      by_cases htargetState : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htargetState] using hstate
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htargetState, hactive] using htarget
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAt : completedAt.currentTime ≤ bound := by
                dsimp [completedAt]
                linarith
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt)
                (by
                  rw [completeNonpreemptivePriorityWorkJob_currentTime]
                  exact hcompletedAt)
              simpa [advanceNonpreemptivePriorityWorkState, htargetState, hactive,
                hcomplete, completedAt] using hind
            · simpa [advanceNonpreemptivePriorityWorkState, htargetState, hactive,
                hcomplete] using htarget

/-- Advancing to an arrival and admitting it cannot move a queue clock beyond
an upper bound shared by the old state and that arrival epoch. -/
theorem advanceThenAdmitNonpreemptivePriorityJob_currentTime_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (bound : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hstate : state.currentTime ≤ bound) (hjob : job.arrivalTime ≤ bound) :
    (advanceThenAdmitNonpreemptivePriorityJob fuel state job).currentTime ≤ bound := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [admitNonpreemptivePriorityJob_currentTime]
  exact advanceNonpreemptivePriorityWorkState_currentTime_le
    fuel job.arrivalTime bound state hstate hjob

/-- A finite arrival trace remains before any upper bound that contains its
initial clock and every presented arrival epoch. -/
theorem runNonpreemptivePriorityArrivalTrace_currentTime_le
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (bound : ℝ)
    (hinitial : initial.currentTime ≤ bound)
    (hjobs : ∀ job ∈ jobs, job.arrivalTime ≤ bound) :
    (runNonpreemptivePriorityArrivalTrace initial jobs).currentTime ≤ bound := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hinitial
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : admitted.currentTime ≤ bound := by
        simp only [admitted]
        apply advanceThenAdmitNonpreemptivePriorityJob_currentTime_le
        · exact hinitial
        · exact hjobs job (by simp)
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted (fun other hother => hjobs other (by simp [hother]))

/-- Regression law for an idle first arrival: an empty-fuel advance still
places the clock at the arrival's physical epoch before that job is admitted. -/
theorem runNonpreemptivePriorityArrivalTrace_singleton_idle_currentTime
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hactive : state.active = none)
    (htime : state.currentTime ≤ job.arrivalTime) :
    (runNonpreemptivePriorityArrivalTrace state [job]).currentTime = job.arrivalTime := by
  unfold runNonpreemptivePriorityArrivalTrace
  simp only [List.foldl_cons, List.foldl_nil]
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [admitNonpreemptivePriorityJob_currentTime]
  by_cases heq : state.currentTime = job.arrivalTime
  · cases hfuel : totalNonpreemptivePriorityWorkJobs state with
    | zero => simp [advanceNonpreemptivePriorityWorkState, heq]
    | succ fuel => simp [advanceNonpreemptivePriorityWorkState, heq]
  · have hlt : state.currentTime < job.arrivalTime := lt_of_le_of_ne htime heq
    cases hfuel : totalNonpreemptivePriorityWorkJobs state with
    | zero =>
        simp [advanceNonpreemptivePriorityWorkState, not_le_of_gt hlt, hactive]
    | succ fuel =>
        simp [advanceNonpreemptivePriorityWorkState, not_le_of_gt hlt, hactive]

/-- Enqueuing at a class tail raises that class's waiting count by one. -/
theorem enqueueNonpreemptivePriorityJob_waiting_selected
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (enqueueNonpreemptivePriorityJob state job).waiting job.priority =
      state.waiting job.priority ++ [job] := by
  classical
  simp [enqueueNonpreemptivePriorityJob]

/-- Enqueuing at one class leaves every other class-FIFO list unchanged. -/
theorem enqueueNonpreemptivePriorityJob_waiting_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hi : i ≠ job.priority) :
    (enqueueNonpreemptivePriorityJob state job).waiting i = state.waiting i := by
  classical
  simp [enqueueNonpreemptivePriorityJob, hi]

/-- Tail admission preserves the invariant that a class-FIFO list contains
only jobs of its declared class. -/
theorem hasClassConsistentWaiting_enqueueNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state) :
    hasClassConsistentWaiting (enqueueNonpreemptivePriorityJob state job) := by
  intro i other hmember
  by_cases hi : i = job.priority
  · subst i
    rw [enqueueNonpreemptivePriorityJob_waiting_selected] at hmember
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with hmember | hmember
    · exact hclass job.priority other hmember
    · subst other
      rfl
  · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state job i hi] at hmember
    exact hclass i other hmember

/-- Starting the next job only removes a FIFO head, so it preserves
class-consistent waiting lists. -/
theorem hasClassConsistentWaiting_startNextNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hclass : hasClassConsistentWaiting state) :
    hasClassConsistentWaiting (startNextNonpreemptivePriorityJob state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hclass
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
              using hclass
        | cons head tail =>
            intro i other hmember
            by_cases hi : i = selected
            · subst i
              simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                selected, hhead, Function.update_self] at hmember
              exact hclass selected other (by
                rw [hhead]
                exact List.mem_cons_of_mem _ hmember)
            · simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hwaiting,
                selected, hhead, Function.update_of_ne hi] at hmember
              exact hclass i other hmember
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hclass

/-- Completing a job and selecting the next one preserves class-consistent
waiting lists. -/
theorem hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hclass : hasClassConsistentWaiting state) :
    hasClassConsistentWaiting (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hclass
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : hasClassConsistentWaiting afterCompletion := by
        simpa [afterCompletion] using hclass
      have hnext := hasClassConsistentWaiting_startNextNonpreemptivePriorityJob
        afterCompletion hafter
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hnext

/-- Admission preserves class-consistent waiting lists, whether the arrival
starts service immediately or joins its class FIFO tail. -/
theorem hasClassConsistentWaiting_admitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state) :
    hasClassConsistentWaiting (admitNonpreemptivePriorityJob state job) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : hasClassConsistentWaiting prepared := by
    simpa [prepared] using
      hasClassConsistentWaiting_startNextNonpreemptivePriorityJob state hclass
  cases hactive : prepared.active with
  | none =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hprepared
  | some active =>
      have henqueued := hasClassConsistentWaiting_enqueueNonpreemptivePriorityJob
        prepared job hprepared
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using henqueued

/-- Finite service evolution preserves the class-list invariant at every
completion and partial-service branch. -/
theorem hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hclass : hasClassConsistentWaiting state) :
    hasClassConsistentWaiting
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hclass
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hclass
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hclass
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hclass
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hclass
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · have hstep := hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
                { state with currentTime := state.currentTime + active.2 } (by
                  simpa using hclass)
              have hind := ih
                (completeNonpreemptivePriorityWorkJob
                  { state with currentTime := state.currentTime + active.2 }) hstep
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                using hind
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                using hclass

/-- A chronologically supplied finite arrival trace never creates a job in an
incorrect class-FIFO list. -/
theorem hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hclass : hasClassConsistentWaiting initial) :
    hasClassConsistentWaiting
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hclass
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hclass
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob advanced job hadvanced
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted

/-- The selected next class is no lower priority than every nonempty waiting
class. -/
theorem nextPriorityWaitingClass_le_of_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwaiting : hasPriorityWaitingJob state) (i : Fin n)
    (hi : 0 < (state.waiting i).length) :
    nextPriorityWaitingClass state hwaiting ≤ i := by
  exact nextNonpreemptivePriority_le_of_positive
    (fun j => (state.waiting j).length) hwaiting i hi

/-- If a service completion leaves waiting jobs, the newly active job comes
from a class no lower priority than every class that was waiting at that
completion instant. -/
theorem completeNonpreemptivePriorityWorkJob_selected_le_of_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active)
    (hwaiting : hasPriorityWaitingJob state)
    (hclass : hasClassConsistentWaiting state) (i : Fin n)
    (hi : 0 < (state.waiting i).length) :
    ∃ job residual,
      (completeNonpreemptivePriorityWorkJob state).active = some (job, residual) ∧
        job.priority ≤ i := by
  let selected := nextPriorityWaitingClass state hwaiting
  have hselected : 0 < (state.waiting selected).length := by
    exact nextNonpreemptivePriority_positive
      (fun j => (state.waiting j).length) hwaiting
  cases hhead : state.waiting selected with
  | nil => simp [hhead] at hselected
  | cons job tail =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafterWaiting : hasPriorityWaitingJob afterCompletion := by
        simpa [afterCompletion] using hwaiting
      let next := nextPriorityWaitingClass afterCompletion hafterWaiting
      have hnext : next = selected := by
        simp [next, selected, nextPriorityWaitingClass, afterCompletion]
      have hafterHead : afterCompletion.waiting next = job :: tail := by
        simpa [afterCompletion, hnext] using hhead
      have hjobclass : job.priority = selected :=
        hclass selected job (by simp [hhead])
      refine ⟨job, job.serviceWork, ?_, ?_⟩
      · simp only [completeNonpreemptivePriorityWorkJob, hactive]
        change (startNextNonpreemptivePriorityJob afterCompletion).active =
          some (job, job.serviceWork)
        have hcanonicalHead :
            afterCompletion.waiting
                (nextPriorityWaitingClass afterCompletion hafterWaiting) = job :: tail := by
          simpa [next] using hafterHead
        unfold startNextNonpreemptivePriorityJob
        dsimp only
        rw [dif_pos hafterWaiting]
        rw [hcanonicalHead]
      · rw [hjobclass]
        exact nextPriorityWaitingClass_le_of_waiting state hwaiting i hi

end

end AppliedModelingLib.Queueing
