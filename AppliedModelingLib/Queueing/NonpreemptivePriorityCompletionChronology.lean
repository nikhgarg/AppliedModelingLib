import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionTimes

/-!
# Chronological completion ledgers for finite priority traces

The finite nonpreemptive-priority execution prepends each new completion
record.  This module records the resulting timestamp order: the ledger is
newest-first, while its reverse is chronological.  The invariant is independent
of the priority rule and supports first-completion observations for tagged
jobs.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Completion records are stored newest first: each later list entry has a
timestamp no greater than the one before it. -/
def nonpreemptivePriorityCompletionLedgerChronological
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  state.completed.Pairwise (fun recent earlier => earlier.2 ≤ recent.2)

/-- Clearing an observational completion ledger makes its chronological
invariant immediate. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_clear
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityCompletionLedgerChronological
      (clearNonpreemptivePriorityCompletionLedger state) := by
  simp [nonpreemptivePriorityCompletionLedgerChronological,
    clearNonpreemptivePriorityCompletionLedger]

/-- Starting a queued job changes neither its completion ledger nor its
chronological order. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological state) :
    nonpreemptivePriorityCompletionLedgerChronological
      (startNextNonpreemptivePriorityJob state) := by
  simpa [nonpreemptivePriorityCompletionLedgerChronological,
    completed_startNextNonpreemptivePriorityJob] using hchronological

/-- Admitting an arrival does not alter the historical completion ledger. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological state) :
    nonpreemptivePriorityCompletionLedgerChronological
      (admitNonpreemptivePriorityJob state job) := by
  simpa [nonpreemptivePriorityCompletionLedgerChronological,
    completed_admitNonpreemptivePriorityJob] using hchronological

/-- Completing the active job prepends an entry at the current clock, so the
completion-time upper bound supplies the new chronological head relation. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological state) :
    nonpreemptivePriorityCompletionLedgerChronological
      (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [nonpreemptivePriorityCompletionLedgerChronological,
        completeNonpreemptivePriorityWorkJob, hactive] using hchronological
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed :=
          (active.1, state.currentTime) :: state.completed }
      have hafter : nonpreemptivePriorityCompletionLedgerChronological afterCompletion := by
        unfold nonpreemptivePriorityCompletionLedgerChronological
        apply List.pairwise_cons.mpr
        constructor
        · intro entry hentry
          exact htimes entry.1 entry.2 hentry
        · exact hchronological
      have hnext := nonpreemptivePriorityCompletionLedgerChronological_startNext
        afterCompletion hafter
      simpa [completeNonpreemptivePriorityWorkJob, afterCompletion, hactive] using hnext

/-- Bounded physical service preserves chronological completion records. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological state) :
    nonpreemptivePriorityCompletionLedgerChronological
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hchronological
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hchronological
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hchronological
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hchronological
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hchronological
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
              have hcompletedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime
                  completedState := by
                intro job completedAt hcompleted
                change completedAt ≤ state.currentTime + active.2
                have hbound : completedAt ≤ state.currentTime :=
                  htimes job completedAt (by simpa [completedState] using hcompleted)
                exact hbound.trans (by linarith [hwork.1 active hactive])
              have hnextWork : nonnegativeNonpreemptivePriorityResidualWork
                  (completeNonpreemptivePriorityWorkJob completedState) :=
                nonnegativeNonpreemptivePriorityResidualWork_complete completedState hcompletedWork
              have hnextTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime
                  (completeNonpreemptivePriorityWorkJob completedState) :=
                nonpreemptivePriorityCompletionTimesLeCurrentTime_complete
                  completedState hcompletedTimes
              have hnextChronological : nonpreemptivePriorityCompletionLedgerChronological
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                apply nonpreemptivePriorityCompletionLedgerChronological_complete
                  completedState hcompletedTimes
                simpa [nonpreemptivePriorityCompletionLedgerChronological,
                  completedState] using hchronological
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using
                ih (completeNonpreemptivePriorityWorkJob completedState)
                  hnextWork hnextTimes hnextChronological
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete] using hchronological

/-- A finite chronological arrival replay preserves the chronological
completion-ledger invariant. -/
theorem nonpreemptivePriorityCompletionLedgerChronological_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hchronological : nonpreemptivePriorityCompletionLedgerChronological initial)
    (hjobs : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonpreemptivePriorityCompletionLedgerChronological
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hchronological
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork htimes
      have hadvancedChronological : nonpreemptivePriorityCompletionLedgerChronological advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionLedgerChronological_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork htimes
          hchronological
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork (hjobs job (by simp))
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime admitted := by
        simpa [admitted] using nonpreemptivePriorityCompletionTimesLeCurrentTime_admit
          advanced job hadvancedTimes
      have hadmittedChronological : nonpreemptivePriorityCompletionLedgerChronological admitted := by
        simpa [admitted] using nonpreemptivePriorityCompletionLedgerChronological_admit
          advanced job hadvancedChronological
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using
        ih admitted hadmittedWork hadmittedTimes hadmittedChronological
          (fun other hother => hjobs other (by simp [hother]))

/-- In a time-sorted finite list, a successful `find?` returns a timestamp no
later than any other matching entry. -/
theorem list_find?_time_le_of_pairwise
    {α : Type*} (time : α → ℝ) (predicate : α → Bool)
    (entries : List α) (found target : α)
    (hsorted : entries.Pairwise (fun first second => time first ≤ time second))
    (hfind : entries.find? predicate = some found)
    (htarget : target ∈ entries) (hmatch : predicate target = true) :
    time found ≤ time target := by
  induction entries with
  | nil => simp at hfind
  | cons head tail ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      cases hheadPredicate : predicate head with
      | false =>
          have hfindTail : tail.find? predicate = some found := by
            simpa [List.find?_cons, hheadPredicate] using hfind
          have htargetTail : target ∈ tail := by
            rcases List.mem_cons.mp htarget with htarget | htarget
            · subst target
              simp [hheadPredicate] at hmatch
            · exact htarget
          exact ih htail hfindTail htargetTail
      | true =>
          have hfound : found = head := by
            have hheadFound : head = found := by
              simpa [List.find?_cons, hheadPredicate] using hfind
            exact hheadFound.symm
          subst found
          rcases List.mem_cons.mp htarget with htarget | htarget
          · subst target
            exact le_rfl
          · exact hhead target htarget

end

end AppliedModelingLib.Queueing
