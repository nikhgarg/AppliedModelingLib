import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionTimes
import AppliedModelingLib.Queueing.NonpreemptivePriorityFifoPredecessors
import AppliedModelingLib.Queueing.NonpreemptivePriorityTraceProvenance

/-!
# Completion order for finite nonpreemptive-priority queues

This module strengthens the class-FIFO position invariant with the temporal
facts needed to reason about literal completion records.  The initial API is
generic: it makes no reference to a particular stochastic input process or
tagged-customer construction.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- A job that is active and also appears in a class waiting list has at least
two occurrences in the live-plus-completed multiplicity ledger. -/
theorem one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_mem_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (residual : ℝ) (i : Fin n)
    (hactive : state.active = some (job, residual))
    (hwaiting : job ∈ state.waiting i) :
    1 < nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  have hactiveExists : ∃ residual, state.active = some (job, residual) :=
    ⟨residual, hactive⟩
  have hcount : 1 ≤ (state.waiting i).count job :=
    List.count_pos_iff.mpr hwaiting
  have hsum : (state.waiting i).count job ≤ ∑ j, (state.waiting j).count job := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun j => (state.waiting j).count job)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [nonpreemptivePriorityWorkStateJobMultiplicity, if_pos hactiveExists]
  omega

/-- A later customer cannot be both active and still after another customer
in the same FIFO list when its literal multiplicity is at most one. -/
theorem not_nonpreemptivePriorityFifoPrecedes_of_active_eq_later_of_multiplicity_le_one
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (later, residual))
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state later ≤ 1) :
    ¬ nonpreemptivePriorityFifoPrecedes state earlier later := by
  intro hprecedes
  rcases hprecedes with ⟨_, front, middle, suffix, hwaiting⟩
  have hlaterWaiting : later ∈ state.waiting later.priority := by
    rw [hwaiting]
    simp
  have htwo := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_mem_waiting
    state later residual later.priority hactive hlaterWaiting
  omega

/-- The completion-order consequence of a same-class FIFO predecessor: every
recorded completion of the later job has an earlier-or-simultaneous completion
record for the predecessor. -/
def nonpreemptivePriorityFifoCompletionOrder
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) : Prop :=
  ∀ laterTime, (later, laterTime) ∈ state.completed →
    ∃ earlierTime, (earlier, earlierTime) ∈ state.completed ∧ earlierTime ≤ laterTime

/-- Completing a queue state preserves FIFO completion order, provided the
later literal job has at most one occurrence.  The only new ledger record is
the active job; FIFO disposition and the ledger time bound rule out that new
record being the later customer before its predecessor has completed. -/
theorem nonpreemptivePriorityFifoCompletionOrder_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdistinct : earlier ≠ later)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state later ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      (completeNonpreemptivePriorityWorkJob state) earlier later := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using horder
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
      intro laterTime hlater
      rw [hledger] at hlater
      rcases List.mem_cons.mp hlater with hnew | hold
      · have hactiveJob : active.1 = later := by
          exact (congrArg Prod.fst hnew).symm
        have htime : laterTime = state.currentTime := by
          exact congrArg Prod.snd hnew
        have hactiveLater : state.active = some (later, active.2) := by
          have hpair : active = (later, active.2) := by
            exact Prod.ext hactiveJob rfl
          rw [hactive, hpair]
        rcases hdisposition with hprecedes | hearlierActive | hearlierCompleted
        · exact (not_nonpreemptivePriorityFifoPrecedes_of_active_eq_later_of_multiplicity_le_one
            state earlier later active.2 hactiveLater hmultiplicity hprecedes).elim
        · rcases hearlierActive with ⟨earlierResidual, hearlierActive⟩
          have heq : earlier = later := by
            have hpairs : (earlier, earlierResidual) = (later, active.2) :=
              Option.some.inj (hearlierActive.symm.trans hactiveLater)
            exact congrArg Prod.fst hpairs
          exact (hdistinct heq).elim
        · rcases hearlierCompleted with ⟨earlierTime, hearlierCompleted⟩
          refine ⟨earlierTime, ?_, ?_⟩
          · exact mem_completed_completeNonpreemptivePriorityWorkJob
              state earlier earlierTime hearlierCompleted
          · rw [htime]
            exact htimes earlier earlierTime hearlierCompleted
      · rcases horder laterTime hold with ⟨earlierTime, hearlierCompleted, htime⟩
        exact ⟨earlierTime,
          mem_completed_completeNonpreemptivePriorityWorkJob
            state earlier earlierTime hearlierCompleted,
          htime⟩

/-- Updating only the physical clock leaves FIFO completion-order facts
unchanged because the completion ledger itself is unchanged. -/
theorem nonpreemptivePriorityFifoCompletionOrder_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) (time : ℝ)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      { state with currentTime := time } earlier later := by
  simpa [nonpreemptivePriorityFifoCompletionOrder] using horder

/-- Selecting a waiting job does not alter FIFO completion-order facts. -/
theorem nonpreemptivePriorityFifoCompletionOrder_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      (startNextNonpreemptivePriorityJob state) earlier later := by
  intro laterTime hlater
  rcases horder laterTime (by
    simpa [completed_startNextNonpreemptivePriorityJob] using hlater) with
    ⟨earlierTime, hearlier, htime⟩
  exact ⟨earlierTime, by
    simpa [completed_startNextNonpreemptivePriorityJob] using hearlier, htime⟩

/-- Tail arrival leaves FIFO completion-order facts unchanged. -/
theorem nonpreemptivePriorityFifoCompletionOrder_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later newJob : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      (enqueueNonpreemptivePriorityJob state newJob) earlier later := by
  simpa [nonpreemptivePriorityFifoCompletionOrder,
    enqueueNonpreemptivePriorityJob] using horder

/-- Admission leaves FIFO completion-order facts unchanged because it records
no service completion. -/
theorem nonpreemptivePriorityFifoCompletionOrder_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later newJob : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      (admitNonpreemptivePriorityJob state newJob) earlier later := by
  intro laterTime hlater
  rcases horder laterTime (by
    simpa [completed_admitNonpreemptivePriorityJob] using hlater) with
    ⟨earlierTime, hearlier, htime⟩
  exact ⟨earlierTime, by
    simpa [completed_admitNonpreemptivePriorityJob] using hearlier, htime⟩

/-- Bounded service evolution preserves the completion order of two distinct
same-class FIFO customers.  A completed predecessor remains recorded, and a
new later-job completion can occur only after the predecessor's record has
been created. -/
theorem nonpreemptivePriorityFifoCompletionOrder_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdistinct : earlier ≠ later)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state later ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later)
    (horder : nonpreemptivePriorityFifoCompletionOrder state earlier later) :
    nonpreemptivePriorityFifoCompletionOrder
      (advanceNonpreemptivePriorityWorkState fuel target state) earlier later := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using horder
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityFifoCompletionOrder_timeUpdate
                state earlier later target horder
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using horder
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using horder
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityFifoCompletionOrder_timeUpdate
                state earlier later target horder
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
              have hcompletedMultiplicity :
                  nonpreemptivePriorityWorkStateJobMultiplicity completedState later ≤ 1 := by
                simpa [completedState] using hmultiplicity
              have hcompletedTimes :
                  nonpreemptivePriorityCompletionTimesLeCurrentTime completedState := by
                intro job completedAt hcompleted
                change completedAt ≤ state.currentTime + active.2
                have hbound : completedAt ≤ state.currentTime :=
                  htimes job completedAt (by simpa [completedState] using hcompleted)
                have hresidual : 0 ≤ active.2 := hwork.1 active hactive
                linarith
              have hcompletedDisposition :
                  nonpreemptivePriorityFifoPrecedesDisposition completedState earlier later := by
                simpa [completedState] using
                  nonpreemptivePriorityFifoPrecedesDisposition_timeUpdate
                    state earlier later (state.currentTime + active.2) hdisposition
              have hcompletedOrder :
                  nonpreemptivePriorityFifoCompletionOrder completedState earlier later := by
                simpa [completedState] using
                  nonpreemptivePriorityFifoCompletionOrder_timeUpdate
                    state earlier later (state.currentTime + active.2) horder
              let next := completeNonpreemptivePriorityWorkJob completedState
              have hnextWork : nonnegativeNonpreemptivePriorityResidualWork next := by
                dsimp [next]
                exact nonnegativeNonpreemptivePriorityResidualWork_complete
                  completedState hcompletedWork
              have hnextMultiplicity :
                  nonpreemptivePriorityWorkStateJobMultiplicity next later ≤ 1 := by
                dsimp [next]
                rw [nonpreemptivePriorityWorkStateJobMultiplicity_complete]
                exact hcompletedMultiplicity
              have hnextTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime next := by
                dsimp [next]
                exact nonpreemptivePriorityCompletionTimesLeCurrentTime_complete
                  completedState hcompletedTimes
              have hnextDisposition :
                  nonpreemptivePriorityFifoPrecedesDisposition next earlier later := by
                dsimp [next]
                exact nonpreemptivePriorityFifoPrecedesDisposition_complete
                  completedState earlier later hcompletedDisposition
              have hnextOrder : nonpreemptivePriorityFifoCompletionOrder next earlier later := by
                dsimp [next]
                exact nonpreemptivePriorityFifoCompletionOrder_complete
                  completedState earlier later hdistinct hcompletedMultiplicity hcompletedTimes
                  hcompletedDisposition hcompletedOrder
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState, next] using
                ih next hnextWork hnextMultiplicity hnextTimes hnextDisposition hnextOrder
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
                nonpreemptivePriorityFifoCompletionOrder_timeUpdate
                  state earlier later target horder

/-- A finite arrival replay preserves completion order for two distinct FIFO
customers when none of its literal arrivals duplicates the later customer. -/
theorem nonpreemptivePriorityFifoCompletionOrder_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdistinct : earlier ≠ later)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial later ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition initial earlier later)
    (horder : nonpreemptivePriorityFifoCompletionOrder initial earlier later)
    (hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork)
    (hjobsDistinct : ∀ job ∈ jobs, job ≠ later) :
    nonpreemptivePriorityFifoCompletionOrder
      (runNonpreemptivePriorityArrivalTrace initial jobs) earlier later := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using horder
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadvancedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity advanced later ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity advanced later =
            nonpreemptivePriorityWorkStateJobMultiplicity initial later by
          dsimp [advanced]
          exact nonpreemptivePriorityWorkStateJobMultiplicity_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial later]
        exact hmultiplicity
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork htimes
      have hadvancedDisposition :
          nonpreemptivePriorityFifoPrecedesDisposition advanced earlier later := by
        simpa [advanced] using nonpreemptivePriorityFifoPrecedesDisposition_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
          earlier later hdisposition
      have hadvancedOrder : nonpreemptivePriorityFifoCompletionOrder advanced earlier later := by
        simpa [advanced] using nonpreemptivePriorityFifoCompletionOrder_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial earlier later
          hdistinct hwork hmultiplicity htimes hdisposition horder
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hjobWork : 0 ≤ job.serviceWork := hjobsWork job (by simp)
      have hjobDistinct : job ≠ later := hjobsDistinct job (by simp)
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork hjobWork
      have hadmittedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity admitted later ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity admitted later =
            nonpreemptivePriorityWorkStateJobMultiplicity advanced later by
          dsimp [admitted]
          exact nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne
            advanced job later hjobDistinct]
        exact hadvancedMultiplicity
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime admitted := by
        simpa [admitted] using
          nonpreemptivePriorityCompletionTimesLeCurrentTime_admit advanced job hadvancedTimes
      have hadmittedDisposition :
          nonpreemptivePriorityFifoPrecedesDisposition admitted earlier later := by
        simpa [admitted] using nonpreemptivePriorityFifoPrecedesDisposition_admit
          advanced earlier later job hadvancedDisposition
      have hadmittedOrder : nonpreemptivePriorityFifoCompletionOrder admitted earlier later := by
        simpa [admitted] using nonpreemptivePriorityFifoCompletionOrder_admit
          advanced earlier later job hadvancedOrder
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using
        ih admitted hadmittedWork hadmittedMultiplicity hadmittedTimes
          hadmittedDisposition hadmittedOrder
          (fun other hother => hjobsWork other (by simp [hother]))
          (fun other hother => hjobsDistinct other (by simp [hother]))

/-- In a no-duplicate arrival trace, a same-class customer already present at
the initial epoch completes no later than any distinct later input customer.
The proof isolates the exact admission at which the later record first enters
the queue, where its completion ledger is still empty, and then reuses the
generic completion-order preservation theorem for the remaining suffix. -/
theorem nonpreemptivePriorityFifoCompletionOrder_run_of_initial_contains
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting initial)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hearlier : nonpreemptivePriorityWorkStateContainsJob initial earlier)
    (hnotlater : ¬ nonpreemptivePriorityWorkStateContainsJob initial later)
    (hnodup : jobs.Nodup)
    (hlater : later ∈ jobs)
    (hpriority : earlier.priority = later.priority)
    (hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonpreemptivePriorityFifoCompletionOrder
      (runNonpreemptivePriorityArrivalTrace initial jobs) earlier later := by
  induction jobs generalizing initial with
  | nil => simp at hlater
  | cons newJob jobs ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hheadNodup, htailNodup⟩
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hnewWork : 0 ≤ newJob.serviceWork := hjobsWork newJob (by simp)
      have hadvancedClass : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial hclass
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial hwork
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial hwork htimes
      have hadvancedEarlier : nonpreemptivePriorityWorkStateContainsJob advanced earlier := by
        simpa [advanced] using nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial earlier hearlier
      have hadvancedNotLater : ¬ nonpreemptivePriorityWorkStateContainsJob advanced later := by
        intro hcontains
        apply hnotlater
        exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial later hcontains
      have hadmittedClass : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob
            advanced newJob hadvancedClass
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced newJob hadvancedWork hnewWork
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime admitted := by
        simpa [admitted] using
          nonpreemptivePriorityCompletionTimesLeCurrentTime_admit advanced newJob hadvancedTimes
      have hadmittedEarlier : nonpreemptivePriorityWorkStateContainsJob admitted earlier := by
        simpa [admitted] using nonpreemptivePriorityWorkStateContainsJob_admit
          advanced newJob earlier hadvancedEarlier
      rcases List.mem_cons.mp hlater with hnew | htail
      · subst newJob
        have hdistinct : earlier ≠ later := by
          intro heq
          subst earlier
          exact hnotlater hearlier
        have hadmittedDisposition :
            nonpreemptivePriorityFifoPrecedesDisposition admitted earlier later := by
          simpa [admitted] using
            nonpreemptivePriorityFifoPrecedesDisposition_admit_of_contains
              advanced earlier later hadvancedClass hpriority hadvancedEarlier
        have hadmittedOrder : nonpreemptivePriorityFifoCompletionOrder admitted earlier later := by
          intro laterTime hlaterCompleted
          rw [completed_admitNonpreemptivePriorityJob] at hlaterCompleted
          exact (hadvancedNotLater (Or.inr (Or.inr ⟨laterTime, hlaterCompleted⟩))).elim
        have hadmittedMultiplicity :
            nonpreemptivePriorityWorkStateJobMultiplicity admitted later ≤ 1 := by
          have hzero : nonpreemptivePriorityWorkStateJobMultiplicity advanced later = 0 :=
            nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
              advanced later hadvancedNotLater
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity admitted later =
              nonpreemptivePriorityWorkStateJobMultiplicity advanced later + 1 by
            simpa [admitted] using
              nonpreemptivePriorityWorkStateJobMultiplicity_admit_self advanced later,
            hzero]
        have htailDistinct : ∀ job ∈ jobs, job ≠ later := by
          intro job hjob heq
          subst job
          exact hheadNodup hjob
        have hrun := nonpreemptivePriorityFifoCompletionOrder_run
          admitted jobs earlier later hdistinct hadmittedWork hadmittedMultiplicity hadmittedTimes
          hadmittedDisposition hadmittedOrder
          (fun job hjob => hjobsWork job (by simp [hjob])) htailDistinct
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun
      · have hnewNeLater : newJob ≠ later := by
          intro heq
          subst newJob
          exact hheadNodup htail
        have hadmittedNotLater : ¬ nonpreemptivePriorityWorkStateContainsJob admitted later := by
          intro hcontains
          rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse
            advanced newJob later (by simpa [admitted] using hcontains) with hadvanced | heq
          · exact hadvancedNotLater hadvanced
          · exact hnewNeLater heq.symm
        have hrun := ih admitted hadmittedClass hadmittedWork hadmittedTimes
          hadmittedEarlier hadmittedNotLater htailNodup htail
          (fun job hjob => hjobsWork job (by simp [hjob]))
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun

end

end AppliedModelingLib.Queueing
