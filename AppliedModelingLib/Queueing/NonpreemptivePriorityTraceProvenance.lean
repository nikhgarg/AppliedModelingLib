import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionLedger

/-!
# Job provenance for finite nonpreemptive-priority traces

The deterministic queue transitions rearrange and complete existing jobs, but
they do not create a job record.  These converse preservation facts let a
tagged queue construction trace every observed job back to either the initial
state or one literal input arrival.  In particular, they support later proofs
that the tagged Palm customer is not duplicated by a finite replay.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- The number of literal occurrences of a job across the active position,
the class FIFO lists, and the observational completion ledger.  Unlike the
ordinary population count, this tracks one specified record and therefore
detects accidental duplication in a finite replay. -/
def nonpreemptivePriorityWorkStateJobMultiplicity
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) : ℕ := by
  classical
  exact (if ∃ residual, state.active = some (job, residual) then 1 else 0) +
    (∑ i, (state.waiting i).count job) +
      (state.completed.map Prod.fst).count job

/-- Dispatching a waiting job preserves the multiplicity of every literal
job record. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (startNextNonpreemptivePriorityJob state) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [nonpreemptivePriorityWorkStateJobMultiplicity,
        startNextNonpreemptivePriorityJob, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simp [nonpreemptivePriorityWorkStateJobMultiplicity,
              startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
        | cons head tail =>
            have hwaitingCounts :
                (fun i => ((startNextNonpreemptivePriorityJob state).waiting i).count job) =
                  Function.update (fun i => (state.waiting i).count job)
                    selected (tail.count job) := by
              funext i
              by_cases hi : i = selected
              · subst i
                simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hhead]
              · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hhead, Function.update_of_ne hi]
            rw [show nonpreemptivePriorityWorkStateJobMultiplicity
                (startNextNonpreemptivePriorityJob state) job =
                  (if head = job then 1 else 0) +
                    (∑ i, ((startNextNonpreemptivePriorityJob state).waiting i).count job) +
                      (state.completed.map Prod.fst).count job by
              simp [nonpreemptivePriorityWorkStateJobMultiplicity,
                startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]]
            rw [hwaitingCounts, Finset.sum_update_of_mem (Finset.mem_univ selected)]
            have hnoActive : ¬ ∃ residual, state.active = some (job, residual) := by
              simp [hactive]
            rw [nonpreemptivePriorityWorkStateJobMultiplicity, if_neg hnoActive]
            rw [← Finset.sum_erase_add _ (fun i => (state.waiting i).count job)
              (Finset.mem_univ selected)]
            rw [Finset.sdiff_singleton_eq_erase]
            by_cases hheadjob : head = job
            · subst head
              simp [hhead, Nat.add_assoc, Nat.add_comm]
            · simp [hhead, hheadjob, Nat.add_assoc, Nat.add_comm]
      · simp [nonpreemptivePriorityWorkStateJobMultiplicity,
        startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Enqueueing the observed record itself raises its multiplicity by one. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_enqueue_self
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (enqueueNonpreemptivePriorityJob state job) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job + 1 := by
  classical
  have hwaitingCounts :
      (fun i => ((enqueueNonpreemptivePriorityJob state job).waiting i).count job) =
        Function.update (fun i => (state.waiting i).count job) job.priority
          ((state.waiting job.priority).count job + 1) := by
    funext i
    by_cases hi : i = job.priority
    · subst i
      simp [enqueueNonpreemptivePriorityJob, List.count_append]
    · simp [enqueueNonpreemptivePriorityJob, Function.update_of_ne hi]
  rw [nonpreemptivePriorityWorkStateJobMultiplicity,
    nonpreemptivePriorityWorkStateJobMultiplicity, hwaitingCounts,
    Finset.sum_update_of_mem (Finset.mem_univ job.priority)]
  rw [← Finset.sum_erase_add _ (fun i => (state.waiting i).count job)
    (Finset.mem_univ job.priority)]
  rw [Finset.sdiff_singleton_eq_erase]
  simp [enqueueNonpreemptivePriorityJob, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Enqueueing a distinct record leaves the observed record's multiplicity
unchanged. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_enqueue_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hnew : newJob ≠ job) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (enqueueNonpreemptivePriorityJob state newJob) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  have hwaitingCounts :
      (fun i => ((enqueueNonpreemptivePriorityJob state newJob).waiting i).count job) =
        Function.update (fun i => (state.waiting i).count job) newJob.priority
          ((state.waiting newJob.priority).count job) := by
    funext i
    by_cases hi : i = newJob.priority
    · subst i
      simp [enqueueNonpreemptivePriorityJob, List.count_append, hnew]
    · simp [enqueueNonpreemptivePriorityJob, Function.update_of_ne hi]
  rw [nonpreemptivePriorityWorkStateJobMultiplicity,
    nonpreemptivePriorityWorkStateJobMultiplicity, hwaitingCounts,
    Finset.sum_update_of_mem (Finset.mem_univ newJob.priority)]
  rw [← Finset.sum_erase_add _ (fun i => (state.waiting i).count job)
    (Finset.mem_univ newJob.priority)]
  rw [Finset.sdiff_singleton_eq_erase]
  simp [enqueueNonpreemptivePriorityJob, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- A service completion moves the active record to the completion ledger and
then possibly dispatches another waiting record, so it preserves every literal
record's total multiplicity. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (completeNonpreemptivePriorityWorkJob state) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  cases hactive : state.active with
  | none =>
      simp [completeNonpreemptivePriorityWorkJob, hactive]
  | some active =>
      rcases active with ⟨activeJob, activeResidual⟩
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed :=
          (activeJob, state.currentTime) :: state.completed }
      have hstart := nonpreemptivePriorityWorkStateJobMultiplicity_startNext
        afterCompletion job
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (completeNonpreemptivePriorityWorkJob state) job =
            nonpreemptivePriorityWorkStateJobMultiplicity afterCompletion job := by
              simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hstart
        _ = nonpreemptivePriorityWorkStateJobMultiplicity state job := by
              by_cases hjob : activeJob = job
              · subst activeJob
                simp [nonpreemptivePriorityWorkStateJobMultiplicity,
                  afterCompletion, hactive]
                omega
              · simp [nonpreemptivePriorityWorkStateJobMultiplicity,
                  afterCompletion, hactive, hjob]

/-- Changing only the physical clock does not alter literal job
multiplicities. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (time : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      { state with currentTime := time } job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  simp [nonpreemptivePriorityWorkStateJobMultiplicity]

/-- Updating an active customer's residual work leaves the represented record
unchanged. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_activeResidualUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (activeJob : NonpreemptivePriorityJob n JobId)
    (oldResidual newResidual : ℝ)
    (hactive : state.active = some (activeJob, oldResidual))
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      { state with active := some (activeJob, newResidual) } job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  by_cases hjob : activeJob = job
  · subst activeJob
    simp [nonpreemptivePriorityWorkStateJobMultiplicity, hactive]
  · simp [nonpreemptivePriorityWorkStateJobMultiplicity, hactive, hjob]

/-- Pure service advancement rearranges and completes records but cannot
duplicate or delete a literal record from the combined live/completed trace. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (advanceNonpreemptivePriorityWorkState fuel target state) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  induction fuel generalizing state with
  | zero =>
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityWorkStateJobMultiplicity_timeUpdate state target job
        | some active =>
            simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
  | succ fuel ih =>
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityWorkStateJobMultiplicity_timeUpdate state target job
        | some active =>
            rcases active with ⟨activeJob, residual⟩
            by_cases hcomplete : residual ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + residual }
              calc
                nonpreemptivePriorityWorkStateJobMultiplicity
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) job =
                    nonpreemptivePriorityWorkStateJobMultiplicity
                      (advanceNonpreemptivePriorityWorkState fuel target
                        (completeNonpreemptivePriorityWorkJob completedAt)) job := by
                          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                            hcomplete, completedAt]
                _ = nonpreemptivePriorityWorkStateJobMultiplicity
                      (completeNonpreemptivePriorityWorkJob completedAt) job :=
                  ih (completeNonpreemptivePriorityWorkJob completedAt)
                _ = nonpreemptivePriorityWorkStateJobMultiplicity completedAt job :=
                  nonpreemptivePriorityWorkStateJobMultiplicity_complete completedAt job
                _ = nonpreemptivePriorityWorkStateJobMultiplicity state job := by
                  simpa [completedAt] using
                    nonpreemptivePriorityWorkStateJobMultiplicity_timeUpdate
                      state (state.currentTime + residual) job
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete] using
                nonpreemptivePriorityWorkStateJobMultiplicity_activeResidualUpdate
                  state activeJob residual
                    (residual - (target - state.currentTime)) hactive job

/-- Admitting the supplied customer contributes exactly one occurrence of its
literal record, regardless of whether it starts service immediately. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_admit_self
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (admitNonpreemptivePriorityJob state job) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job + 1 := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared := nonpreemptivePriorityWorkStateJobMultiplicity_startNext state job
  cases hactive : prepared.active with
  | none =>
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (admitNonpreemptivePriorityJob state job) job =
            nonpreemptivePriorityWorkStateJobMultiplicity prepared job + 1 := by
              simp [admitNonpreemptivePriorityJob, prepared, hactive,
                nonpreemptivePriorityWorkStateJobMultiplicity]
              omega
        _ = nonpreemptivePriorityWorkStateJobMultiplicity state job + 1 := by
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity prepared job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (startNextNonpreemptivePriorityJob state) job by rfl]
          rw [hprepared]
  | some active =>
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (admitNonpreemptivePriorityJob state job) job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (enqueueNonpreemptivePriorityJob prepared job) job := by
                simp [admitNonpreemptivePriorityJob, prepared, hactive]
        _ = nonpreemptivePriorityWorkStateJobMultiplicity prepared job + 1 :=
          nonpreemptivePriorityWorkStateJobMultiplicity_enqueue_self prepared job
        _ = nonpreemptivePriorityWorkStateJobMultiplicity state job + 1 := by
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity prepared job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (startNextNonpreemptivePriorityJob state) job by rfl]
          rw [hprepared]

/-- Admitting a distinct customer leaves the observed record's multiplicity
unchanged. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hnew : newJob ≠ job) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (admitNonpreemptivePriorityJob state newJob) job =
        nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared := nonpreemptivePriorityWorkStateJobMultiplicity_startNext state job
  cases hactive : prepared.active with
  | none =>
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (admitNonpreemptivePriorityJob state newJob) job =
            nonpreemptivePriorityWorkStateJobMultiplicity prepared job := by
              simp [admitNonpreemptivePriorityJob, prepared, hactive,
                nonpreemptivePriorityWorkStateJobMultiplicity, hnew]
        _ = nonpreemptivePriorityWorkStateJobMultiplicity state job := by
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity prepared job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (startNextNonpreemptivePriorityJob state) job by rfl]
          rw [hprepared]
  | some active =>
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (admitNonpreemptivePriorityJob state newJob) job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (enqueueNonpreemptivePriorityJob prepared newJob) job := by
                simp [admitNonpreemptivePriorityJob, prepared, hactive]
        _ = nonpreemptivePriorityWorkStateJobMultiplicity prepared job :=
          nonpreemptivePriorityWorkStateJobMultiplicity_enqueue_of_ne prepared newJob job hnew
        _ = nonpreemptivePriorityWorkStateJobMultiplicity state job := by
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity prepared job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (startNextNonpreemptivePriorityJob state) job by rfl]
          rw [hprepared]

/-- A finite replay whose literal input records exclude `job` preserves that
job's total multiplicity. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId)
    (hjobs : ∀ newJob ∈ jobs, newJob ≠ job) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (runNonpreemptivePriorityArrivalTrace initial jobs) job =
        nonpreemptivePriorityWorkStateJobMultiplicity initial job := by
  induction jobs generalizing initial with
  | nil => simp [runNonpreemptivePriorityArrivalTrace]
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hnew : newJob ≠ job := hjobs newJob (by simp)
      have htail : ∀ later ∈ jobs, later ≠ job := by
        intro later hlater
        exact hjobs later (List.mem_cons_of_mem _ hlater)
      calc
        nonpreemptivePriorityWorkStateJobMultiplicity
            (runNonpreemptivePriorityArrivalTrace initial (newJob :: jobs)) job =
            nonpreemptivePriorityWorkStateJobMultiplicity
              (runNonpreemptivePriorityArrivalTrace admitted jobs) job := by
                simp [runNonpreemptivePriorityArrivalTrace,
                  advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted]
        _ = nonpreemptivePriorityWorkStateJobMultiplicity admitted job :=
          ih admitted htail
        _ = nonpreemptivePriorityWorkStateJobMultiplicity advanced job :=
          nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne advanced newJob job hnew
        _ = nonpreemptivePriorityWorkStateJobMultiplicity initial job :=
          nonpreemptivePriorityWorkStateJobMultiplicity_advance
            (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial job

/-- A no-duplicate finite input ledger contributes exactly one occurrence of
each listed literal job to the live-plus-completed queue trace. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_run_eq_add_one_of_nodup_mem
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId)
    (hnodup : jobs.Nodup)
    (hmem : job ∈ jobs) :
    nonpreemptivePriorityWorkStateJobMultiplicity
      (runNonpreemptivePriorityArrivalTrace initial jobs) job =
        nonpreemptivePriorityWorkStateJobMultiplicity initial job + 1 := by
  induction jobs generalizing initial with
  | nil => simp at hmem
  | cons newJob jobs ih =>
      rcases List.nodup_cons.mp hnodup with ⟨hhead, htailNodup⟩
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      rcases List.mem_cons.mp hmem with hnew | htail
      · subst newJob
        have htailNe : ∀ later ∈ jobs, later ≠ job := by
          intro later hlater hlaterEq
          subst later
          exact hhead hlater
        calc
          nonpreemptivePriorityWorkStateJobMultiplicity
              (runNonpreemptivePriorityArrivalTrace initial (job :: jobs)) job =
              nonpreemptivePriorityWorkStateJobMultiplicity
                (runNonpreemptivePriorityArrivalTrace admitted jobs) job := by
                  simp [runNonpreemptivePriorityArrivalTrace,
                    advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted]
          _ = nonpreemptivePriorityWorkStateJobMultiplicity admitted job :=
            nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
              admitted jobs job htailNe
          _ = nonpreemptivePriorityWorkStateJobMultiplicity advanced job + 1 :=
            nonpreemptivePriorityWorkStateJobMultiplicity_admit_self advanced job
          _ = nonpreemptivePriorityWorkStateJobMultiplicity initial job + 1 := by
            rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance]
      · have hnewNe : newJob ≠ job := by
          intro hnewEq
          subst newJob
          exact hhead htail
        have hrun := ih admitted htailNodup htail
        calc
          nonpreemptivePriorityWorkStateJobMultiplicity
              (runNonpreemptivePriorityArrivalTrace initial (newJob :: jobs)) job =
              nonpreemptivePriorityWorkStateJobMultiplicity
                (runNonpreemptivePriorityArrivalTrace admitted jobs) job := by
                  simp [runNonpreemptivePriorityArrivalTrace,
                    advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted]
          _ = nonpreemptivePriorityWorkStateJobMultiplicity admitted job + 1 := hrun
          _ = nonpreemptivePriorityWorkStateJobMultiplicity advanced job + 1 := by
            rw [nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne
              advanced newJob job hnewNe]
          _ = nonpreemptivePriorityWorkStateJobMultiplicity initial job + 1 := by
            rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance]

/-- An absent literal record has zero multiplicity. -/
theorem nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hnot : ¬ nonpreemptivePriorityWorkStateContainsJob state job) :
    nonpreemptivePriorityWorkStateJobMultiplicity state job = 0 := by
  classical
  have hactive : ¬ ∃ residual, state.active = some (job, residual) := by
    intro h
    exact hnot (Or.inl h)
  have hwaiting : ∀ i, job ∉ state.waiting i := by
    intro i hmember
    exact hnot (Or.inr (Or.inl ⟨i, hmember⟩))
  have hcompleted : ∀ time, (job, time) ∉ state.completed := by
    intro time hmember
    exact hnot (Or.inr (Or.inr ⟨time, hmember⟩))
  have hcompletedMap : job ∉ state.completed.map Prod.fst := by
    intro hmember
    rcases List.mem_map.mp hmember with ⟨entry, hentry, hentryJob⟩
    rcases entry with ⟨entryJob, time⟩
    change entryJob = job at hentryJob
    subst entryJob
    exact hcompleted time hentry
  have hsum : (∑ i, (state.waiting i).count job) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact List.count_eq_zero_of_not_mem (hwaiting i)
  rw [nonpreemptivePriorityWorkStateJobMultiplicity, if_neg hactive, hsum]
  simp [List.count_eq_zero_of_not_mem hcompletedMap]

/-- A nonzero provenance multiplicity supplies an actual active, waiting, or
completed occurrence of the literal job. -/
theorem nonpreemptivePriorityWorkStateContainsJob_of_jobMultiplicity_ne_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state job ≠ 0) :
    nonpreemptivePriorityWorkStateContainsJob state job := by
  by_contra hcontains
  exact hmultiplicity
    (nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
      state job hcontains)

/-- The number of occurrences of a literal job in just the completion ledger.
This wrapper fixes the classical equality decision locally, so the generic
queue API does not need a global decidable-equality parameter on job IDs. -/
noncomputable def nonpreemptivePriorityCompletedJobMultiplicity
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) : ℕ := by
  classical
  exact (state.completed.map Prod.fst).count job

/-- The completion ledger accounts for no more copies of a job than the full
live-plus-completed multiplicity. -/
theorem nonpreemptivePriorityCompletedJobMultiplicity_le
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityCompletedJobMultiplicity state job ≤
      nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  rw [nonpreemptivePriorityCompletedJobMultiplicity,
    nonpreemptivePriorityWorkStateJobMultiplicity]
  omega

/-- Dispatching a waiting customer does not create a new represented job. -/
theorem nonpreemptivePriorityWorkStateContainsJob_startNext_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (startNextNonpreemptivePriorityJob state) job) :
    nonpreemptivePriorityWorkStateContainsJob state job := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hcontains
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hselected : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
              selected, hselected] using hcontains
        | cons head tail =>
            rcases hcontains with hactiveJob | hwaitingJob | hcompleted
            · rcases hactiveJob with ⟨residual, hjob⟩
              refine Or.inr (Or.inl ⟨selected, ?_⟩)
              have hhead : job = head := by
                have hpair : (head, head.serviceWork) = (job, residual) := by
                  exact Option.some.inj (by
                    simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                      selected, hselected] using hjob)
                exact (congrArg Prod.fst hpair).symm
              simpa [hhead, hselected]
            · rcases hwaitingJob with ⟨j, hmember⟩
              refine Or.inr (Or.inl ⟨j, ?_⟩)
              by_cases hjs : j = selected
              · subst j
                have htail : job ∈ tail := by
                  simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hselected] using hmember
                rw [hselected]
                exact List.mem_cons_of_mem _ htail
              · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                selected, hselected, Function.update_of_ne hjs] using hmember
            · exact Or.inr (Or.inr (by
                simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hselected] using hcompleted))
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hcontains

/-- Enqueuing a customer can create only that newly supplied job record. -/
theorem nonpreemptivePriorityWorkStateContainsJob_enqueue_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (enqueueNonpreemptivePriorityJob state newJob) job) :
    nonpreemptivePriorityWorkStateContainsJob state job ∨ job = newJob := by
  classical
  rcases hcontains with hactive | hwaiting | hcompleted
  · left
    rcases hactive with ⟨residual, hactive⟩
    exact Or.inl ⟨residual, by
      simpa [enqueueNonpreemptivePriorityJob] using hactive⟩
  · rcases hwaiting with ⟨i, hmember⟩
    by_cases hi : i = newJob.priority
    · subst i
      rw [enqueueNonpreemptivePriorityJob_waiting_selected] at hmember
      rcases List.mem_append.mp hmember with hmember | hmember
      · exact Or.inl (Or.inr (Or.inl ⟨newJob.priority, hmember⟩))
      · exact Or.inr (by simpa using hmember)
    · left
      refine Or.inr (Or.inl ⟨i, ?_⟩)
      simpa [enqueueNonpreemptivePriorityJob,
        Function.update_of_ne hi] using hmember
  · left
    exact Or.inr (Or.inr ⟨hcompleted.choose, by
      simpa [enqueueNonpreemptivePriorityJob] using hcompleted.choose_spec⟩)

/-- Completing the active service and dispatching a successor cannot create a
job record: every represented job was already present before the completion. -/
theorem nonpreemptivePriorityWorkStateContainsJob_complete_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (completeNonpreemptivePriorityWorkJob state) job) :
    nonpreemptivePriorityWorkStateContainsJob state job := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hcontains
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hafter : nonpreemptivePriorityWorkStateContainsJob afterCompletion job := by
        exact nonpreemptivePriorityWorkStateContainsJob_startNext_reverse
          afterCompletion job (by
            simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hcontains)
      rcases hafter with hactiveJob | hwaitingJob | hcompleted
      · simp [afterCompletion] at hactiveJob
      · rcases hwaitingJob with ⟨i, hmember⟩
        exact Or.inr (Or.inl ⟨i, by simpa [afterCompletion] using hmember⟩)
      · rcases hcompleted with ⟨time, hmember⟩
        rw [show afterCompletion.completed =
          (active.1, state.currentTime) :: state.completed by rfl] at hmember
        rcases List.mem_cons.mp hmember with hmember | hmember
        · have hjob : job = active.1 := by
            exact (Prod.ext_iff.mp hmember).1
          exact Or.inl ⟨active.2, by simp [hactive, hjob]⟩
        · exact Or.inr (Or.inr ⟨time, hmember⟩)

/-- Admission can create only the job supplied to the admission operation. -/
theorem nonpreemptivePriorityWorkStateContainsJob_admit_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (admitNonpreemptivePriorityJob state newJob) job) :
    nonpreemptivePriorityWorkStateContainsJob state job ∨ job = newJob := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  cases hactive : prepared.active with
  | none =>
      rcases hcontains with hactiveJob | hwaitingJob | hcompleted
      · rcases hactiveJob with ⟨residual, hjob⟩
        right
        have hpair : (newJob, newJob.serviceWork) = (job, residual) := by
          exact Option.some.inj (by
            simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hjob)
        exact (congrArg Prod.fst hpair).symm
      · left
        rcases hwaitingJob with ⟨i, hmember⟩
        have hprepared : nonpreemptivePriorityWorkStateContainsJob prepared job :=
          Or.inr (Or.inl ⟨i, by
            simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hmember⟩)
        exact nonpreemptivePriorityWorkStateContainsJob_startNext_reverse state job
          (by simpa [prepared] using hprepared)
      · left
        rcases hcompleted with ⟨time, hmember⟩
        have hprepared : nonpreemptivePriorityWorkStateContainsJob prepared job :=
          Or.inr (Or.inr ⟨time, by
            simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hmember⟩)
        exact nonpreemptivePriorityWorkStateContainsJob_startNext_reverse state job
          (by simpa [prepared] using hprepared)
  | some active =>
      have henqueued : nonpreemptivePriorityWorkStateContainsJob prepared job ∨ job = newJob :=
        nonpreemptivePriorityWorkStateContainsJob_enqueue_reverse prepared newJob job (by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcontains)
      rcases henqueued with hprepared | hnew
      · left
        exact nonpreemptivePriorityWorkStateContainsJob_startNext_reverse
          state job (by simpa [prepared] using hprepared)
      · exact Or.inr hnew

/-- Changing only a queue state's physical clock does not alter its represented
jobs. -/
theorem nonpreemptivePriorityWorkStateContainsJob_timeUpdate_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (time : ℝ)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      { state with currentTime := time } job) :
    nonpreemptivePriorityWorkStateContainsJob state job := by
  simpa [nonpreemptivePriorityWorkStateContainsJob] using hcontains

/-- Advancing service without admitting an arrival cannot create a job record. -/
theorem nonpreemptivePriorityWorkStateContainsJob_advance_reverse
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (advanceNonpreemptivePriorityWorkState fuel target state) job) :
    nonpreemptivePriorityWorkStateContainsJob state job := by
  classical
  induction fuel generalizing state with
  | zero =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcontains
      · cases hactive : state.active with
        | none =>
            apply nonpreemptivePriorityWorkStateContainsJob_timeUpdate_reverse state target job
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
  | succ fuel ih =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hcontains
      · cases hactive : state.active with
        | none =>
            apply nonpreemptivePriorityWorkStateContainsJob_timeUpdate_reverse state target job
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hcontains
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompleted : nonpreemptivePriorityWorkStateContainsJob
                  (completeNonpreemptivePriorityWorkJob completedAt) job := by
                apply ih
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete, completedAt] using hcontains
              have hbefore : nonpreemptivePriorityWorkStateContainsJob completedAt job :=
                nonpreemptivePriorityWorkStateContainsJob_complete_reverse
                  completedAt job hcompleted
              simpa [completedAt] using hbefore
            · rcases hcontains with hactiveJob | hwaitingJob | hcompleted
              · rcases hactiveJob with ⟨residual, hjob⟩
                have hpair : (active.1, active.2 - (target - state.currentTime)) =
                    (job, residual) := by
                  exact Option.some.inj (by
                    simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                      hcomplete] using hjob)
                have hfirst : active.1 = job := congrArg Prod.fst hpair
                refine Or.inl ⟨active.2, ?_⟩
                rw [hactive]
                exact congrArg some (Prod.ext hfirst rfl)
              · rcases hwaitingJob with ⟨i, hmember⟩
                exact Or.inr (Or.inl ⟨i, by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using hmember⟩)
              · rcases hcompleted with ⟨time, hmember⟩
                exact Or.inr (Or.inr ⟨time, by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using hmember⟩)

/-- A finite arrival trace can represent only an initial job or one of its
literal input records. -/
theorem nonpreemptivePriorityWorkStateContainsJob_run_reverse
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob
      (runNonpreemptivePriorityArrivalTrace initial jobs) job) :
    nonpreemptivePriorityWorkStateContainsJob initial job ∨ job ∈ jobs := by
  induction jobs generalizing initial with
  | nil =>
      exact Or.inl (by simpa [runNonpreemptivePriorityArrivalTrace] using hcontains)
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have htail : nonpreemptivePriorityWorkStateContainsJob admitted job ∨ job ∈ jobs := by
        apply ih admitted
        simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using hcontains
      rcases htail with hadmitted | hmember
      · rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse
          advanced newJob job hadmitted with hadvanced | hnew
        · left
          exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
            (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial job
            (by simpa [advanced] using hadvanced)
        · exact Or.inr (List.mem_cons.mpr (Or.inl hnew))
      · exact Or.inr (List.mem_cons.mpr (Or.inr hmember))

end

end AppliedModelingLib.Queueing
