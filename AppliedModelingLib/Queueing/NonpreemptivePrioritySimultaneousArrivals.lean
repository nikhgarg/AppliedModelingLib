import AppliedModelingLib.Queueing.NonpreemptivePriorityAdvanceSemigroup
import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionTimes
import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkConservation

/-!
# Simultaneous arrivals in a finite nonpreemptive-priority trace

This module records the local fact that a finite batch of arrivals at the
current clock value cannot change the FIFO-waiting status of an already
present, single-occurrence job.  The fact is independent of a particular
stationary construction and makes the endpoint convention in finite replays
explicit.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Advancing to the current physical time is the identity, independently of
the available recursion fuel. -/
theorem advanceNonpreemptivePriorityWorkState_eq_self_of_target_eq_currentTime
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId) :
    advanceNonpreemptivePriorityWorkState fuel state.currentTime state = state := by
  cases fuel <;> simp [advanceNonpreemptivePriorityWorkState]

/-- When the server is already busy, admission only appends the arriving job
to a FIFO list. -/
theorem admitNonpreemptivePriorityJob_eq_enqueue_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hactive : state.active ≠ none) :
    admitNonpreemptivePriorityJob state job =
      enqueueNonpreemptivePriorityJob state job := by
  classical
  cases hstate : state.active with
  | none => exact (hactive hstate).elim
  | some active =>
      simp [admitNonpreemptivePriorityJob, startNextNonpreemptivePriorityJob, hstate]

/-- A busy-server admission preserves an existing FIFO occurrence. -/
theorem mem_waiting_admitNonpreemptivePriorityJob_of_mem_waiting_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob tag : NonpreemptivePriorityJob n JobId) (priority : Fin n)
    (hactive : state.active ≠ none)
    (hwaiting : tag ∈ state.waiting priority) :
    tag ∈ (admitNonpreemptivePriorityJob state newJob).waiting priority := by
  rw [admitNonpreemptivePriorityJob_eq_enqueue_of_active state newJob hactive]
  by_cases hpriority : priority = newJob.priority
  · subst priority
    rw [enqueueNonpreemptivePriorityJob_waiting_selected]
    exact List.mem_append_left _ hwaiting
  · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state newJob priority hpriority]
    exact hwaiting

/-- A busy-server admission leaves the active job and its residual work
unchanged. -/
theorem active_eq_admitNonpreemptivePriorityJob_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob activeJob : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (activeJob, residual)) :
    (admitNonpreemptivePriorityJob state newJob).active =
      some (activeJob, residual) := by
  rw [admitNonpreemptivePriorityJob_eq_enqueue_of_active state newJob]
  · simpa [enqueueNonpreemptivePriorityJob] using hactive
  · exact hactive ▸ Option.some_ne_none _

/-- A batch all arriving at the current time preserves a waiting customer
when the server is initially busy. -/
theorem mem_waiting_runNonpreemptivePriorityArrivalTrace_of_mem_waiting_of_active_of_arrivalTime_eq
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (priority : Fin n)
    (hactive : initial.active ≠ none)
    (hwaiting : tag ∈ initial.waiting priority)
    (htimes : ∀ newJob ∈ jobs, newJob.arrivalTime = initial.currentTime) :
    tag ∈ (runNonpreemptivePriorityArrivalTrace initial jobs).waiting priority := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hwaiting
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      have hnewTime : newJob.arrivalTime = initial.currentTime := htimes newJob (by simp)
      have hadvanced : advanced = initial := by
        simpa [advanced, hnewTime] using
          advanceNonpreemptivePriorityWorkState_eq_self_of_target_eq_currentTime
            (totalNonpreemptivePriorityWorkJobs initial) initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadmittedWaiting : tag ∈ admitted.waiting priority := by
        simpa [admitted, hadvanced] using
          mem_waiting_admitNonpreemptivePriorityJob_of_mem_waiting_of_active
            initial newJob tag priority hactive hwaiting
      have hadmittedActive : admitted.active ≠ none := by
        simpa [admitted] using active_ne_none_admitNonpreemptivePriorityJob advanced newJob
      have hadmittedTime : admitted.currentTime = initial.currentTime := by
        calc
          admitted.currentTime = advanced.currentTime := by
            exact admitNonpreemptivePriorityJob_currentTime advanced newJob
          _ = initial.currentTime := congrArg NonpreemptivePriorityWorkState.currentTime hadvanced
      have htailTimes : ∀ later ∈ jobs, later.arrivalTime = admitted.currentTime := by
        intro later hlater
        rw [htimes later (List.mem_cons_of_mem _ hlater), hadmittedTime]
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmittedActive hadmittedWaiting htailTimes

/-- A batch all arriving at the current time leaves an already active service
record unchanged. -/
theorem active_eq_runNonpreemptivePriorityArrivalTrace_of_active_of_arrivalTime_eq
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (activeJob : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : initial.active = some (activeJob, residual))
    (htimes : ∀ newJob ∈ jobs, newJob.arrivalTime = initial.currentTime) :
    (runNonpreemptivePriorityArrivalTrace initial jobs).active =
      some (activeJob, residual) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hactive
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      have hnewTime : newJob.arrivalTime = initial.currentTime := htimes newJob (by simp)
      have hadvanced : advanced = initial := by
        simpa [advanced, hnewTime] using
          advanceNonpreemptivePriorityWorkState_eq_self_of_target_eq_currentTime
            (totalNonpreemptivePriorityWorkJobs initial) initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadmittedActive : admitted.active = some (activeJob, residual) := by
        simpa [admitted, hadvanced] using
          active_eq_admitNonpreemptivePriorityJob_of_active
            initial newJob activeJob residual hactive
      have hadmittedTime : admitted.currentTime = initial.currentTime := by
        calc
          admitted.currentTime = advanced.currentTime := by
            exact admitNonpreemptivePriorityJob_currentTime advanced newJob
          _ = initial.currentTime := congrArg NonpreemptivePriorityWorkState.currentTime hadvanced
      have htailTimes : ∀ later ∈ jobs, later.arrivalTime = admitted.currentTime := by
        intro later hlater
        rw [htimes later (List.mem_cons_of_mem _ hlater), hadmittedTime]
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmittedActive htailTimes

/-- At a terminal horizon, a finite trace can be split into its strict prefix
and an endpoint batch.  The endpoint batch is replayed from the state already
advanced to that horizon. -/
theorem advance_runNonpreemptivePriorityArrivalTrace_append_of_all_arrivalTime_eq_target
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (hclock : (runNonpreemptivePriorityArrivalTrace initial front).currentTime ≤ target)
    (harrival : ∀ job ∈ tail, job.arrivalTime = target) :
    advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace initial (front ++ tail))) target
      (runNonpreemptivePriorityArrivalTrace initial (front ++ tail)) =
      runNonpreemptivePriorityArrivalTrace
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial front)) target
          (runNonpreemptivePriorityArrivalTrace initial front)) tail := by
  rw [runNonpreemptivePriorityArrivalTrace_append]
  let frontState := runNonpreemptivePriorityArrivalTrace initial front
  let advanced := advanceNonpreemptivePriorityWorkState
    (totalNonpreemptivePriorityWorkJobs frontState) target frontState
  have hadvancedClock : advanced.currentTime = target := by
    dsimp [advanced]
    exact advanceNonpreemptivePriorityWorkState_currentTime_eq_target
      (totalNonpreemptivePriorityWorkJobs frontState) target frontState
      (by simpa [frontState] using hclock) le_rfl
  have hcut := advance_runNonpreemptivePriorityArrivalTrace_cut
    frontState tail target target (by simpa [frontState] using hclock) le_rfl
    (fun job hjob => (harrival job hjob).symm.le)
  have hrunClock : (runNonpreemptivePriorityArrivalTrace advanced tail).currentTime = target :=
    run_currentTime_eq_of_all_arrivalTime_eq_currentTime advanced tail target
      hadvancedClock (by simpa [advanced] using harrival)
  calc
    advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace frontState tail)) target
        (runNonpreemptivePriorityArrivalTrace frontState tail) =
        advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace advanced tail)) target
          (runNonpreemptivePriorityArrivalTrace advanced tail) := by
            simpa [frontState, advanced] using hcut
    _ = runNonpreemptivePriorityArrivalTrace advanced tail := by
      rw [show target = (runNonpreemptivePriorityArrivalTrace advanced tail).currentTime by
        exact hrunClock.symm]
      exact advanceNonpreemptivePriorityWorkState_eq_self_of_target_eq_currentTime
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace advanced tail))
        (runNonpreemptivePriorityArrivalTrace advanced tail)
    _ = runNonpreemptivePriorityArrivalTrace
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial front)) target
          (runNonpreemptivePriorityArrivalTrace initial front)) tail := by
            rfl

/-- For a single-occurrence customer in a work-conserving state, appending a
batch at the current clock time preserves whether that customer is waiting in
its FIFO class. -/
theorem mem_waiting_iff_mem_waiting_runNonpreemptivePriorityArrivalTrace_of_arrivalTime_eq
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (priority : Fin n)
    (hclass : hasClassConsistentWaiting initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial tag ≤ 1)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob initial tag)
    (hpriority : tag.priority = priority)
    (htimes : ∀ newJob ∈ jobs, newJob.arrivalTime = initial.currentTime)
    (hnew : ∀ newJob ∈ jobs, newJob ≠ tag) :
    tag ∈ initial.waiting priority ↔
      tag ∈ (runNonpreemptivePriorityArrivalTrace initial jobs).waiting priority := by
  constructor
  · intro hwaiting
    have hactive : initial.active ≠ none := by
      intro hidle
      apply hwork hidle
      exact ⟨priority, List.length_pos_of_mem hwaiting⟩
    exact mem_waiting_runNonpreemptivePriorityArrivalTrace_of_mem_waiting_of_active_of_arrivalTime_eq
      initial jobs tag priority hactive hwaiting htimes
  · intro hfinal
    let final := runNonpreemptivePriorityArrivalTrace initial jobs
    have hfinalMultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity final tag ≤ 1 := by
      rw [show nonpreemptivePriorityWorkStateJobMultiplicity final tag =
          nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
        simpa [final] using nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
          initial jobs tag hnew]
      exact hmultiplicity
    have hdisjoint := not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
      final tag priority (by simpa [final] using hfinal) hfinalMultiplicity
    have hinitialContains : nonpreemptivePriorityWorkStateContainsJob initial tag := by
      rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse initial jobs tag
        (Or.inr (Or.inl ⟨priority, by simpa [final] using hfinal⟩)) with hinitial | hmember
      · exact hinitial
      · exact (hnew tag hmember rfl).elim
    rcases hinitialContains with hactive | hwaiting | hcompleted
    · rcases hactive with ⟨residual, hactive⟩
      have hactiveFinal : final.active = some (tag, residual) := by
        simpa [final] using
          active_eq_runNonpreemptivePriorityArrivalTrace_of_active_of_arrivalTime_eq
            initial jobs tag residual hactive htimes
      exact (hdisjoint.1 ⟨residual, hactiveFinal⟩).elim
    · rcases hwaiting with ⟨waitingPriority, hwaiting⟩
      have hwaitingPriority : tag.priority = waitingPriority :=
        hclass waitingPriority tag hwaiting
      have : waitingPriority = priority := hwaitingPriority.symm.trans hpriority
      simpa [this] using hwaiting
    · rcases hcompleted with ⟨completedAt, hcompleted⟩
      have hcompletedFinal : (tag, completedAt) ∈ final.completed := by
        simpa [final] using mem_completed_runNonpreemptivePriorityArrivalTrace
          initial jobs tag completedAt hcompleted
      exact (hdisjoint.2 ⟨completedAt, hcompletedFinal⟩).elim

/-- Under the same hypotheses, the presence of a literal customer in some
FIFO list is invariant under the endpoint batch.  This form does not require
any assumption about how FIFO classes are encoded. -/
theorem exists_mem_waiting_iff_exists_mem_waiting_runNonpreemptivePriorityArrivalTrace_of_arrivalTime_eq
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial tag ≤ 1)
    (htimes : ∀ newJob ∈ jobs, newJob.arrivalTime = initial.currentTime)
    (hnew : ∀ newJob ∈ jobs, newJob ≠ tag) :
    (∃ priority, tag ∈ initial.waiting priority) ↔
      ∃ priority, tag ∈
        (runNonpreemptivePriorityArrivalTrace initial jobs).waiting priority := by
  constructor
  · rintro ⟨priority, hwaiting⟩
    have hactive : initial.active ≠ none := by
      intro hidle
      apply hwork hidle
      exact ⟨priority, List.length_pos_of_mem hwaiting⟩
    exact ⟨priority,
      mem_waiting_runNonpreemptivePriorityArrivalTrace_of_mem_waiting_of_active_of_arrivalTime_eq
        initial jobs tag priority hactive hwaiting htimes⟩
  · rintro ⟨priority, hfinal⟩
    let final := runNonpreemptivePriorityArrivalTrace initial jobs
    have hfinalMultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity final tag ≤ 1 := by
      rw [show nonpreemptivePriorityWorkStateJobMultiplicity final tag =
          nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
        simpa [final] using nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
          initial jobs tag hnew]
      exact hmultiplicity
    have hdisjoint := not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
      final tag priority (by simpa [final] using hfinal) hfinalMultiplicity
    have hinitialContains : nonpreemptivePriorityWorkStateContainsJob initial tag := by
      rcases nonpreemptivePriorityWorkStateContainsJob_run_reverse initial jobs tag
        (Or.inr (Or.inl ⟨priority, by simpa [final] using hfinal⟩)) with hinitial | hmember
      · exact hinitial
      · exact (hnew tag hmember rfl).elim
    rcases hinitialContains with hactive | hwaiting | hcompleted
    · rcases hactive with ⟨residual, hactive⟩
      have hactiveFinal : final.active = some (tag, residual) := by
        simpa [final] using
          active_eq_runNonpreemptivePriorityArrivalTrace_of_active_of_arrivalTime_eq
            initial jobs tag residual hactive htimes
      exact (hdisjoint.1 ⟨residual, hactiveFinal⟩).elim
    · exact hwaiting
    · rcases hcompleted with ⟨completedAt, hcompleted⟩
      have hcompletedFinal : (tag, completedAt) ∈ final.completed := by
        simpa [final] using mem_completed_runNonpreemptivePriorityArrivalTrace
          initial jobs tag completedAt hcompleted
      exact (hdisjoint.2 ⟨completedAt, hcompletedFinal⟩).elim

end

end AppliedModelingLib.Queueing
