import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload

/-!
# Identifier transport for finite nonpreemptive-priority traces

The deterministic priority discipline depends on a job's class, arrival
epoch, and required work, but not on the representation chosen for its
identifier.  This module records that invariance for finite trace states.
-/

namespace AppliedModelingLib
namespace Queueing

noncomputable section

/-- Relabel every identifier stored in a finite priority queue state. -/
def nonpreemptivePriorityWorkStateMapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId')
    (state : NonpreemptivePriorityWorkState n JobId) :
    NonpreemptivePriorityWorkState n JobId' :=
  { currentTime := state.currentTime
    active := state.active.map (fun entry =>
      (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2))
    waiting := fun i => (state.waiting i).map (nonpreemptivePriorityJobMapIdentifier f)
    completed := state.completed.map (fun entry =>
      (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2)) }

@[simp]
theorem nonpreemptivePriorityJobMapIdentifier_priority
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobMapIdentifier f job).priority = job.priority := rfl

@[simp]
theorem nonpreemptivePriorityJobMapIdentifier_arrivalTime
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobMapIdentifier f job).arrivalTime = job.arrivalTime := rfl

@[simp]
theorem nonpreemptivePriorityJobMapIdentifier_serviceWork
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobMapIdentifier f job).serviceWork = job.serviceWork := rfl

@[simp]
theorem nonpreemptivePriorityWorkStateMapIdentifier_currentTime
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    (nonpreemptivePriorityWorkStateMapIdentifier f state).currentTime = state.currentTime := rfl

@[simp]
theorem nonpreemptivePriorityWorkStateMapIdentifier_active
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    (nonpreemptivePriorityWorkStateMapIdentifier f state).active =
      state.active.map (fun entry =>
        (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2)) := rfl

@[simp]
theorem nonpreemptivePriorityWorkStateMapIdentifier_waiting
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting i =
      (state.waiting i).map (nonpreemptivePriorityJobMapIdentifier f) := rfl

@[simp]
theorem nonpreemptivePriorityWorkStateMapIdentifier_completed
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    (nonpreemptivePriorityWorkStateMapIdentifier f state).completed =
      state.completed.map (fun entry =>
        (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2)) := rfl

/-- Relabelling preserves the resident-job count. -/
theorem totalNonpreemptivePriorityWorkJobs_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityWorkJobs (nonpreemptivePriorityWorkStateMapIdentifier f state) =
      totalNonpreemptivePriorityWorkJobs state := by
  unfold totalNonpreemptivePriorityWorkJobs totalPriorityWaitingJobs
  cases hactive : state.active <;>
    simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]

/-- Relabelling preserves whether the queue has a nonempty priority class. -/
theorem hasPriorityWaitingJob_mapIdentifier_iff
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    hasPriorityWaitingJob (nonpreemptivePriorityWorkStateMapIdentifier f state) ↔
      hasPriorityWaitingJob state := by
  unfold hasPriorityWaitingJob
  simp [nonpreemptivePriorityWorkStateMapIdentifier]

/-- The selected nonempty priority class is unchanged by relabelling. -/
theorem nextPriorityWaitingClass_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (hwaiting : hasPriorityWaitingJob state) :
    nextPriorityWaitingClass (nonpreemptivePriorityWorkStateMapIdentifier f state)
        ((hasPriorityWaitingJob_mapIdentifier_iff f state).mpr hwaiting) =
      nextPriorityWaitingClass state hwaiting := by
  unfold nextPriorityWaitingClass
  congr 1
  funext i
  simp [nonpreemptivePriorityWorkStateMapIdentifier]

/-- Adding a relabelled job commutes with relabelling the queue state. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_enqueue
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (enqueueNonpreemptivePriorityJob state job) =
      enqueueNonpreemptivePriorityJob
        (nonpreemptivePriorityWorkStateMapIdentifier f state)
        (nonpreemptivePriorityJobMapIdentifier f job) := by
  classical
  cases state
  simp [nonpreemptivePriorityWorkStateMapIdentifier,
    enqueueNonpreemptivePriorityJob, Function.update]
  funext i
  by_cases hi : i = job.priority <;> simp [Function.update, hi]

/-- Selecting the next priority job commutes with relabelling identifiers. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_startNext
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (startNextNonpreemptivePriorityJob state) =
      startNextNonpreemptivePriorityJob
        (nonpreemptivePriorityWorkStateMapIdentifier f state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob,
        nonpreemptivePriorityWorkStateMapIdentifier, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · have hwaitingMapped : hasPriorityWaitingJob
            (nonpreemptivePriorityWorkStateMapIdentifier f state) :=
            (hasPriorityWaitingJob_mapIdentifier_iff f state).mpr hwaiting
        have hselected :
            nextPriorityWaitingClass (nonpreemptivePriorityWorkStateMapIdentifier f state)
                hwaitingMapped =
              nextPriorityWaitingClass state hwaiting := by
          exact nextPriorityWaitingClass_mapIdentifier f state hwaiting
        cases hhead : state.waiting (nextPriorityWaitingClass state hwaiting) with
        | nil =>
            have hheadMapped : (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting
                (nextPriorityWaitingClass
                  (nonpreemptivePriorityWorkStateMapIdentifier f state) hwaitingMapped) = [] := by
              rw [hselected]
              simp [nonpreemptivePriorityWorkStateMapIdentifier, hhead]
            have hstartMapped :
                startNextNonpreemptivePriorityJob
                    (nonpreemptivePriorityWorkStateMapIdentifier f state) =
                  nonpreemptivePriorityWorkStateMapIdentifier f state := by
              unfold startNextNonpreemptivePriorityJob
              rw [show (nonpreemptivePriorityWorkStateMapIdentifier f state).active = none by
                simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]]
              rw [dif_pos hwaitingMapped]
              simp only
              rw [hheadMapped]
            rw [hstartMapped]
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, hhead]
        | cons job tail =>
            have hheadMapped : (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting
                (nextPriorityWaitingClass
                  (nonpreemptivePriorityWorkStateMapIdentifier f state) hwaitingMapped) =
                  nonpreemptivePriorityJobMapIdentifier f job ::
                    tail.map (nonpreemptivePriorityJobMapIdentifier f) := by
              rw [hselected]
              simp [nonpreemptivePriorityWorkStateMapIdentifier, hhead]
            have hstartMapped :
                startNextNonpreemptivePriorityJob
                    (nonpreemptivePriorityWorkStateMapIdentifier f state) =
                  { (nonpreemptivePriorityWorkStateMapIdentifier f state) with
                    active := some (nonpreemptivePriorityJobMapIdentifier f job, job.serviceWork)
                    waiting := Function.update
                      (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting
                      (nextPriorityWaitingClass
                        (nonpreemptivePriorityWorkStateMapIdentifier f state) hwaitingMapped)
                      (tail.map (nonpreemptivePriorityJobMapIdentifier f)) } := by
              unfold startNextNonpreemptivePriorityJob
              rw [show (nonpreemptivePriorityWorkStateMapIdentifier f state).active = none by
                simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]]
              rw [dif_pos hwaitingMapped]
              simp only
              rw [hheadMapped]
              rfl
            rw [hselected] at hstartMapped
            rw [hstartMapped]
            simp [startNextNonpreemptivePriorityJob,
              nonpreemptivePriorityWorkStateMapIdentifier, hactive, hwaiting, hhead]
            funext i
            by_cases hi : i = nextPriorityWaitingClass state hwaiting <;>
              simp [Function.update, hi]
      · have hwaitingMapped : ¬ hasPriorityWaitingJob
            (nonpreemptivePriorityWorkStateMapIdentifier f state) :=
            (hasPriorityWaitingJob_mapIdentifier_iff f state).not.mpr hwaiting
        have hstartMapped :
            startNextNonpreemptivePriorityJob
                (nonpreemptivePriorityWorkStateMapIdentifier f state) =
              nonpreemptivePriorityWorkStateMapIdentifier f state := by
          unfold startNextNonpreemptivePriorityJob
          rw [show (nonpreemptivePriorityWorkStateMapIdentifier f state).active = none by
            simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]]
          rw [dif_neg hwaitingMapped]
        rw [hstartMapped]
        simp [startNextNonpreemptivePriorityJob, hactive, hwaiting]

/-- Admission of a relabelled job commutes with relabelling the queue state. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_admit
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (admitNonpreemptivePriorityJob state job) =
      admitNonpreemptivePriorityJob
        (nonpreemptivePriorityWorkStateMapIdentifier f state)
        (nonpreemptivePriorityJobMapIdentifier f job) := by
  classical
  unfold admitNonpreemptivePriorityJob
  rw [show startNextNonpreemptivePriorityJob
      (nonpreemptivePriorityWorkStateMapIdentifier f state) =
        nonpreemptivePriorityWorkStateMapIdentifier f
          (startNextNonpreemptivePriorityJob state) by
    symm
    exact nonpreemptivePriorityWorkStateMapIdentifier_startNext f state]
  dsimp
  cases hprepared : (startNextNonpreemptivePriorityJob state).active with
  | none =>
      simp [hprepared, nonpreemptivePriorityWorkStateMapIdentifier]
  | some active =>
      simpa [hprepared] using
        (nonpreemptivePriorityWorkStateMapIdentifier_enqueue f
          (startNextNonpreemptivePriorityJob state) job)

/-- Recording a completion and selecting the next job commutes with
identifier relabelling. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_complete
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (completeNonpreemptivePriorityWorkJob state) =
      completeNonpreemptivePriorityWorkJob
        (nonpreemptivePriorityWorkStateMapIdentifier f state) := by
  classical
  unfold completeNonpreemptivePriorityWorkJob
  cases hactive : state.active with
  | none =>
      simp [hactive, nonpreemptivePriorityWorkStateMapIdentifier]
  | some active =>
      let pre : NonpreemptivePriorityWorkState n JobId :=
        { currentTime := state.currentTime
          active := none
          waiting := state.waiting
          completed := (active.1, state.currentTime) :: state.completed }
      have hpre : nonpreemptivePriorityWorkStateMapIdentifier f pre =
          { currentTime := (nonpreemptivePriorityWorkStateMapIdentifier f state).currentTime
            active := none
            waiting := (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting
            completed := (nonpreemptivePriorityJobMapIdentifier f active.1,
              (nonpreemptivePriorityWorkStateMapIdentifier f state).currentTime) ::
                (nonpreemptivePriorityWorkStateMapIdentifier f state).completed } := by
        simp [pre, nonpreemptivePriorityWorkStateMapIdentifier]
      have hactiveMapped :
          (nonpreemptivePriorityWorkStateMapIdentifier f state).active =
            some (nonpreemptivePriorityJobMapIdentifier f active.1, active.2) := by
        simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]
      rw [hactiveMapped]
      simp only
      rw [← hpre, ← nonpreemptivePriorityWorkStateMapIdentifier_startNext f pre]

/-- Bounded deterministic service evolution commutes with identifier
relabelling. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_advance
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (advanceNonpreemptivePriorityWorkState fuel target state) =
      advanceNonpreemptivePriorityWorkState fuel target
        (nonpreemptivePriorityWorkStateMapIdentifier f state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none =>
            simp [advanceNonpreemptivePriorityWorkState,
              nonpreemptivePriorityWorkStateMapIdentifier,
              htarget, hactive]
        | some active =>
            simp [advanceNonpreemptivePriorityWorkState,
              nonpreemptivePriorityWorkStateMapIdentifier,
              htarget, hactive]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none =>
            simp [advanceNonpreemptivePriorityWorkState,
              nonpreemptivePriorityWorkStateMapIdentifier,
              htarget, hactive]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { currentTime := state.currentTime + active.2
                  active := some active
                  waiting := state.waiting
                  completed := state.completed }
              have hcompletedAtMap :
                  nonpreemptivePriorityWorkStateMapIdentifier f completedAt =
                    { currentTime := state.currentTime + active.2
                      active := some
                        (nonpreemptivePriorityJobMapIdentifier f active.1, active.2)
                      waiting := (nonpreemptivePriorityWorkStateMapIdentifier f state).waiting
                      completed := state.completed.map (fun entry =>
                        (nonpreemptivePriorityJobMapIdentifier f entry.1, entry.2)) } := by
                simp [completedAt, nonpreemptivePriorityWorkStateMapIdentifier]
              simp [advanceNonpreemptivePriorityWorkState, htarget,
                hactive, hcomplete]
              rw [← hcompletedAtMap,
                ← nonpreemptivePriorityWorkStateMapIdentifier_complete f completedAt]
              exact ih (completeNonpreemptivePriorityWorkJob completedAt)
            · simp [advanceNonpreemptivePriorityWorkState,
                nonpreemptivePriorityWorkStateMapIdentifier,
                htarget, hactive, hcomplete]

/-- Advancing to a relabelled arrival and admitting it commutes with
identifier relabelling. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_advanceThenAdmit
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (fuel : ℕ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (advanceThenAdmitNonpreemptivePriorityJob fuel state job) =
      advanceThenAdmitNonpreemptivePriorityJob fuel
        (nonpreemptivePriorityWorkStateMapIdentifier f state)
        (nonpreemptivePriorityJobMapIdentifier f job) := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [nonpreemptivePriorityWorkStateMapIdentifier_admit,
    nonpreemptivePriorityWorkStateMapIdentifier_advance]
  rfl

/-- Executing a finite relabelled arrival list commutes with relabelling the
final queue state. -/
theorem nonpreemptivePriorityWorkStateMapIdentifier_run
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId')
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityWorkStateMapIdentifier f
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      runNonpreemptivePriorityArrivalTrace
        (nonpreemptivePriorityWorkStateMapIdentifier f initial)
        (jobs.map (nonpreemptivePriorityJobMapIdentifier f)) := by
  induction jobs generalizing initial with
  | nil =>
      rfl
  | cons job jobs ih =>
      change nonpreemptivePriorityWorkStateMapIdentifier f
          (runNonpreemptivePriorityArrivalTrace
            (advanceThenAdmitNonpreemptivePriorityJob
              (totalNonpreemptivePriorityWorkJobs initial) initial job) jobs) =
        runNonpreemptivePriorityArrivalTrace
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs
              (nonpreemptivePriorityWorkStateMapIdentifier f initial))
            (nonpreemptivePriorityWorkStateMapIdentifier f initial)
            (nonpreemptivePriorityJobMapIdentifier f job))
          (jobs.map (nonpreemptivePriorityJobMapIdentifier f))
      rw [ih]
      rw [nonpreemptivePriorityWorkStateMapIdentifier_advanceThenAdmit,
        totalNonpreemptivePriorityWorkJobs_mapIdentifier]

/-- Relabelling identifiers leaves the residual work of the active customer
unchanged.  This lets canonical-past replay transports retain the physical
service component of a queue state, not only its aggregate workload. -/
theorem activeNonpreemptivePriorityResidualWork_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    activeNonpreemptivePriorityResidualWork
      (nonpreemptivePriorityWorkStateMapIdentifier f state) =
        activeNonpreemptivePriorityResidualWork state := by
  unfold activeNonpreemptivePriorityResidualWork
  cases hactive : state.active <;>
    simp [nonpreemptivePriorityWorkStateMapIdentifier, hactive]

/-- Relabelling identifiers preserves the squared ledger of all unfinished
service requirements. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePrioritySquaredResidualWork
      (nonpreemptivePriorityWorkStateMapIdentifier f state) =
        totalNonpreemptivePrioritySquaredResidualWork state := by
  unfold totalNonpreemptivePrioritySquaredResidualWork
  rw [activeNonpreemptivePriorityResidualWork_mapIdentifier]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [nonpreemptivePriorityWorkStateMapIdentifier_waiting]
  rw [List.map_map]
  change ((state.waiting i).map
    (fun job => (nonpreemptivePriorityJobMapIdentifier f job).serviceWork ^ 2)).sum =
      ((state.waiting i).map (fun job => job.serviceWork ^ 2)).sum
  congr 1

/-- Relabelling identifiers preserves the service work held in every class
FIFO list. -/
theorem priorityWaitingResidualWork_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (i : Fin n) :
    priorityWaitingResidualWork (nonpreemptivePriorityWorkStateMapIdentifier f state) i =
      priorityWaitingResidualWork state i := by
  unfold priorityWaitingResidualWork
  rw [nonpreemptivePriorityWorkStateMapIdentifier_waiting]
  rw [List.map_map]
  change ((state.waiting i).map
    (fun job => (nonpreemptivePriorityJobMapIdentifier f job).serviceWork)).sum =
      ((state.waiting i).map (fun job => job.serviceWork)).sum
  congr 1

/-- Relabelling identifiers preserves the total waiting work in priority
classes at least as urgent as a designated class. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (i : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (nonpreemptivePriorityWorkStateMapIdentifier f state) i =
        priorityWaitingResidualWorkAtLeastAsUrgent state i := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_congr rfl
  intro j _
  exact priorityWaitingResidualWork_mapIdentifier f state j

/-- Relabelling identifiers preserves the total waiting work in less-urgent
priority classes. -/
theorem priorityWaitingResidualWorkLessUrgent_mapIdentifier
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (state : NonpreemptivePriorityWorkState n JobId)
    (i : Fin n) :
    priorityWaitingResidualWorkLessUrgent
      (nonpreemptivePriorityWorkStateMapIdentifier f state) i =
        priorityWaitingResidualWorkLessUrgent state i := by
  unfold priorityWaitingResidualWorkLessUrgent
  apply Finset.sum_congr rfl
  intro j _
  exact priorityWaitingResidualWork_mapIdentifier f state j

end
end Queueing
end AppliedModelingLib
