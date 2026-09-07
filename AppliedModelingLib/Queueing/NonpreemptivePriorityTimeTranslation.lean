import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkload

/-!
# Time translation for finite nonpreemptive-priority states

The finite priority queue dynamics depend on differences of physical times.
This module records the corresponding translation of jobs and states.  The
first layer establishes the invariance of all resident-work observables; later
trace lemmas can use it to transport an execution between two choices of time
origin.
-/

namespace AppliedModelingLib.Queueing

open scoped BigOperators

noncomputable section

/-- Re-express a finite-trace job after moving the physical time origin
forward by `offset`. -/
def translateNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) : NonpreemptivePriorityJob n JobId :=
  { job with arrivalTime := job.arrivalTime - offset }

/-- Re-express a finite priority state after moving the physical time origin
forward by `offset`.  Residual and declared service work are invariant under
this coordinate change. -/
def translateNonpreemptivePriorityWorkState
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  { currentTime := state.currentTime - offset
    active := state.active.map fun active =>
      (translateNonpreemptivePriorityJob offset active.1, active.2)
    waiting := fun i => (state.waiting i).map (translateNonpreemptivePriorityJob offset)
    completed := state.completed.map fun completed =>
      (translateNonpreemptivePriorityJob offset completed.1, completed.2 - offset) }

@[simp]
theorem translateNonpreemptivePriorityJob_identifier
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    (translateNonpreemptivePriorityJob offset job).identifier = job.identifier := rfl

@[simp]
theorem translateNonpreemptivePriorityJob_priority
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    (translateNonpreemptivePriorityJob offset job).priority = job.priority := rfl

@[simp]
theorem translateNonpreemptivePriorityJob_serviceWork
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    (translateNonpreemptivePriorityJob offset job).serviceWork = job.serviceWork := rfl

@[simp]
theorem translateNonpreemptivePriorityJob_arrivalTime
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    (translateNonpreemptivePriorityJob offset job).arrivalTime = job.arrivalTime - offset := rfl

theorem translateNonpreemptivePriorityJob_zero
    {n : ℕ} {JobId : Type*} (job : NonpreemptivePriorityJob n JobId) :
    translateNonpreemptivePriorityJob 0 job = job := by
  cases job
  simp [translateNonpreemptivePriorityJob]

theorem translateNonpreemptivePriorityJob_translate
    {n : ℕ} {JobId : Type*} (first second : ℝ)
    (job : NonpreemptivePriorityJob n JobId) :
    translateNonpreemptivePriorityJob second
      (translateNonpreemptivePriorityJob first job) =
      translateNonpreemptivePriorityJob (first + second) job := by
  cases job
  simp [translateNonpreemptivePriorityJob]
  ring

/-- A time translation preserves the number of resident jobs. -/
theorem totalNonpreemptivePriorityWorkJobs_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityWorkJobs
      (translateNonpreemptivePriorityWorkState offset state) =
      totalNonpreemptivePriorityWorkJobs state := by
  unfold totalNonpreemptivePriorityWorkJobs totalPriorityWaitingJobs
    translateNonpreemptivePriorityWorkState
  cases state.active <;> simp

/-- A time translation preserves each class's waiting-work total. -/
theorem priorityWaitingResidualWork_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    priorityWaitingResidualWork (translateNonpreemptivePriorityWorkState offset state) i =
      priorityWaitingResidualWork state i := by
  unfold priorityWaitingResidualWork translateNonpreemptivePriorityWorkState
  change (List.map (fun job => job.serviceWork)
    (List.map (translateNonpreemptivePriorityJob offset) (state.waiting i))).sum =
      (List.map (fun job => job.serviceWork) (state.waiting i)).sum
  have hservice : (fun job : NonpreemptivePriorityJob n JobId => job.serviceWork) ∘
      translateNonpreemptivePriorityJob offset =
      fun job => job.serviceWork := by
    funext job
    exact translateNonpreemptivePriorityJob_serviceWork offset job
  simpa [List.map_map, hservice]

/-- A time translation preserves active residual work. -/
theorem activeNonpreemptivePriorityResidualWork_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    activeNonpreemptivePriorityResidualWork
      (translateNonpreemptivePriorityWorkState offset state) =
      activeNonpreemptivePriorityResidualWork state := by
  unfold activeNonpreemptivePriorityResidualWork
    translateNonpreemptivePriorityWorkState
  cases state.active <;> rfl

/-- A time translation preserves the squared ledger of all unfinished service
requirements. -/
theorem totalNonpreemptivePrioritySquaredResidualWork_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePrioritySquaredResidualWork
      (translateNonpreemptivePriorityWorkState offset state) =
        totalNonpreemptivePrioritySquaredResidualWork state := by
  unfold totalNonpreemptivePrioritySquaredResidualWork
  rw [activeNonpreemptivePriorityResidualWork_translate]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold translateNonpreemptivePriorityWorkState
  change (List.map (fun job => job.serviceWork ^ 2)
    (List.map (translateNonpreemptivePriorityJob offset) (state.waiting i))).sum =
      (List.map (fun job => job.serviceWork ^ 2) (state.waiting i)).sum
  have hservice : (fun job : NonpreemptivePriorityJob n JobId => job.serviceWork ^ 2) ∘
      translateNonpreemptivePriorityJob offset =
      fun job => job.serviceWork ^ 2 := by
    funext job
    dsimp [Function.comp]
  simpa [List.map_map, hservice]

/-- A time translation preserves waiting work in classes at least as urgent as
a specified priority. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent
      (translateNonpreemptivePriorityWorkState offset state) i =
      priorityWaitingResidualWorkAtLeastAsUrgent state i := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.sum_congr rfl
  intro j _
  exact priorityWaitingResidualWork_translate offset state j

/-- A time translation preserves waiting work in classes less urgent than a
specified priority. -/
theorem priorityWaitingResidualWorkLessUrgent_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    priorityWaitingResidualWorkLessUrgent
      (translateNonpreemptivePriorityWorkState offset state) i =
      priorityWaitingResidualWorkLessUrgent state i := by
  unfold priorityWaitingResidualWorkLessUrgent
  apply Finset.sum_congr rfl
  intro j _
  exact priorityWaitingResidualWork_translate offset state j

/-- A time translation preserves total unfinished work. -/
theorem totalNonpreemptivePriorityResidualWork_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityResidualWork
      (translateNonpreemptivePriorityWorkState offset state) =
      totalNonpreemptivePriorityResidualWork state := by
  unfold totalNonpreemptivePriorityResidualWork
  rw [activeNonpreemptivePriorityResidualWork_translate]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact priorityWaitingResidualWork_translate offset state i

end

end AppliedModelingLib.Queueing
