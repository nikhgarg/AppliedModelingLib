import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceMeasurability
import AppliedModelingLib.Queueing.NonpreemptivePriorityFiniteTrace
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkload
import Mathlib.Tactic

/-!
# Fixed-event Borel nonpreemptive-priority traces

This module is the coordinate layer for a finite nonpreemptive-priority
execution whose job identities, priorities, and event skeleton are fixed.
Only arrival, service, residual, and clock coordinates vary with the sample.
It will support a countable Borel partition of literal finite priority replays;
it does not replace the executable queue dynamics.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]
variable {n : ℕ} {JobId : Type*}

/-- A priority job with fixed discrete label and priority, but sample-dependent
arrival and service coordinates. -/
structure NonpreemptivePriorityFixedJobCoordinate
    (Ω : Type*) (n : ℕ) (JobId : Type*) where
  identifier : JobId
  priority : Fin n
  arrivalTime : Ω → ℝ
  serviceWork : Ω → ℝ

/-- Evaluate one fixed-label coordinate job at a sample. -/
def NonpreemptivePriorityFixedJobCoordinate.eval
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) (omega : Ω) :
    NonpreemptivePriorityJob n JobId :=
  { identifier := job.identifier
    priority := job.priority
    arrivalTime := job.arrivalTime omega
    serviceWork := job.serviceWork omega }

/-- The real coordinates carried by a fixed-label job are Borel. -/
def NonpreemptivePriorityFixedJobCoordinate.CoordinatesMeasurable
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) : Prop :=
  Measurable job.arrivalTime ∧ Measurable job.serviceWork

/-- Static coordinate states retain the full literal completion ledger.  Their
list shapes and all discrete data are fixed; only the listed real coordinates
depend on the sample. -/
structure NonpreemptivePriorityFixedStateCoordinate
    (Ω : Type*) (n : ℕ) (JobId : Type*) where
  currentTime : Ω → ℝ
  active : Option (NonpreemptivePriorityFixedJobCoordinate Ω n JobId × (Ω → ℝ))
  waiting : Fin n → List (NonpreemptivePriorityFixedJobCoordinate Ω n JobId)
  completed : List (NonpreemptivePriorityFixedJobCoordinate Ω n JobId × (Ω → ℝ))

/-- Evaluate a fixed-shape coordinate state as the existing literal work
state. -/
def NonpreemptivePriorityFixedStateCoordinate.eval
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) (omega : Ω) :
    NonpreemptivePriorityWorkState n JobId :=
  { currentTime := state.currentTime omega
    active := state.active.map fun entry => (entry.1.eval omega, entry.2 omega)
    waiting := fun i => (state.waiting i).map fun job => job.eval omega
    completed := state.completed.map fun entry => (entry.1.eval omega, entry.2 omega) }

/-- Borel coordinate requirements for a static priority state. -/
def NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) : Prop :=
  Measurable state.currentTime ∧
    (∀ entry, entry ∈ state.active →
      entry.1.CoordinatesMeasurable ∧ Measurable entry.2) ∧
    (∀ i job, job ∈ state.waiting i → job.CoordinatesMeasurable) ∧
    ∀ entry, entry ∈ state.completed →
      entry.1.CoordinatesMeasurable ∧ Measurable entry.2

/-- The empty fixed-shape state at a Borel initial clock. -/
def emptyNonpreemptivePriorityFixedStateCoordinate
    (time : Ω → ℝ) : NonpreemptivePriorityFixedStateCoordinate Ω n JobId :=
  { currentTime := time
    active := none
    waiting := fun _ => []
    completed := [] }

/-- The coordinate empty state evaluates to the literal empty state. -/
theorem emptyNonpreemptivePriorityFixedStateCoordinate_eval
    (time : Ω → ℝ) (omega : Ω) :
    (emptyNonpreemptivePriorityFixedStateCoordinate (n := n) (JobId := JobId) time).eval omega =
      { currentTime := time omega
        active := none
        waiting := fun _ => []
        completed := [] } := by
  rfl

/-- Borelness of the empty fixed-shape state is exactly Borelness of its clock. -/
theorem emptyNonpreemptivePriorityFixedStateCoordinate_coordinatesMeasurable
    (time : Ω → ℝ) (htime : Measurable time) :
    NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable
      (emptyNonpreemptivePriorityFixedStateCoordinate (n := n) (JobId := JobId) time) := by
  refine ⟨htime, ?_, ?_, ?_⟩
  · intro entry hentry
    simp [emptyNonpreemptivePriorityFixedStateCoordinate] at hentry
  · intro i job hjob
    simp [emptyNonpreemptivePriorityFixedStateCoordinate] at hjob
  · intro entry hentry
    simp [emptyNonpreemptivePriorityFixedStateCoordinate] at hentry

/-- Append one fixed-label job to its static class FIFO queue. -/
noncomputable def NonpreemptivePriorityFixedStateCoordinate.enqueue
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) :
    NonpreemptivePriorityFixedStateCoordinate Ω n JobId :=
  { currentTime := state.currentTime
    active := state.active
    waiting := fun i => if i = job.priority then state.waiting i ++ [job] else state.waiting i
    completed := state.completed }

/-- Fixed-shape enqueue is pointwise the literal queue enqueue. -/
theorem NonpreemptivePriorityFixedStateCoordinate.eval_enqueue
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId) (omega : Ω) :
    (state.enqueue job).eval omega =
      enqueueNonpreemptivePriorityJob (state.eval omega) (job.eval omega) := by
  classical
  rcases state with ⟨currentTime, active, waiting, completed⟩
  simp only [NonpreemptivePriorityFixedStateCoordinate.enqueue,
    NonpreemptivePriorityFixedStateCoordinate.eval, enqueueNonpreemptivePriorityJob,
    NonpreemptivePriorityFixedJobCoordinate.eval]
  congr 1
  funext i
  by_cases hi : i = job.priority
  · subst i
    simp
  · simp [hi]

/-- Enqueue preserves coordinatewise Borelness. -/
theorem NonpreemptivePriorityFixedStateCoordinate.CoordinatesMeasurable.enqueue
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (job : NonpreemptivePriorityFixedJobCoordinate Ω n JobId)
    (hstate : state.CoordinatesMeasurable)
    (hjob : job.CoordinatesMeasurable) :
    (state.enqueue job).CoordinatesMeasurable := by
  rcases hstate with ⟨htime, hactive, hwaiting, hcompleted⟩
  refine ⟨htime, ?_, ?_, hcompleted⟩
  · intro entry hentry
    exact hactive entry (by simpa [NonpreemptivePriorityFixedStateCoordinate.enqueue] using hentry)
  · intro i later hlater
    by_cases hi : i = job.priority
    · subst i
      rw [show (state.enqueue job).waiting job.priority =
          state.waiting job.priority ++ [job] by
        simp [NonpreemptivePriorityFixedStateCoordinate.enqueue]] at hlater
      rcases List.mem_append.mp hlater with hprior | hself
      · exact hwaiting job.priority later hprior
      · rcases List.mem_singleton.mp hself with rfl
        exact hjob
    · rw [show (state.enqueue job).waiting i = state.waiting i by
        simp [NonpreemptivePriorityFixedStateCoordinate.enqueue, hi]] at hlater
      exact hwaiting i later hlater

/-- A finite sum of Borel real coordinates is Borel.  This small list API is
used to read residual-work ledgers from a fixed-shape queue state. -/
theorem measurable_list_sum_apply
    (values : List (Ω → ℝ))
    (hvalues : ∀ value ∈ values, Measurable value) :
    Measurable (fun omega => (values.map fun value => value omega).sum) := by
  induction values with
  | nil => simpa using measurable_const
  | cons value values ih =>
      have hvalue : Measurable value := hvalues value (by simp)
      have htail : ∀ later ∈ values, Measurable later := by
        intro later hlater
        exact hvalues later (by simp [hlater])
      simpa using hvalue.add (ih htail)

/-- The active residual-work coordinate of a fixed-shape priority state is
Borel whenever that state's real coordinates are Borel. -/
theorem measurable_activeNonpreemptivePriorityResidualWork_fixedState_eval
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (hstate : state.CoordinatesMeasurable) :
    Measurable (fun omega => activeNonpreemptivePriorityResidualWork (state.eval omega)) := by
  rcases hstate with ⟨_, hactive, _, _⟩
  cases hstateActive : state.active with
  | none => simp [NonpreemptivePriorityFixedStateCoordinate.eval,
      activeNonpreemptivePriorityResidualWork, hstateActive]
  | some entry =>
      simpa [NonpreemptivePriorityFixedStateCoordinate.eval,
        activeNonpreemptivePriorityResidualWork, hstateActive] using
        (hactive entry (by simp [hstateActive])).2

/-- The squared residual-work ledger of a fixed-shape priority state is Borel
whenever its real coordinates are Borel. -/
theorem measurable_totalNonpreemptivePrioritySquaredResidualWork_fixedState_eval
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (hstate : state.CoordinatesMeasurable) :
    Measurable (fun omega =>
      totalNonpreemptivePrioritySquaredResidualWork (state.eval omega)) := by
  unfold totalNonpreemptivePrioritySquaredResidualWork
  apply (measurable_activeNonpreemptivePriorityResidualWork_fixedState_eval
    state hstate).pow_const 2 |>.add
  apply Finset.measurable_fun_sum
  intro i _
  have hwaiting : ∀ job ∈ state.waiting i,
      Measurable (fun omega => job.serviceWork omega ^ 2) := by
    intro job hjob
    exact (hstate.2.2.1 i job hjob).2.pow_const 2
  let values : List (Ω → ℝ) := (state.waiting i).map
    fun job omega => job.serviceWork omega ^ 2
  have hvalues : ∀ value ∈ values, Measurable value := by
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨job, hjob, rfl⟩
    exact hwaiting job hjob
  simpa [values, NonpreemptivePriorityFixedStateCoordinate.eval] using
    measurable_list_sum_apply values hvalues

/-- The waiting residual-work ledger of one class in a fixed-shape priority
state is Borel whenever that state's real coordinates are Borel. -/
theorem measurable_priorityWaitingResidualWork_fixedState_eval
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (hstate : state.CoordinatesMeasurable) (i : Fin n) :
    Measurable (fun omega => priorityWaitingResidualWork (state.eval omega) i) := by
  have hwaiting : ∀ job ∈ state.waiting i, Measurable job.serviceWork := by
    intro job hjob
    exact (hstate.2.2.1 i job hjob).2
  let values : List (Ω → ℝ) := (state.waiting i).map fun job => job.serviceWork
  have hvalues : ∀ value ∈ values, Measurable value := by
    intro value hvalue
    rcases List.mem_map.mp hvalue with ⟨job, hjob, rfl⟩
    exact hwaiting job hjob
  simpa [values, NonpreemptivePriorityFixedStateCoordinate.eval,
    priorityWaitingResidualWork] using measurable_list_sum_apply values hvalues

/-- The aggregate waiting residual work at least as urgent as a priority is
Borel in every fixed-shape priority state with Borel real coordinates. -/
theorem measurable_priorityWaitingResidualWorkAtLeastAsUrgent_fixedState_eval
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId)
    (hstate : state.CoordinatesMeasurable) (i : Fin n) :
    Measurable (fun omega =>
      priorityWaitingResidualWorkAtLeastAsUrgent (state.eval omega) i) := by
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
  apply Finset.measurable_fun_sum
  intro j _
  exact measurable_priorityWaitingResidualWork_fixedState_eval state hstate j

/-- A waiting job exists in a fixed coordinate state exactly when one of its
static FIFO lists is nonempty. -/
def hasFixedPriorityWaitingJob
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) : Prop :=
  ∃ i, 0 < (state.waiting i).length

/-- A static service-order evaluator.  The `clock` is the completion epoch of
the preceding service, and a job that reaches service after an idle period
starts at the larger of its arrival epoch and that clock. -/
def fixedPriorityServiceResponse
    (key : JobId → Bool) (clock : Ω → ℝ) :
    List (NonpreemptivePriorityFixedJobCoordinate Ω n JobId) → Ω → ℝ
  | [], _ => 0
  | job :: jobs, omega =>
      let completedAt := max (clock omega) (job.arrivalTime omega) + job.serviceWork omega
      if key job.identifier = true then completedAt - job.arrivalTime omega
      else fixedPriorityServiceResponse key
        (fun sample => max (clock sample) (job.arrivalTime sample) + job.serviceWork sample)
        jobs omega

/-- The completion epoch generated by a fixed service-order prefix is Borel
from the fixed job coordinates. -/
theorem measurable_fixedPriorityServiceCompletionEpoch
    (clock : Ω → ℝ) (hclock : Measurable clock) :
    ∀ jobs : List (NonpreemptivePriorityFixedJobCoordinate Ω n JobId),
      (∀ job ∈ jobs, job.CoordinatesMeasurable) →
      Measurable (fun omega =>
        match jobs with
        | [] => clock omega
        | job :: _ => max (clock omega) (job.arrivalTime omega) + job.serviceWork omega) := by
  intro jobs hjobs
  cases jobs with
  | nil => simpa using hclock
  | cons job jobs =>
      have hjob := hjobs job (by simp)
      exact (hclock.max hjob.1).add hjob.2

/-- A fixed priority service-order response is Borel.  The Boolean keyed
branch is static because the job identifiers are part of the fixed skeleton. -/
theorem measurable_fixedPriorityServiceResponse
    (key : JobId → Bool) (clock : Ω → ℝ) (hclock : Measurable clock)
    (jobs : List (NonpreemptivePriorityFixedJobCoordinate Ω n JobId))
    (hjobs : ∀ job ∈ jobs, job.CoordinatesMeasurable) :
    Measurable (fixedPriorityServiceResponse key clock jobs) := by
  induction jobs generalizing clock with
  | nil => simp [fixedPriorityServiceResponse]
  | cons job jobs ih =>
      have hjob : job.CoordinatesMeasurable := hjobs job (by simp)
      have htail : ∀ later ∈ jobs, later.CoordinatesMeasurable := by
        intro later hlater
        exact hjobs later (by simp [hlater])
      let nextClock : Ω → ℝ := fun omega =>
        max (clock omega) (job.arrivalTime omega) + job.serviceWork omega
      have hnextClock : Measurable nextClock := (hclock.max hjob.1).add hjob.2
      by_cases hkey : key job.identifier = true
      · simpa [fixedPriorityServiceResponse, nextClock, hkey] using
          (hnextClock.sub hjob.1)
      · simpa [fixedPriorityServiceResponse, nextClock, hkey] using
          ih (clock := nextClock) hnextClock htail

end

end AppliedModelingLib.Queueing
