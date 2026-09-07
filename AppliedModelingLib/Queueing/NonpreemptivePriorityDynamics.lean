import AppliedModelingLib.Queueing.NonpreemptivePriorityDiscipline

/-!
# Event dynamics for finite nonpreemptive-priority queues

This module extends the waiting-backlog discipline by recording the class
currently in service.  It is a deterministic event layer suitable for a later
marked-arrival and exponential-service construction.
-/

namespace AppliedModelingLib
namespace Queueing

/-- A finite nonpreemptive-priority queue state records the currently served
class, if any, and the waiting backlog by class. -/
structure NonpreemptivePriorityState (n : ℕ) where
  active : Option (Fin n)
  waiting : Fin n → ℕ

/-- The state record is equivalently its active-service and waiting-backlog
coordinates. -/
def nonpreemptivePriorityStateEquiv (n : ℕ) :
    NonpreemptivePriorityState n ≃ Option (Fin n) × (Fin n → ℕ) where
  toFun state := (state.active, state.waiting)
  invFun state := ⟨state.1, state.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A finite-class priority state is countable. -/
instance (n : ℕ) : Countable (NonpreemptivePriorityState n) :=
  (nonpreemptivePriorityStateEquiv n).countable_iff.mpr inferInstance

/-- The countable priority state space carries its discrete measurable
structure for Markov-kernel constructions. -/
instance (n : ℕ) : MeasurableSpace (NonpreemptivePriorityState n) := ⊤

instance (n : ℕ) : MeasurableSingletonClass (NonpreemptivePriorityState n) where
  measurableSet_singleton _ := by trivial

/-- The empty finite priority-queue state.  This is the discrete embedded
state used at a regeneration epoch; unlike the physical trace state it carries
no clock or completion ledger. -/
def emptyNonpreemptivePriorityState (n : ℕ) : NonpreemptivePriorityState n where
  active := none
  waiting := fun _ => 0

@[simp] theorem emptyNonpreemptivePriorityState_active (n : ℕ) :
    (emptyNonpreemptivePriorityState n).active = none := rfl

@[simp] theorem emptyNonpreemptivePriorityState_waiting
    {n : ℕ} (i : Fin n) :
    (emptyNonpreemptivePriorityState n).waiting i = 0 := rfl

/-- The active-service contribution to the number of jobs in a queue state. -/
def activePriorityJobCount {n : ℕ} (state : NonpreemptivePriorityState n) : ℕ :=
  match state.active with
  | none => 0
  | some _ => 1

/-- The total number of waiting or in-service jobs in a finite priority state. -/
def totalNonpreemptivePriorityJobs {n : ℕ} (state : NonpreemptivePriorityState n) : ℕ :=
  activePriorityJobCount state + totalPriorityBacklog state.waiting

/-- The number of waiting or in-service jobs belonging to one fixed priority
class.  This coordinate is useful for classwise flow conservation, independently
of the service-selection rule among the other classes. -/
def classNonpreemptivePriorityJobs {n : ℕ}
    (state : NonpreemptivePriorityState n) (i : Fin n) : ℕ :=
  state.waiting i + if state.active = some i then 1 else 0

/-- An arrival starts service immediately at an idle server; otherwise it joins
the waiting backlog of its declared priority class. -/
def arriveNonpreemptivePriority
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    NonpreemptivePriorityState n :=
  match state.active with
  | none => ⟨some i, state.waiting⟩
  | some active => ⟨some active, addPriorityArrival state.waiting i⟩

/-- An arrival to the empty embedded state starts service immediately and
leaves every waiting backlog empty. -/
theorem arriveNonpreemptivePriority_empty
    {n : ℕ} (i : Fin n) :
    arriveNonpreemptivePriority (emptyNonpreemptivePriorityState n) i =
      ⟨some i, fun _ => 0⟩ := by
  rfl

/-- Every arrival increases the total finite queue population by one. -/
theorem totalNonpreemptivePriorityJobs_arrive
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    totalNonpreemptivePriorityJobs (arriveNonpreemptivePriority state i) =
      totalNonpreemptivePriorityJobs state + 1 := by
  cases hactive : state.active with
  | none =>
      simp [arriveNonpreemptivePriority, totalNonpreemptivePriorityJobs,
        activePriorityJobCount, hactive]
      omega
  | some active =>
      simp only [arriveNonpreemptivePriority, hactive,
        totalNonpreemptivePriorityJobs, activePriorityJobCount]
      rw [totalPriorityBacklog_addPriorityArrival]
      omega

/-- An arrival increments exactly the population of its own class. -/
theorem classNonpreemptivePriorityJobs_arrive
    {n : ℕ} (state : NonpreemptivePriorityState n) (arrivalClass i : Fin n) :
    classNonpreemptivePriorityJobs (arriveNonpreemptivePriority state arrivalClass) i =
      classNonpreemptivePriorityJobs state i + if i = arrivalClass then 1 else 0 := by
  by_cases hi : i = arrivalClass
  · subst i
    cases hactive : state.active with
    | none =>
        simp [classNonpreemptivePriorityJobs, arriveNonpreemptivePriority, hactive]
    | some active =>
        simp [classNonpreemptivePriorityJobs, arriveNonpreemptivePriority, hactive,
          addPriorityArrival_selected]
        omega
  · cases hactive : state.active with
    | none =>
        have hji : arrivalClass ≠ i := Ne.symm hi
        simp [classNonpreemptivePriorityJobs, arriveNonpreemptivePriority, hactive, hi, hji]
    | some active =>
        simp [classNonpreemptivePriorityJobs, arriveNonpreemptivePriority, hactive, hi,
          addPriorityArrival_of_ne _ arrivalClass i hi]

/-- A service completion leaves an idle queue unchanged.  If work is waiting,
the highest-priority waiting class immediately begins its own nonpreemptive
service; otherwise the server becomes idle. -/
noncomputable def completeNonpreemptivePriority
    {n : ℕ} (state : NonpreemptivePriorityState n) : NonpreemptivePriorityState n :=
  match state.active with
  | none => state
  | some _ =>
      if hwaiting : ∃ i, 0 < state.waiting i then
        ⟨some (nextNonpreemptivePriority state.waiting hwaiting),
          completeNonpreemptivePriorityService state.waiting hwaiting⟩
      else
        ⟨none, state.waiting⟩

/-- Completing service from a busy finite priority queue removes exactly one
job, whether or not another waiting job starts service. -/
theorem totalNonpreemptivePriorityJobs_complete_of_active
    {n : ℕ} (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active) :
    totalNonpreemptivePriorityJobs (completeNonpreemptivePriority state) + 1 =
      totalNonpreemptivePriorityJobs state := by
  by_cases hwaiting : ∃ i, 0 < state.waiting i
  · simp only [completeNonpreemptivePriority, hactive, dif_pos hwaiting,
      totalNonpreemptivePriorityJobs, activePriorityJobCount]
    have hback :=
      totalPriorityBacklog_completeNonpreemptivePriorityService state.waiting hwaiting
    omega
  · simp [completeNonpreemptivePriority, hactive, hwaiting,
      totalNonpreemptivePriorityJobs, activePriorityJobCount]
    omega

/-- Completing an active job decreases exactly the population of that active
class.  When another waiting job of the same class immediately starts service,
the active/waiting split changes but the total class population still falls by
one. -/
theorem classNonpreemptivePriorityJobs_complete_of_active
    {n : ℕ} (state : NonpreemptivePriorityState n) (active i : Fin n)
    (hactive : state.active = some active) :
    classNonpreemptivePriorityJobs (completeNonpreemptivePriority state) i +
        (if i = active then 1 else 0) =
      classNonpreemptivePriorityJobs state i := by
  by_cases hwaiting : ∃ j, 0 < state.waiting j
  · by_cases hiActive : i = active
    · subst i
      by_cases hselected : nextNonpreemptivePriority state.waiting hwaiting = active
      · have hpositive : 0 < state.waiting active := by
          simpa [hselected] using
            (nextNonpreemptivePriority_positive state.waiting hwaiting)
        have hupdate : completeNonpreemptivePriorityService state.waiting hwaiting active =
            state.waiting active - 1 := by
          rw [← hselected]
          exact completeNonpreemptivePriorityService_selected state.waiting hwaiting
        simp only [classNonpreemptivePriorityJobs, completeNonpreemptivePriority,
          hactive, dif_pos hwaiting, Option.some.injEq]
        rw [hupdate]
        simp [hselected]
        omega
      · have hupdate : completeNonpreemptivePriorityService state.waiting hwaiting active =
            state.waiting active :=
          completeNonpreemptivePriorityService_of_ne state.waiting hwaiting active
            (Ne.symm hselected)
        simp only [classNonpreemptivePriorityJobs, completeNonpreemptivePriority,
          hactive, dif_pos hwaiting, Option.some.injEq]
        rw [hupdate]
        simp [hselected]
    · have hactiveNe : active ≠ i := Ne.symm hiActive
      by_cases hselected : i = nextNonpreemptivePriority state.waiting hwaiting
      · have hselected' : nextNonpreemptivePriority state.waiting hwaiting = i := hselected.symm
        have hpositive : 0 < state.waiting i := by
          simpa [hselected'] using
            (nextNonpreemptivePriority_positive state.waiting hwaiting)
        have hupdate : completeNonpreemptivePriorityService state.waiting hwaiting i =
            state.waiting i - 1 := by
          rw [← hselected']
          exact completeNonpreemptivePriorityService_selected state.waiting hwaiting
        simp only [classNonpreemptivePriorityJobs, completeNonpreemptivePriority,
          hactive, dif_pos hwaiting, Option.some.injEq]
        rw [hupdate]
        have hactiveSelected :
            active = nextNonpreemptivePriority state.waiting hwaiting ↔
              nextNonpreemptivePriority state.waiting hwaiting = active := eq_comm
        simp [hselected, hactiveSelected]
        exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr
          (nextNonpreemptivePriority_positive state.waiting hwaiting))
      · have hselected' : nextNonpreemptivePriority state.waiting hwaiting ≠ i :=
          Ne.symm hselected
        have hupdate : completeNonpreemptivePriorityService state.waiting hwaiting i =
            state.waiting i :=
          completeNonpreemptivePriorityService_of_ne state.waiting hwaiting i hselected
        simp only [classNonpreemptivePriorityJobs, completeNonpreemptivePriority,
          hactive, dif_pos hwaiting, Option.some.injEq]
        rw [hupdate]
        simp [hiActive, hselected', hactiveNe]
  · simp [classNonpreemptivePriorityJobs, completeNonpreemptivePriority,
      hactive, hwaiting, eq_comm]

/-- A queue state is idle-consistent when it does not retain a waiting
backlog after its active-service coordinate becomes empty.  The state record
itself intentionally permits malformed values, so this invariant records the
property preserved by executions started from the empty state. -/
def nonpreemptivePriorityStateIdleConsistent
    {n : ℕ} (state : NonpreemptivePriorityState n) : Prop :=
  state.active = none → ∀ i, state.waiting i = 0

/-- An idle-consistent state whose active coordinate is empty is the literal
empty state. -/
theorem nonpreemptivePriorityState_eq_empty_of_active_eq_none
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state)
    (hactive : state.active = none) :
    state = emptyNonpreemptivePriorityState n := by
  cases state with
  | mk active waiting =>
      cases active with
      | none =>
          have hwaiting : waiting = fun _ => 0 := by
            funext i
            exact hconsistent rfl i
          subst waiting
          rfl
      | some active =>
          simp at hactive

/-- The empty state is idle-consistent. -/
theorem emptyNonpreemptivePriorityState_idleConsistent (n : ℕ) :
    nonpreemptivePriorityStateIdleConsistent (emptyNonpreemptivePriorityState n) := by
  intro _ i
  rfl

/-- Arrival preserves the fact that an idle state carries no waiting work. -/
theorem nonpreemptivePriorityStateIdleConsistent_arrive
    {n : ℕ} (state : NonpreemptivePriorityState n) (i : Fin n) :
    nonpreemptivePriorityStateIdleConsistent (arriveNonpreemptivePriority state i) := by
  intro hactive
  cases hstate : state.active with
  | none => simp [arriveNonpreemptivePriority, hstate] at hactive
  | some active => simp [arriveNonpreemptivePriority, hstate] at hactive

/-- Service completion preserves idle consistency when it holds before the
completion. -/
theorem nonpreemptivePriorityStateIdleConsistent_complete
    {n : ℕ} (state : NonpreemptivePriorityState n)
    (hconsistent : nonpreemptivePriorityStateIdleConsistent state) :
    nonpreemptivePriorityStateIdleConsistent (completeNonpreemptivePriority state) := by
  intro hactive i
  cases hstate : state.active with
  | none =>
      simpa [completeNonpreemptivePriority, hstate] using hconsistent hstate i
  | some active =>
      by_cases hwaiting : ∃ j, 0 < state.waiting j
      · simp [completeNonpreemptivePriority, hstate, hwaiting] at hactive
      · have hzero : ∀ j, state.waiting j = 0 := by
          intro j
          exact Nat.eq_zero_of_not_pos fun hj => hwaiting ⟨j, hj⟩
        simpa [completeNonpreemptivePriority, hstate, hwaiting] using hzero i

/-- When a completion starts a new service, the selected class is no lower
priority than any waiting class with positive backlog. -/
theorem completeNonpreemptivePriority_selected_le_of_waiting
    {n : ℕ} (state : NonpreemptivePriorityState n) (active : Fin n)
    (hactive : state.active = some active)
    (hwaiting : ∃ i, 0 < state.waiting i) (i : Fin n)
    (hi : 0 < state.waiting i) :
    (completeNonpreemptivePriority state).active =
        some (nextNonpreemptivePriority state.waiting hwaiting) ∧
      nextNonpreemptivePriority state.waiting hwaiting ≤ i := by
  constructor
  · simp [completeNonpreemptivePriority, hactive, hwaiting]
  · exact nextNonpreemptivePriority_le_of_positive state.waiting hwaiting i hi

end Queueing
end AppliedModelingLib
