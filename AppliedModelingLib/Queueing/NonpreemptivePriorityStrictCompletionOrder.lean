import AppliedModelingLib.Queueing.NonpreemptivePriorityFifoCompletionOrder
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkConservation

/-!
# Strict-priority completion order for finite nonpreemptive queues

This module complements the within-class FIFO completion API.  If a higher
priority customer is already present before a lower priority customer is
admitted, nonpreemption allows an already active low-priority job to finish,
but it never lets the later low-priority customer start ahead of the higher
priority customer.  The resulting literal completion-order theorem is the
deterministic exclusion needed in tagged priority-queue workload arguments.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- The persistent disposition of a strictly higher-priority customer relative
to a later lower-priority one.  In the waiting case the lower-priority record
is explicitly not active; this is the nonpreemptive priority guard that turns
service selection into a completion-order fact. -/
def nonpreemptivePriorityStrictPrecedesDisposition
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId) : Prop :=
  (∃ residual, state.active = some (higher, residual)) ∨
    (∃ completedAt, (higher, completedAt) ∈ state.completed) ∨
      higher ∈ state.waiting higher.priority ∧
        ∀ residual, state.active ≠ some (lower, residual)

/-- A class-consistent represented customer has the strict-priority
disposition whenever the comparison customer is not active. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_of_contains
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state higher)
    (hnotActive : ∀ residual, state.active ≠ some (lower, residual)) :
    nonpreemptivePriorityStrictPrecedesDisposition state higher lower := by
  rcases hcontains with hactive | hwaiting | hcompleted
  · exact Or.inl hactive
  · rcases hwaiting with ⟨i, hwaiting⟩
    have hpriority : higher.priority = i := hclass i higher hwaiting
    exact Or.inr (Or.inr ⟨by simpa [hpriority] using hwaiting, hnotActive⟩)
  · exact Or.inr (Or.inl hcompleted)

/-- Changing only the physical clock preserves a strict-priority disposition. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId) (time : ℝ)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      { state with currentTime := time } higher lower := by
  rcases hdisposition with hactive | hcompleted | hwaiting
  · exact Or.inl ⟨hactive.choose, by simpa using hactive.choose_spec⟩
  · exact Or.inr (Or.inl ⟨hcompleted.choose, by simpa using hcompleted.choose_spec⟩)
  · refine Or.inr (Or.inr ⟨by simpa using hwaiting.1, ?_⟩)
    intro residual hactive
    exact hwaiting.2 residual (by simpa using hactive)

/-- Updating the residual requirement of an active customer preserves the
strict-priority disposition. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_activeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active)
    (time residual : ℝ)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      { state with currentTime := time, active := some (active.1, residual) }
      higher lower := by
  rcases hdisposition with hhigherActive | hhigherCompleted | hhigherWaiting
  · rcases hhigherActive with ⟨oldResidual, hhigherActive⟩
    have hhigher : active.1 = higher := by
      exact congrArg Prod.fst (Option.some.inj (hactive.symm.trans hhigherActive))
    exact Or.inl ⟨residual, by simp [hhigher]⟩
  · exact Or.inr (Or.inl ⟨hhigherCompleted.choose, by
      simpa using hhigherCompleted.choose_spec⟩)
  · refine Or.inr (Or.inr ⟨by simpa using hhigherWaiting.1, ?_⟩)
    intro lowerResidual hnewActive
    have hjob : active.1 = lower := by
      exact congrArg Prod.fst (Option.some.inj hnewActive)
    have hpair : active = (lower, active.2) := Prod.ext hjob rfl
    apply hhigherWaiting.2 active.2
    calc
      state.active = some active := hactive
      _ = some (lower, active.2) := congrArg some hpair

/-- Dispatching from an idle queue cannot select a lower-priority customer
while a higher-priority customer remains waiting.  This is the one-step
nonpreemptive priority guard underlying strict completion order. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : higher.priority < lower.priority)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      (startNextNonpreemptivePriorityJob state) higher lower := by
  classical
  rcases hdisposition with hhigherActive | hhigherCompleted | hhigherWaiting
  · rcases hhigherActive with ⟨residual, hhigherActive⟩
    exact Or.inl ⟨residual, by
      simpa [startNextNonpreemptivePriorityJob, hhigherActive] using hhigherActive⟩
  · rcases hhigherCompleted with ⟨completedAt, hhigherCompleted⟩
    exact Or.inr (Or.inl ⟨completedAt,
      mem_completed_startNextNonpreemptivePriorityJob state higher completedAt hhigherCompleted⟩)
  · rcases hhigherWaiting with ⟨hhigherWaiting, hguard⟩
    cases hstate : state.active with
    | some active =>
        simpa [startNextNonpreemptivePriorityJob, hstate] using
          Or.inr (Or.inr ⟨hhigherWaiting, hguard⟩)
    | none =>
        have hhasWaiting : hasPriorityWaitingJob state :=
          ⟨higher.priority, List.length_pos_of_mem hhigherWaiting⟩
        let selected := nextPriorityWaitingClass state hhasWaiting
        have hselectedPositive : 0 < (state.waiting selected).length := by
          simpa [selected] using nextNonpreemptivePriority_positive
            (fun j => (state.waiting j).length) hhasWaiting
        cases hhead : state.waiting selected with
        | nil => simp [hhead] at hselectedPositive
        | cons head tail =>
            have hheadPriority : head.priority = selected :=
              hclass selected head (by simp [hhead])
            have hselectedLe : selected ≤ higher.priority := by
              exact nextPriorityWaitingClass_le_of_waiting state hhasWaiting higher.priority
                (List.length_pos_of_mem hhigherWaiting)
            have hnoLower : ∀ residual,
                (startNextNonpreemptivePriorityJob state).active ≠ some (lower, residual) := by
              intro residual hactive
              have hpair : (head, head.serviceWork) = (lower, residual) := by
                exact Option.some.inj (by
                  simpa [startNextNonpreemptivePriorityJob, hstate, hhasWaiting,
                    selected, hhead] using hactive)
              have hheadLower : head.priority = lower.priority :=
                congrArg NonpreemptivePriorityJob.priority (congrArg Prod.fst hpair)
              have hlowerLe : lower.priority ≤ higher.priority := by
                rw [← hheadLower, hheadPriority]
                exact hselectedLe
              exact (not_lt_of_ge hlowerLe) hpriority
            have hcontains : nonpreemptivePriorityWorkStateContainsJob
                (startNextNonpreemptivePriorityJob state) higher := by
              apply nonpreemptivePriorityWorkStateContainsJob_startNext state higher
              exact Or.inr (Or.inl ⟨higher.priority, hhigherWaiting⟩)
            rcases hcontains with hactive | hwaiting | hcompleted
            · exact Or.inl hactive
            · rcases hwaiting with ⟨j, hwaiting⟩
              have hclassNext : hasClassConsistentWaiting
                  (startNextNonpreemptivePriorityJob state) :=
                hasClassConsistentWaiting_startNextNonpreemptivePriorityJob state hclass
              have hj : higher.priority = j := hclassNext j higher hwaiting
              exact Or.inr (Or.inr ⟨by simpa [hj] using hwaiting, hnoLower⟩)
            · exact Or.inr (Or.inl hcompleted)

/-- A service completion preserves the strict-priority disposition.  If the
higher-priority customer was active, this completion explicitly records it;
if it was waiting, the following dispatch cannot choose the lower-priority
customer. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : higher.priority < lower.priority)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      (completeNonpreemptivePriorityWorkJob state) higher lower := by
  classical
  rcases hdisposition with hhigherActive | hhigherCompleted | hhigherWaiting
  · rcases hhigherActive with ⟨residual, hhigherActive⟩
    cases hstate : state.active with
    | none => simp [hstate] at hhigherActive
    | some active =>
        have hhigher : active.1 = higher := by
          exact congrArg Prod.fst (Option.some.inj (hstate.symm.trans hhigherActive))
        let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
          { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
        have hrecorded : (higher, state.currentTime) ∈ afterCompletion.completed := by
          simp [afterCompletion, hhigher]
        exact Or.inr (Or.inl ⟨state.currentTime, by
          simpa [completeNonpreemptivePriorityWorkJob, hstate, afterCompletion] using
            mem_completed_startNextNonpreemptivePriorityJob afterCompletion
              higher state.currentTime hrecorded⟩)
  · rcases hhigherCompleted with ⟨completedAt, hhigherCompleted⟩
    exact Or.inr (Or.inl ⟨completedAt,
      mem_completed_completeNonpreemptivePriorityWorkJob state higher completedAt hhigherCompleted⟩)
  · rcases hhigherWaiting with ⟨hhigherWaiting, hguard⟩
    cases hstate : state.active with
    | none =>
        simpa [completeNonpreemptivePriorityWorkJob, hstate] using
          Or.inr (Or.inr ⟨hhigherWaiting, hguard⟩)
    | some active =>
        let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
          { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
        have hafterClass : hasClassConsistentWaiting afterCompletion := by
          simpa [afterCompletion] using hclass
        have hafterDisposition :
            nonpreemptivePriorityStrictPrecedesDisposition afterCompletion higher lower := by
          refine Or.inr (Or.inr ⟨by simpa [afterCompletion] using hhigherWaiting, ?_⟩)
          intro residual hactive
          simp [afterCompletion] at hactive
        have hnext := nonpreemptivePriorityStrictPrecedesDisposition_startNext
          afterCompletion higher lower hafterClass hpriority hafterDisposition
        simpa [completeNonpreemptivePriorityWorkJob, hstate, afterCompletion] using hnext

/-- Admitting a new job preserves the strict-priority disposition.  The
dispatch performed before tail admission either keeps the higher-priority
customer live ahead of the lower one or records that it has already completed. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower newJob : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : higher.priority < lower.priority)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      (admitNonpreemptivePriorityJob state newJob) higher lower := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared := nonpreemptivePriorityStrictPrecedesDisposition_startNext
    state higher lower hclass hpriority hdisposition
  cases hactive : prepared.active with
  | none =>
      rcases hprepared with hhigherActive | hhigherCompleted | hhigherWaiting
      · rcases hhigherActive with ⟨residual, hhigherActive⟩
        exact (Option.some_ne_none (higher, residual)
          (hhigherActive.symm.trans hactive)).elim
      · rcases hhigherCompleted with ⟨completedAt, hhigherCompleted⟩
        exact Or.inr (Or.inl ⟨completedAt, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hhigherCompleted⟩)
      · have hnonidle := nonpreemptivePriorityWorkConserving_startNext state
        exact (hnonidle hactive ⟨higher.priority,
          List.length_pos_of_mem hhigherWaiting.1⟩).elim
  | some active =>
      rcases hprepared with hhigherActive | hhigherCompleted | hhigherWaiting
      · rcases hhigherActive with ⟨residual, hhigherActive⟩
        exact Or.inl ⟨residual, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive,
            enqueueNonpreemptivePriorityJob] using hhigherActive⟩
      · rcases hhigherCompleted with ⟨completedAt, hhigherCompleted⟩
        exact Or.inr (Or.inl ⟨completedAt, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive,
            completed_enqueueNonpreemptivePriorityJob] using hhigherCompleted⟩)
      · have hwaitPrepared : higher ∈ prepared.waiting higher.priority := by
          simpa [prepared] using hhigherWaiting.1
        have hhigherStillWaiting : higher ∈
            (enqueueNonpreemptivePriorityJob prepared newJob).waiting higher.priority := by
          by_cases hsame : newJob.priority = higher.priority
          · rw [← hsame, enqueueNonpreemptivePriorityJob_waiting_selected]
            exact List.mem_append_left _ (by simpa [hsame] using hwaitPrepared)
          · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne prepared newJob higher.priority
              (Ne.symm hsame)]
            exact hwaitPrepared
        refine Or.inr (Or.inr ⟨by
            simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hhigherStillWaiting, ?_⟩)
        intro residual hnewActive
        apply hhigherWaiting.2 residual
        simpa [admitNonpreemptivePriorityJob, prepared, hactive,
          enqueueNonpreemptivePriorityJob] using hnewActive

/-- Bounded service evolution preserves the strict-priority disposition.  The
class invariant is needed only when a service completion dispatches the next
waiting customer. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : higher.priority < lower.priority)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      (advanceNonpreemptivePriorityWorkState fuel target state) higher lower := by
  induction fuel generalizing state with
  | zero =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hdisposition
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityStrictPrecedesDisposition_timeUpdate
                state higher lower target hdisposition
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hdisposition
  | succ fuel ih =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hdisposition
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityStrictPrecedesDisposition_timeUpdate
                state higher lower target hdisposition
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let atCompletion : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hatCompletionClass : hasClassConsistentWaiting atCompletion := by
                simpa [atCompletion] using hclass
              have hatCompletionDisposition :
                  nonpreemptivePriorityStrictPrecedesDisposition atCompletion higher lower := by
                simpa [atCompletion] using
                  nonpreemptivePriorityStrictPrecedesDisposition_timeUpdate
                    state higher lower (state.currentTime + active.2) hdisposition
              let next := completeNonpreemptivePriorityWorkJob atCompletion
              have hnextClass : hasClassConsistentWaiting next := by
                dsimp [next]
                exact hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
                  atCompletion hatCompletionClass
              have hnextDisposition :
                  nonpreemptivePriorityStrictPrecedesDisposition next higher lower := by
                dsimp [next]
                exact nonpreemptivePriorityStrictPrecedesDisposition_complete
                  atCompletion higher lower hatCompletionClass hpriority hatCompletionDisposition
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, atCompletion, next] using ih next hnextClass hnextDisposition
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
                nonpreemptivePriorityStrictPrecedesDisposition_activeUpdate
                  state higher lower active hactive target
                  (active.2 - (target - state.currentTime)) hdisposition

/-- A finite chronological arrival replay preserves a strict-priority
disposition.  Class consistency is transported across both the finite service
advance and the following tail admission. -/
theorem nonpreemptivePriorityStrictPrecedesDisposition_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting initial)
    (hpriority : higher.priority < lower.priority)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition initial higher lower) :
    nonpreemptivePriorityStrictPrecedesDisposition
      (runNonpreemptivePriorityArrivalTrace initial jobs) higher lower := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hdisposition
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedClass : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hclass
      have hadvancedDisposition :
          nonpreemptivePriorityStrictPrecedesDisposition advanced higher lower := by
        simpa [advanced] using nonpreemptivePriorityStrictPrecedesDisposition_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial higher lower
          hclass hpriority hdisposition
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmittedClass : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob advanced job hadvancedClass
      have hadmittedDisposition :
          nonpreemptivePriorityStrictPrecedesDisposition admitted higher lower := by
        simpa [admitted] using nonpreemptivePriorityStrictPrecedesDisposition_admit
          advanced higher lower job hadvancedClass hpriority hadvancedDisposition
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using
        ih admitted hadmittedClass hadmittedDisposition

/-- Completion order induced by a strict priority relation. -/
def nonpreemptivePriorityStrictCompletionOrder
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId) : Prop :=
  ∀ lowerTime, (lower, lowerTime) ∈ state.completed →
    ∃ higherTime, (higher, higherTime) ∈ state.completed ∧ higherTime ≤ lowerTime

/-- Completing a queue state preserves strict-priority completion order when
the lower-priority literal job has at most one occurrence.  A newly recorded
lower-priority completion is impossible while the higher-priority customer is
waiting, and otherwise that higher customer is already active or completed. -/
theorem nonpreemptivePriorityStrictCompletionOrder_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hdistinct : higher ≠ lower)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state lower ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (completeNonpreemptivePriorityWorkJob state) higher lower := by
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
          _ = afterCompletion.completed := completed_startNextNonpreemptivePriorityJob afterCompletion
          _ = (active.1, state.currentTime) :: state.completed := rfl
      intro lowerTime hlower
      rw [hledger] at hlower
      rcases List.mem_cons.mp hlower with hnew | hold
      · have hactiveJob : active.1 = lower := by
          exact (congrArg Prod.fst hnew).symm
        have htime : lowerTime = state.currentTime := congrArg Prod.snd hnew
        have hactiveLower : state.active = some (lower, active.2) := by
          have hpair : active = (lower, active.2) := Prod.ext hactiveJob rfl
          rw [hactive, hpair]
        rcases hdisposition with hhigherActive | hhigherCompleted | hhigherWaiting
        · rcases hhigherActive with ⟨higherResidual, hhigherActive⟩
          have heq : higher = lower := by
            have hpairs : (higher, higherResidual) = (lower, active.2) :=
              Option.some.inj (hhigherActive.symm.trans hactiveLower)
            exact congrArg Prod.fst hpairs
          exact (hdistinct heq).elim
        · rcases hhigherCompleted with ⟨higherTime, hhigherCompleted⟩
          refine ⟨higherTime,
            mem_completed_completeNonpreemptivePriorityWorkJob
              state higher higherTime hhigherCompleted, ?_⟩
          rw [htime]
          exact htimes higher higherTime hhigherCompleted
        · exact (hhigherWaiting.2 active.2 hactiveLower).elim
      · rcases horder lowerTime hold with ⟨higherTime, hhigherCompleted, htime⟩
        exact ⟨higherTime,
          mem_completed_completeNonpreemptivePriorityWorkJob
            state higher higherTime hhigherCompleted, htime⟩

/-- Clock changes preserve strict-priority completion order. -/
theorem nonpreemptivePriorityStrictCompletionOrder_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId) (time : ℝ)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      { state with currentTime := time } higher lower := by
  simpa [nonpreemptivePriorityStrictCompletionOrder] using horder

/-- Dispatch, tail enqueue, and admission do not add completion records, so
they preserve strict-priority completion order. -/
theorem nonpreemptivePriorityStrictCompletionOrder_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (startNextNonpreemptivePriorityJob state) higher lower := by
  intro lowerTime hlower
  rcases horder lowerTime (by
    simpa [completed_startNextNonpreemptivePriorityJob] using hlower) with
    ⟨higherTime, hhigher, htime⟩
  exact ⟨higherTime, by
    simpa [completed_startNextNonpreemptivePriorityJob] using hhigher, htime⟩

theorem nonpreemptivePriorityStrictCompletionOrder_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower newJob : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (enqueueNonpreemptivePriorityJob state newJob) higher lower := by
  simpa [nonpreemptivePriorityStrictCompletionOrder,
    enqueueNonpreemptivePriorityJob] using horder

theorem nonpreemptivePriorityStrictCompletionOrder_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower newJob : NonpreemptivePriorityJob n JobId)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (admitNonpreemptivePriorityJob state newJob) higher lower := by
  intro lowerTime hlower
  rcases horder lowerTime (by
    simpa [completed_admitNonpreemptivePriorityJob] using hlower) with
    ⟨higherTime, hhigher, htime⟩
  exact ⟨higherTime, by
    simpa [completed_admitNonpreemptivePriorityJob] using hhigher, htime⟩

/-- Bounded service evolution preserves the strict-priority completion order.
The class-consistency invariant is used exactly at the dispatch following a
completion, where it prevents a waiting higher-priority customer from being
skipped in favor of the lower one. -/
theorem nonpreemptivePriorityStrictCompletionOrder_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : higher.priority < lower.priority)
    (hdistinct : higher ≠ lower)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state lower ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime state)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition state higher lower)
    (horder : nonpreemptivePriorityStrictCompletionOrder state higher lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (advanceNonpreemptivePriorityWorkState fuel target state) higher lower := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using horder
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityStrictCompletionOrder_timeUpdate
                state higher lower target horder
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using horder
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using horder
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityStrictCompletionOrder_timeUpdate
                state higher lower target horder
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedClass : hasClassConsistentWaiting completedState := by
                simpa [completedState] using hclass
              have hcompletedWork : nonnegativeNonpreemptivePriorityResidualWork completedState := by
                constructor
                · intro job hjob
                  simpa [completedState] using hwork.1 job hjob
                · intro i job hmember
                  simpa [completedState] using hwork.2 i job hmember
              have hcompletedMultiplicity :
                  nonpreemptivePriorityWorkStateJobMultiplicity completedState lower ≤ 1 := by
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
                  nonpreemptivePriorityStrictPrecedesDisposition completedState higher lower := by
                simpa [completedState] using
                  nonpreemptivePriorityStrictPrecedesDisposition_timeUpdate
                    state higher lower (state.currentTime + active.2) hdisposition
              have hcompletedOrder :
                  nonpreemptivePriorityStrictCompletionOrder completedState higher lower := by
                simpa [completedState] using
                  nonpreemptivePriorityStrictCompletionOrder_timeUpdate
                    state higher lower (state.currentTime + active.2) horder
              let next := completeNonpreemptivePriorityWorkJob completedState
              have hnextClass : hasClassConsistentWaiting next := by
                dsimp [next]
                exact hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
                  completedState hcompletedClass
              have hnextWork : nonnegativeNonpreemptivePriorityResidualWork next := by
                dsimp [next]
                exact nonnegativeNonpreemptivePriorityResidualWork_complete
                  completedState hcompletedWork
              have hnextMultiplicity :
                  nonpreemptivePriorityWorkStateJobMultiplicity next lower ≤ 1 := by
                dsimp [next]
                rw [nonpreemptivePriorityWorkStateJobMultiplicity_complete]
                exact hcompletedMultiplicity
              have hnextTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime next := by
                dsimp [next]
                exact nonpreemptivePriorityCompletionTimesLeCurrentTime_complete
                  completedState hcompletedTimes
              have hnextDisposition :
                  nonpreemptivePriorityStrictPrecedesDisposition next higher lower := by
                dsimp [next]
                exact nonpreemptivePriorityStrictPrecedesDisposition_complete
                  completedState higher lower hcompletedClass hpriority hcompletedDisposition
              have hnextOrder : nonpreemptivePriorityStrictCompletionOrder next higher lower := by
                dsimp [next]
                exact nonpreemptivePriorityStrictCompletionOrder_complete
                  completedState higher lower hdistinct hcompletedMultiplicity hcompletedTimes
                  hcompletedDisposition hcompletedOrder
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState, next] using
                ih next hnextClass hnextWork hnextMultiplicity hnextTimes hnextDisposition hnextOrder
            · have hpartialDisposition :=
                nonpreemptivePriorityStrictPrecedesDisposition_activeUpdate
                  state higher lower active hactive target
                  (active.2 - (target - state.currentTime)) hdisposition
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
                nonpreemptivePriorityStrictCompletionOrder_timeUpdate
                  state higher lower target horder

/-- A finite arrival replay preserves the literal completion order of a
higher-priority customer and a distinct lower-priority customer.  The priority
guard is transported through each finite service segment and each admission. -/
theorem nonpreemptivePriorityStrictCompletionOrder_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting initial)
    (hpriority : higher.priority < lower.priority)
    (hdistinct : higher ≠ lower)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial lower ≤ 1)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hdisposition : nonpreemptivePriorityStrictPrecedesDisposition initial higher lower)
    (horder : nonpreemptivePriorityStrictCompletionOrder initial higher lower)
    (hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork)
    (hjobsDistinct : ∀ job ∈ jobs, job ≠ lower) :
    nonpreemptivePriorityStrictCompletionOrder
      (runNonpreemptivePriorityArrivalTrace initial jobs) higher lower := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using horder
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedClass : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hclass
      have hadvancedWork : nonnegativeNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using nonnegativeNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadvancedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity advanced lower ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity advanced lower =
            nonpreemptivePriorityWorkStateJobMultiplicity initial lower by
          dsimp [advanced]
          exact nonpreemptivePriorityWorkStateJobMultiplicity_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial lower]
        exact hmultiplicity
      have hadvancedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime advanced := by
        simpa [advanced] using nonpreemptivePriorityCompletionTimesLeCurrentTime_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork htimes
      have hadvancedDisposition :
          nonpreemptivePriorityStrictPrecedesDisposition advanced higher lower := by
        simpa [advanced] using nonpreemptivePriorityStrictPrecedesDisposition_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial higher lower
          hclass hpriority hdisposition
      have hadvancedOrder : nonpreemptivePriorityStrictCompletionOrder advanced higher lower := by
        simpa [advanced] using nonpreemptivePriorityStrictCompletionOrder_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial higher lower
          hclass hpriority hdistinct hwork hmultiplicity htimes hdisposition horder
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hjobWork : 0 ≤ job.serviceWork := hjobsWork job (by simp)
      have hjobDistinct : job ≠ lower := hjobsDistinct job (by simp)
      have hadmittedClass : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob advanced job hadvancedClass
      have hadmittedWork : nonnegativeNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using nonnegativeNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedWork hjobWork
      have hadmittedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity admitted lower ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity admitted lower =
            nonpreemptivePriorityWorkStateJobMultiplicity advanced lower by
          dsimp [admitted]
          exact nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne
            advanced job lower hjobDistinct]
        exact hadvancedMultiplicity
      have hadmittedTimes : nonpreemptivePriorityCompletionTimesLeCurrentTime admitted := by
        simpa [admitted] using
          nonpreemptivePriorityCompletionTimesLeCurrentTime_admit advanced job hadvancedTimes
      have hadmittedDisposition :
          nonpreemptivePriorityStrictPrecedesDisposition admitted higher lower := by
        simpa [admitted] using nonpreemptivePriorityStrictPrecedesDisposition_admit
          advanced higher lower job hadvancedClass hpriority hadvancedDisposition
      have hadmittedOrder : nonpreemptivePriorityStrictCompletionOrder admitted higher lower := by
        simpa [admitted] using nonpreemptivePriorityStrictCompletionOrder_admit
          advanced higher lower job hadvancedOrder
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using
        ih admitted hadmittedClass hadmittedWork hadmittedMultiplicity
          hadmittedTimes hadmittedDisposition hadmittedOrder
          (fun other hother => hjobsWork other (by simp [hother]))
          (fun other hother => hjobsDistinct other (by simp [hother]))

/-- In a no-duplicate arrival trace, a higher-priority customer present at the
initial epoch completes no later than any distinct lower-priority input
customer.  The proof starts at the lower customer's unique admission and
then transports the literal completion order through the remaining trace. -/
theorem nonpreemptivePriorityStrictCompletionOrder_run_of_initial_contains
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (higher lower : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting initial)
    (hwork : nonnegativeNonpreemptivePriorityResidualWork initial)
    (htimes : nonpreemptivePriorityCompletionTimesLeCurrentTime initial)
    (hhigher : nonpreemptivePriorityWorkStateContainsJob initial higher)
    (hnotlower : ¬ nonpreemptivePriorityWorkStateContainsJob initial lower)
    (hnodup : jobs.Nodup)
    (hlower : lower ∈ jobs)
    (hpriority : higher.priority < lower.priority)
    (hjobsWork : ∀ job ∈ jobs, 0 ≤ job.serviceWork) :
    nonpreemptivePriorityStrictCompletionOrder
      (runNonpreemptivePriorityArrivalTrace initial jobs) higher lower := by
  induction jobs generalizing initial with
  | nil => simp at hlower
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
      have hadvancedHigher : nonpreemptivePriorityWorkStateContainsJob advanced higher := by
        simpa [advanced] using nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial higher hhigher
      have hadvancedNotLower : ¬ nonpreemptivePriorityWorkStateContainsJob advanced lower := by
        intro hcontains
        apply hnotlower
        exact nonpreemptivePriorityWorkStateContainsJob_advance_reverse
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial lower hcontains
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
      have hadmittedHigher : nonpreemptivePriorityWorkStateContainsJob admitted higher := by
        simpa [admitted] using nonpreemptivePriorityWorkStateContainsJob_admit
          advanced newJob higher hadvancedHigher
      rcases List.mem_cons.mp hlower with hnew | htail
      · subst newJob
        have hdistinct : higher ≠ lower := by
          intro heq
          subst higher
          exact hnotlower hhigher
        have hadvancedNotActive : ∀ residual,
            advanced.active ≠ some (lower, residual) := by
          intro residual hactive
          exact hadvancedNotLower (Or.inl ⟨residual, hactive⟩)
        have hadvancedDisposition :
            nonpreemptivePriorityStrictPrecedesDisposition advanced higher lower := by
          exact nonpreemptivePriorityStrictPrecedesDisposition_of_contains
            advanced higher lower hadvancedClass hadvancedHigher hadvancedNotActive
        have hadmittedDisposition :
            nonpreemptivePriorityStrictPrecedesDisposition admitted higher lower := by
          simpa [admitted] using nonpreemptivePriorityStrictPrecedesDisposition_admit
            advanced higher lower lower hadvancedClass hpriority hadvancedDisposition
        have hadmittedOrder : nonpreemptivePriorityStrictCompletionOrder admitted higher lower := by
          intro lowerTime hlowerCompleted
          rw [completed_admitNonpreemptivePriorityJob] at hlowerCompleted
          exact (hadvancedNotLower (Or.inr (Or.inr ⟨lowerTime, hlowerCompleted⟩))).elim
        have hadmittedMultiplicity :
            nonpreemptivePriorityWorkStateJobMultiplicity admitted lower ≤ 1 := by
          have hzero : nonpreemptivePriorityWorkStateJobMultiplicity advanced lower = 0 :=
            nonpreemptivePriorityWorkStateJobMultiplicity_eq_zero_of_not_contains
              advanced lower hadvancedNotLower
          rw [show nonpreemptivePriorityWorkStateJobMultiplicity admitted lower =
              nonpreemptivePriorityWorkStateJobMultiplicity advanced lower + 1 by
            simpa [admitted] using
              nonpreemptivePriorityWorkStateJobMultiplicity_admit_self advanced lower,
            hzero]
        have htailDistinct : ∀ job ∈ jobs, job ≠ lower := by
          intro job hjob heq
          subst job
          exact hheadNodup hjob
        have hrun := nonpreemptivePriorityStrictCompletionOrder_run
          admitted jobs higher lower hadmittedClass hpriority hdistinct hadmittedWork
          hadmittedMultiplicity hadmittedTimes hadmittedDisposition hadmittedOrder
          (fun job hjob => hjobsWork job (by simp [hjob])) htailDistinct
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun
      · have hnewNeLower : newJob ≠ lower := by
          intro heq
          subst newJob
          exact hheadNodup htail
        have hadmittedNotLower : ¬ nonpreemptivePriorityWorkStateContainsJob admitted lower := by
          intro hcontains
          rcases nonpreemptivePriorityWorkStateContainsJob_admit_reverse
            advanced newJob lower (by simpa [admitted] using hcontains) with hadvanced | heq
          · exact hadvancedNotLower hadvanced
          · exact hnewNeLower heq.symm
        have hrun := ih admitted hadmittedClass hadmittedWork hadmittedTimes
          hadmittedHigher hadmittedNotLower htailNodup htail
          (fun job hjob => hjobsWork job (by simp [hjob]))
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun

end

end AppliedModelingLib.Queueing
