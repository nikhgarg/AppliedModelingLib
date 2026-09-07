import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedCompletionBound

/-!
# Strict tagged completion bounds in nonpreemptive-priority traces

A tagged customer that is still waiting at a service-decision epoch cannot
finish after merely its own service requirement: another active customer must
first receive a positive amount of service.  This file records the strict
version of the usual tagged completion bound and its deterministic transition
rules.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Every completion of the tag is strictly later than the given origin plus
its declared service work; the active case records the corresponding future
completion epoch. -/
def nonpreemptivePriorityTaggedCompletionStrictLowerBound
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  origin ≤ state.currentTime ∧
    (∀ completedAt, (tag, completedAt) ∈ state.completed →
      origin + tag.serviceWork < completedAt) ∧
    (∀ residual, state.active = some (tag, residual) →
      origin + tag.serviceWork < state.currentTime + residual)

/-- FIFO membership of a unique literal tag establishes the strict bound at
the current clock: the tag is neither active nor already completed there. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_of_mem_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hwaiting : tag ∈ state.waiting i)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound state.currentTime tag state := by
  have hdisjoint := not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
    state tag i hwaiting hmultiplicity
  constructor
  · exact le_rfl
  constructor
  · intro completedAt hcompleted
    exact (hdisjoint.2 ⟨completedAt, hcompleted⟩).elim
  · intro residual hactive
    exact (hdisjoint.1 ⟨residual, hactive⟩).elim

/-- Moving an idle-tag bound's clock forward preserves its strict completion
bound. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_timeUpdate
    {n : ℕ} {JobId : Type*}
    (origin target : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state)
    (htarget : state.currentTime ≤ target) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      { state with currentTime := target } := by
  constructor
  · exact hbound.1.trans htarget
  constructor
  · intro completedAt hcompleted
    exact hbound.2.1 completedAt (by simpa using hcompleted)
  · intro residual hactive
    have hprevious := hbound.2.2 residual (by simpa using hactive)
    linarith

/-- Enqueueing any job does not alter a strict tagged completion bound. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_enqueue
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag newJob : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (enqueueNonpreemptivePriorityJob state newJob) := by
  simpa [nonpreemptivePriorityTaggedCompletionStrictLowerBound,
    enqueueNonpreemptivePriorityJob] using hbound

/-- Dispatching preserves a strict tagged bound in a work-conserving state.
The only potentially new active tag would have to come from an idle state
with waiting work, which work conservation excludes. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_startNext
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state)
    (hsafe : origin < state.currentTime ∨ nonpreemptivePriorityWorkConserving state) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (startNextNonpreemptivePriorityJob state) := by
  classical
  constructor
  · rw [startNextNonpreemptivePriorityJob_currentTime]
    exact hbound.1
  constructor
  · intro completedAt hcompleted
    apply hbound.2.1 completedAt
    simpa [completed_startNextNonpreemptivePriorityJob] using hcompleted
  · intro residual htag
    cases hstate : state.active with
    | some active =>
        have htag' : state.active = some (tag, residual) := by
          simpa [startNextNonpreemptivePriorityJob, hstate] using htag
        simpa [startNextNonpreemptivePriorityJob_currentTime] using hbound.2.2 residual htag'
    | none =>
        by_cases hwaiting : hasPriorityWaitingJob state
        · let selected := nextPriorityWaitingClass state hwaiting
          cases hhead : state.waiting selected with
          | nil =>
              simp [startNextNonpreemptivePriorityJob, hstate, hwaiting,
                selected, hhead] at htag
          | cons head tail =>
              have hpair : (head, head.serviceWork) = (tag, residual) := by
                exact Option.some.inj (by
                  simpa [startNextNonpreemptivePriorityJob, hstate, hwaiting,
                    selected, hhead] using htag)
              have htagEq : head = tag := congrArg Prod.fst hpair
              have hresidual : head.serviceWork = residual := congrArg Prod.snd hpair
              rcases hsafe with htime | hwork
              · rw [← htagEq, ← hresidual,
                  startNextNonpreemptivePriorityJob_currentTime]
                linarith
              · exact (hwork hstate hwaiting).elim
        · simp [startNextNonpreemptivePriorityJob, hstate, hwaiting] at htag

/-- Completing an active service after its residual amount preserves the
strict tagged bound.  If the completed job is the tag, the active strict
bound becomes the strict inequality for its newly recorded completion. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_complete_after_residual
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state)
    (hactive : state.active = some active)
    (hpositive : 0 < active.2) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (completeNonpreemptivePriorityWorkJob
        { state with currentTime := state.currentTime + active.2 }) := by
  classical
  let completedState : NonpreemptivePriorityWorkState n JobId :=
    { state with currentTime := state.currentTime + active.2 }
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { completedState with active := none, completed :=
      (active.1, completedState.currentTime) :: completedState.completed }
  have hafter : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      afterCompletion := by
    constructor
    · dsimp [afterCompletion, completedState]
      linarith [hbound.1]
    constructor
    · intro completedAt hcompleted
      rw [show afterCompletion.completed =
          (active.1, completedState.currentTime) :: completedState.completed by rfl] at hcompleted
      rcases List.mem_cons.mp hcompleted with hnew | hold
      · have htag : tag = active.1 := congrArg Prod.fst hnew
        have htime : completedAt = completedState.currentTime := congrArg Prod.snd hnew
        have hactiveTag : state.active = some (tag, active.2) := by
          rw [hactive, htag]
        have hprevious := hbound.2.2 active.2 hactiveTag
        dsimp [completedState] at htime
        linarith
      · apply hbound.2.1 completedAt
        simpa [afterCompletion, completedState] using hold
    · intro residual htag
      simp [afterCompletion] at htag
  have hnext := nonpreemptivePriorityTaggedCompletionStrictLowerBound_startNext
    origin tag afterCompletion hafter (Or.inl (by
      dsimp [afterCompletion, completedState]
      linarith [hbound.1, hpositive]))
  simpa [completeNonpreemptivePriorityWorkJob, completedState, afterCompletion,
    hactive] using hnext

/-- Bounded service evolution preserves the strict tagged completion bound
when all active residual works are positive.  A completed service advances
the clock strictly before any possible tagged dispatch. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (origin target : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state)
    (hpositive : positiveNonpreemptivePriorityResidualWork state) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              (nonpreemptivePriorityTaggedCompletionStrictLowerBound_timeUpdate
                origin target tag state hbound htime)
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hbound
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hbound
      · cases hactive : state.active with
        | none =>
            have htime : state.currentTime ≤ target := le_of_lt (lt_of_not_ge htarget)
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              (nonpreemptivePriorityTaggedCompletionStrictLowerBound_timeUpdate
                origin target tag state hbound htime)
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedBound : nonpreemptivePriorityTaggedCompletionStrictLowerBound
                  origin tag (completeNonpreemptivePriorityWorkJob completedState) := by
                simpa [completedState] using
                  (nonpreemptivePriorityTaggedCompletionStrictLowerBound_complete_after_residual
                    origin tag state active hbound hactive (hpositive.1 active hactive))
              have hcompletedPositive : positiveNonpreemptivePriorityResidualWork
                  completedState := by
                constructor
                · intro other hother
                  simpa [completedState] using hpositive.1 other hother
                · intro j other hmember
                  simpa [completedState] using hpositive.2 j other hmember
              have hnextPositive : positiveNonpreemptivePriorityResidualWork
                  (completeNonpreemptivePriorityWorkJob completedState) := by
                exact positiveNonpreemptivePriorityResidualWork_complete
                  completedState hcompletedPositive
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState)
                hcompletedBound hnextPositive
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using hind
            · constructor
              · have horigin : origin ≤ target :=
                  hbound.1.trans (le_of_lt (lt_of_not_ge htarget))
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] using horigin
              constructor
              · intro completedAt hcompleted
                apply hbound.2.1 completedAt
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete] using hcompleted
              · intro residual htag
                have hpair : (active.1,
                    active.2 - (target - state.currentTime)) = (tag, residual) := by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using htag
                have htagEq : active.1 = tag := congrArg Prod.fst hpair
                have hresidual : active.2 - (target - state.currentTime) = residual :=
                  congrArg Prod.snd hpair
                have hactiveTag : state.active = some (tag, active.2) := by
                  have hactivePair : active = (tag, active.2) := by
                    apply Prod.ext
                    · exact htagEq
                    · rfl
                  rw [hactive, hactivePair]
                have hprevious := hbound.2.2 active.2 hactiveTag
                have hcurrent :
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).currentTime =
                      target := by
                  simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                rw [hcurrent, ← hresidual]
                linarith

/-- Admitting a job different from the tag preserves its strict completion
bound in a work-conserving state. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_admit_of_ne
    {n : ℕ} {JobId : Type*}
    (origin : ℝ) (tag newJob : NonpreemptivePriorityJob n JobId)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hnew : newJob ≠ tag) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (admitNonpreemptivePriorityJob state newJob) := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag prepared := by
    simpa [prepared] using
      (nonpreemptivePriorityTaggedCompletionStrictLowerBound_startNext
        origin tag state hbound (Or.inr hwork))
  cases hactive : prepared.active with
  | none =>
      constructor
      · rw [admitNonpreemptivePriorityJob_currentTime]
        rw [← startNextNonpreemptivePriorityJob_currentTime state]
        simpa [prepared] using hprepared.1
      constructor
      · intro completedAt hcompleted
        apply hprepared.2.1 completedAt
        simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted
      · intro residual htag
        have hpair : (newJob, newJob.serviceWork) = (tag, residual) := by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using htag
        exact (hnew (congrArg Prod.fst hpair)).elim
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        (nonpreemptivePriorityTaggedCompletionStrictLowerBound_enqueue
          origin tag newJob prepared hprepared)

/-- Replaying a finite list of positive-work arrivals that excludes the tag
preserves its strict completion bound. -/
theorem nonpreemptivePriorityTaggedCompletionStrictLowerBound_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (origin : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (hbound : nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag initial)
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hjobsWork : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hjobsDistinct : ∀ job ∈ jobs, job ≠ tag) :
    nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hbound
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvancedBound :
          nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag advanced := by
        simpa [advanced] using
          nonpreemptivePriorityTaggedCompletionStrictLowerBound_advance
            (totalNonpreemptivePriorityWorkJobs initial) origin job.arrivalTime tag initial
            hbound hpositive
      have hadvancedPositive : positiveNonpreemptivePriorityResidualWork advanced := by
        simpa [advanced] using positiveNonpreemptivePriorityResidualWork_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hpositive
      have hadvancedWork : nonpreemptivePriorityWorkConserving advanced := by
        simpa [advanced] using nonpreemptivePriorityWorkConserving_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hjobWork : 0 < job.serviceWork := hjobsWork job (by simp)
      have hjobDistinct : job ≠ tag := hjobsDistinct job (by simp)
      have hadmittedBound :
          nonpreemptivePriorityTaggedCompletionStrictLowerBound origin tag admitted := by
        simpa [admitted] using
          nonpreemptivePriorityTaggedCompletionStrictLowerBound_admit_of_ne
            origin tag job advanced hadvancedBound hadvancedWork hjobDistinct
      have hadmittedPositive : positiveNonpreemptivePriorityResidualWork admitted := by
        simpa [admitted] using positiveNonpreemptivePriorityResidualWork_admit
          advanced job hadvancedPositive hjobWork
      have hadmittedWork : nonpreemptivePriorityWorkConserving admitted := by
        simpa [admitted] using nonpreemptivePriorityWorkConserving_admit advanced job
      have htailWork : ∀ other ∈ jobs, 0 < other.serviceWork := by
        intro other hother
        exact hjobsWork other (by simp [hother])
      have htailDistinct : ∀ other ∈ jobs, other ≠ tag := by
        intro other hother
        exact hjobsDistinct other (by simp [hother])
      have htail := ih admitted hadmittedBound hadmittedPositive hadmittedWork
        htailWork htailDistinct
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using htail

/-- If the unique tagged job is still waiting in a positive-work,
work-conserving state, every completion subsequently recorded for that tag is
strictly later than the current clock plus its own service work. -/
theorem taggedCompletion_gt_currentTime_add_service_of_mem_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (target completedAt : ℝ)
    (hwaiting : tag ∈ state.waiting i)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hjobsWork : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hjobsDistinct : ∀ job ∈ jobs, job ≠ tag)
    (hcompleted : (tag, completedAt) ∈
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace state jobs)) target
        (runNonpreemptivePriorityArrivalTrace state jobs)).completed) :
    state.currentTime + tag.serviceWork < completedAt := by
  let afterArrivals := runNonpreemptivePriorityArrivalTrace state jobs
  have hinitial : nonpreemptivePriorityTaggedCompletionStrictLowerBound
      state.currentTime tag state := by
    exact nonpreemptivePriorityTaggedCompletionStrictLowerBound_of_mem_waiting
      state tag i hwaiting hmultiplicity
  have hrun : nonpreemptivePriorityTaggedCompletionStrictLowerBound
      state.currentTime tag afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedCompletionStrictLowerBound_run
        state jobs state.currentTime tag hinitial hpositive hwork hjobsWork hjobsDistinct
  have hpositiveRun : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using
      positiveNonpreemptivePriorityResidualWork_run state jobs hpositive hjobsWork
  have hfinal : nonpreemptivePriorityTaggedCompletionStrictLowerBound
      state.currentTime tag
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) target afterArrivals) := by
    exact nonpreemptivePriorityTaggedCompletionStrictLowerBound_advance
      (totalNonpreemptivePriorityWorkJobs afterArrivals) state.currentTime target tag
      afterArrivals hrun hpositiveRun
  exact hfinal.2.1 completedAt (by simpa [afterArrivals] using hcompleted)

end

end AppliedModelingLib.Queueing
