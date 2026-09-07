import AppliedModelingLib.Queueing.NonpreemptivePriorityFiniteTrace

/-!
# Work conservation of finite nonpreemptive-priority traces

A finite priority state is work-conserving when an idle server has no waiting
job.  This property is independent of the numerical service requirements and
is preserved by every operation of the deterministic trace.
-/

namespace AppliedModelingLib
namespace Queueing

/-- An idle server has no waiting work. -/
def nonpreemptivePriorityWorkConserving
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  state.active = none → ¬ hasPriorityWaitingJob state

/-- Selecting the next priority job produces a work-conserving state even
from an arbitrary finite input state. -/
theorem nonpreemptivePriorityWorkConserving_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWorkConserving (startNextNonpreemptivePriorityJob state) := by
  classical
  intro hactive hwaiting
  cases hstate : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob, hstate] at hactive
  | none =>
      by_cases hwaitingState : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaitingState
        have hselected : 0 < (state.waiting selected).length :=
          nextNonpreemptivePriority_positive
            (fun i => (state.waiting i).length) hwaitingState
        cases hhead : state.waiting selected with
        | nil => simp [hhead] at hselected
        | cons head tail =>
            simp [startNextNonpreemptivePriorityJob, hstate, hwaitingState,
              selected, hhead] at hactive
      · simpa [startNextNonpreemptivePriorityJob, hstate, hwaitingState] using hwaiting

/-- Every admission leaves the server busy. -/
theorem active_ne_none_admitNonpreemptivePriorityJob
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    (admitNonpreemptivePriorityJob state job).active ≠ none := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  cases hactive : prepared.active with
  | none => simp [admitNonpreemptivePriorityJob, prepared, hactive]
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive,
        enqueueNonpreemptivePriorityJob] using Option.some_ne_none active

/-- Admitting a job produces a work-conserving state. -/
theorem nonpreemptivePriorityWorkConserving_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    nonpreemptivePriorityWorkConserving (admitNonpreemptivePriorityJob state job) := by
  intro hactive
  exact (active_ne_none_admitNonpreemptivePriorityJob state job hactive).elim

/-- Completion preserves work conservation whenever the incoming state was
work-conserving. -/
theorem nonpreemptivePriorityWorkConserving_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonpreemptivePriorityWorkConserving state) :
    nonpreemptivePriorityWorkConserving (completeNonpreemptivePriorityWorkJob state) := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hwork
  | some active =>
      let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
        { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
      have hnext := nonpreemptivePriorityWorkConserving_startNext afterCompletion
      simpa [completeNonpreemptivePriorityWorkJob, hactive, afterCompletion] using hnext

/-- Bounded service evolution preserves work conservation. -/
theorem nonpreemptivePriorityWorkConserving_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hwork : nonpreemptivePriorityWorkConserving state) :
    nonpreemptivePriorityWorkConserving
      (advanceNonpreemptivePriorityWorkState fuel target state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            intro _ hwaiting
            exact hwork hactive (by
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hwaiting)
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hwork
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hwork
      · cases hactive : state.active with
        | none =>
            intro _ hwaiting
            exact hwork hactive (by
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hwaiting)
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAt : nonpreemptivePriorityWorkConserving completedAt := by
                intro hnone
                exact (Option.some_ne_none active
                  (by simpa [completedAt, hactive] using hnone)).elim
              have hstep := nonpreemptivePriorityWorkConserving_complete
                completedAt hcompletedAt
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt) hstep
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedAt] using hind
            · intro hnone
              exact (Option.some_ne_none (active.1, active.2 - (target - state.currentTime))
                (by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                    hcomplete] using hnone)).elim

/-- A finite arrival trace begun from a work-conserving state remains
work-conserving. -/
theorem nonpreemptivePriorityWorkConserving_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hinitial : nonpreemptivePriorityWorkConserving initial) :
    nonpreemptivePriorityWorkConserving
      (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hinitial
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : nonpreemptivePriorityWorkConserving advanced := by
        simpa [advanced] using
          nonpreemptivePriorityWorkConserving_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hinitial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hadmitted : nonpreemptivePriorityWorkConserving admitted := by
        simpa [admitted] using nonpreemptivePriorityWorkConserving_admit advanced job
      simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted] using
        ih admitted hadmitted

end Queueing
end AppliedModelingLib
