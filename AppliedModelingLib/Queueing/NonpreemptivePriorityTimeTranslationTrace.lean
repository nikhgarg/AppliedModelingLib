import AppliedModelingLib.Queueing.NonpreemptivePriorityTimeTranslation

/-!
# Time translation of finite nonpreemptive-priority traces

This module lifts the time-origin change for finite queue states through the
deterministic arrival and service operations.  It is an exact covariance
statement: a replay expressed in shifted coordinates has the shifted replay
state, including its completion ledger.
-/

namespace AppliedModelingLib
namespace Queueing

noncomputable section

/-- A time translation preserves whether any class-FIFO list is nonempty. -/
theorem hasPriorityWaitingJob_translate_iff
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    hasPriorityWaitingJob (translateNonpreemptivePriorityWorkState offset state) ↔
      hasPriorityWaitingJob state := by
  unfold hasPriorityWaitingJob translateNonpreemptivePriorityWorkState
  simp

/-- The selected class is invariant under a change of time origin. -/
theorem nextPriorityWaitingClass_translate
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hwaiting : hasPriorityWaitingJob state) :
    nextPriorityWaitingClass (translateNonpreemptivePriorityWorkState offset state)
        ((hasPriorityWaitingJob_translate_iff offset state).mpr hwaiting) =
      nextPriorityWaitingClass state hwaiting := by
  unfold nextPriorityWaitingClass
  congr 1
  funext i
  simp [translateNonpreemptivePriorityWorkState]

/-- Appending a shifted arrival to a shifted state agrees with shifting the
state after the original append. -/
theorem translateNonpreemptivePriorityWorkState_enqueue
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (enqueueNonpreemptivePriorityJob state job) =
      enqueueNonpreemptivePriorityJob
        (translateNonpreemptivePriorityWorkState offset state)
        (translateNonpreemptivePriorityJob offset job) := by
  classical
  cases state
  simp [translateNonpreemptivePriorityWorkState,
    enqueueNonpreemptivePriorityJob, Function.update]
  funext i
  by_cases hi : i = job.priority <;> simp [Function.update, hi]

/-- Starting service commutes with a change of time origin. -/
theorem translateNonpreemptivePriorityWorkState_startNext
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (startNextNonpreemptivePriorityJob state) =
      startNextNonpreemptivePriorityJob
        (translateNonpreemptivePriorityWorkState offset state) := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob,
        translateNonpreemptivePriorityWorkState, hactive]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · have hwaitingTranslated : hasPriorityWaitingJob
            (translateNonpreemptivePriorityWorkState offset state) :=
            (hasPriorityWaitingJob_translate_iff offset state).mpr hwaiting
        have hselected :
            nextPriorityWaitingClass (translateNonpreemptivePriorityWorkState offset state)
                hwaitingTranslated =
              nextPriorityWaitingClass state hwaiting := by
          exact nextPriorityWaitingClass_translate offset state hwaiting
        cases hhead : state.waiting (nextPriorityWaitingClass state hwaiting) with
        | nil =>
            have hheadTranslated :
                (translateNonpreemptivePriorityWorkState offset state).waiting
                    (nextPriorityWaitingClass
                      (translateNonpreemptivePriorityWorkState offset state)
                      hwaitingTranslated) = [] := by
              rw [hselected]
              simp [translateNonpreemptivePriorityWorkState, hhead]
            have hstartTranslated :
                startNextNonpreemptivePriorityJob
                    (translateNonpreemptivePriorityWorkState offset state) =
                  translateNonpreemptivePriorityWorkState offset state := by
              unfold startNextNonpreemptivePriorityJob
              rw [show (translateNonpreemptivePriorityWorkState offset state).active = none by
                simp [translateNonpreemptivePriorityWorkState, hactive]]
              rw [dif_pos hwaitingTranslated]
              simp only
              rw [hheadTranslated]
            rw [hstartTranslated]
            simp [startNextNonpreemptivePriorityJob,
              translateNonpreemptivePriorityWorkState, hactive, hwaiting, hhead]
        | cons job tail =>
            have hheadTranslated :
                (translateNonpreemptivePriorityWorkState offset state).waiting
                    (nextPriorityWaitingClass
                      (translateNonpreemptivePriorityWorkState offset state)
                      hwaitingTranslated) =
                  translateNonpreemptivePriorityJob offset job ::
                    tail.map (translateNonpreemptivePriorityJob offset) := by
              rw [hselected]
              simp [translateNonpreemptivePriorityWorkState, hhead]
            have hstartTranslated :
                startNextNonpreemptivePriorityJob
                    (translateNonpreemptivePriorityWorkState offset state) =
                  { (translateNonpreemptivePriorityWorkState offset state) with
                    active := some (translateNonpreemptivePriorityJob offset job,
                      job.serviceWork)
                    waiting := Function.update
                      (translateNonpreemptivePriorityWorkState offset state).waiting
                      (nextPriorityWaitingClass
                        (translateNonpreemptivePriorityWorkState offset state)
                        hwaitingTranslated)
                      (tail.map (translateNonpreemptivePriorityJob offset)) } := by
              unfold startNextNonpreemptivePriorityJob
              rw [show (translateNonpreemptivePriorityWorkState offset state).active = none by
                simp [translateNonpreemptivePriorityWorkState, hactive]]
              rw [dif_pos hwaitingTranslated]
              simp only
              rw [hheadTranslated]
              rfl
            rw [hselected] at hstartTranslated
            rw [hstartTranslated]
            simp [startNextNonpreemptivePriorityJob,
              translateNonpreemptivePriorityWorkState, hactive, hwaiting, hhead]
            funext i
            by_cases hi : i = nextPriorityWaitingClass state hwaiting <;>
              simp [Function.update, hi]
      · have hwaitingTranslated : ¬ hasPriorityWaitingJob
            (translateNonpreemptivePriorityWorkState offset state) :=
            (hasPriorityWaitingJob_translate_iff offset state).not.mpr hwaiting
        have hstartTranslated :
            startNextNonpreemptivePriorityJob
                (translateNonpreemptivePriorityWorkState offset state) =
              translateNonpreemptivePriorityWorkState offset state := by
          unfold startNextNonpreemptivePriorityJob
          rw [show (translateNonpreemptivePriorityWorkState offset state).active = none by
            simp [translateNonpreemptivePriorityWorkState, hactive]]
          rw [dif_neg hwaitingTranslated]
        rw [hstartTranslated]
        simp [startNextNonpreemptivePriorityJob,
          translateNonpreemptivePriorityWorkState, hactive, hwaiting]

/-- Admission of a shifted arrival commutes with a change of time origin. -/
theorem translateNonpreemptivePriorityWorkState_admit
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (admitNonpreemptivePriorityJob state job) =
      admitNonpreemptivePriorityJob
        (translateNonpreemptivePriorityWorkState offset state)
        (translateNonpreemptivePriorityJob offset job) := by
  classical
  unfold admitNonpreemptivePriorityJob
  rw [show startNextNonpreemptivePriorityJob
      (translateNonpreemptivePriorityWorkState offset state) =
        translateNonpreemptivePriorityWorkState offset
          (startNextNonpreemptivePriorityJob state) by
    symm
    exact translateNonpreemptivePriorityWorkState_startNext offset state]
  dsimp
  cases hprepared : (startNextNonpreemptivePriorityJob state).active with
  | none =>
      simp [hprepared, translateNonpreemptivePriorityWorkState]
  | some active =>
      have hpreparedTranslated :
          (translateNonpreemptivePriorityWorkState offset
            (startNextNonpreemptivePriorityJob state)).active =
            some (translateNonpreemptivePriorityJob offset active.1, active.2) := by
        simp [translateNonpreemptivePriorityWorkState, hprepared]
      simp [hpreparedTranslated]
      exact
        (translateNonpreemptivePriorityWorkState_enqueue offset
          (startNextNonpreemptivePriorityJob state) job)

/-- Completing service and starting the next job commutes with a change of
time origin, including the recorded completion time. -/
theorem translateNonpreemptivePriorityWorkState_complete
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (completeNonpreemptivePriorityWorkJob state) =
      completeNonpreemptivePriorityWorkJob
        (translateNonpreemptivePriorityWorkState offset state) := by
  classical
  unfold completeNonpreemptivePriorityWorkJob
  cases hactive : state.active with
  | none =>
      simp [hactive, translateNonpreemptivePriorityWorkState]
  | some active =>
      let pre : NonpreemptivePriorityWorkState n JobId :=
        { currentTime := state.currentTime
          active := none
          waiting := state.waiting
          completed := (active.1, state.currentTime) :: state.completed }
      have hpre : translateNonpreemptivePriorityWorkState offset pre =
          { currentTime := (translateNonpreemptivePriorityWorkState offset state).currentTime
            active := none
            waiting := (translateNonpreemptivePriorityWorkState offset state).waiting
            completed := (translateNonpreemptivePriorityJob offset active.1,
              (translateNonpreemptivePriorityWorkState offset state).currentTime) ::
                (translateNonpreemptivePriorityWorkState offset state).completed } := by
        simp [pre, translateNonpreemptivePriorityWorkState]
      have hactiveTranslated :
          (translateNonpreemptivePriorityWorkState offset state).active =
            some (translateNonpreemptivePriorityJob offset active.1, active.2) := by
        simp [translateNonpreemptivePriorityWorkState, hactive]
      rw [hactiveTranslated]
      simp only
      rw [← hpre, ← translateNonpreemptivePriorityWorkState_startNext offset pre]

/-- Bounded deterministic service evolution commutes with a change of time
origin. -/
theorem translateNonpreemptivePriorityWorkState_advance
    {n : ℕ} {JobId : Type*} (offset : ℝ) (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (advanceNonpreemptivePriorityWorkState fuel target state) =
      advanceNonpreemptivePriorityWorkState fuel (target - offset)
        (translateNonpreemptivePriorityWorkState offset state) := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have htranslated : target - offset ≤
            (translateNonpreemptivePriorityWorkState offset state).currentTime := by
          simp [translateNonpreemptivePriorityWorkState]
          linarith
        simp [advanceNonpreemptivePriorityWorkState, htarget, htranslated]
      · have htranslated : ¬ target - offset ≤
            (translateNonpreemptivePriorityWorkState offset state).currentTime := by
          simp [translateNonpreemptivePriorityWorkState]
          linarith
        cases hactive : state.active with
        | none =>
            simp [advanceNonpreemptivePriorityWorkState,
              translateNonpreemptivePriorityWorkState,
              htarget, hactive]
        | some active =>
            simp [advanceNonpreemptivePriorityWorkState,
              translateNonpreemptivePriorityWorkState,
              htarget, hactive]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have htranslated : target - offset ≤
            (translateNonpreemptivePriorityWorkState offset state).currentTime := by
          simp [translateNonpreemptivePriorityWorkState]
          linarith
        simp [advanceNonpreemptivePriorityWorkState, htarget, htranslated]
      · have htranslated : ¬ target - offset ≤
            (translateNonpreemptivePriorityWorkState offset state).currentTime := by
          simp [translateNonpreemptivePriorityWorkState]
          linarith
        cases hactive : state.active with
        | none =>
            simp [advanceNonpreemptivePriorityWorkState,
              translateNonpreemptivePriorityWorkState,
              htarget, hactive]
        | some active =>
            have hactiveTranslated :
                (translateNonpreemptivePriorityWorkState offset state).active =
                  some (translateNonpreemptivePriorityJob offset active.1, active.2) := by
              simp [translateNonpreemptivePriorityWorkState, hactive]
            have hgap : target - state.currentTime =
                (target - offset) -
                  (translateNonpreemptivePriorityWorkState offset state).currentTime := by
              simp [translateNonpreemptivePriorityWorkState]
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · have hcompleteTranslated : active.2 ≤ (target - offset) -
                  (translateNonpreemptivePriorityWorkState offset state).currentTime := by
                rw [← hgap]
                exact hcomplete
              let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { currentTime := state.currentTime + active.2
                  active := some active
                  waiting := state.waiting
                  completed := state.completed }
              have hcompletedAtTranslate :
                  translateNonpreemptivePriorityWorkState offset completedAt =
                    { currentTime := (translateNonpreemptivePriorityWorkState offset state).currentTime +
                        active.2
                      active := some
                        (translateNonpreemptivePriorityJob offset active.1, active.2)
                      waiting := (translateNonpreemptivePriorityWorkState offset state).waiting
                      completed := (translateNonpreemptivePriorityWorkState offset state).completed } := by
                simp [completedAt, translateNonpreemptivePriorityWorkState]
                ring
              simp [advanceNonpreemptivePriorityWorkState, htarget,
                htranslated, hactive, hactiveTranslated, hcomplete, hcompleteTranslated]
              rw [← hcompletedAtTranslate,
                ← translateNonpreemptivePriorityWorkState_complete offset completedAt]
              exact ih (completeNonpreemptivePriorityWorkJob completedAt)
            · have hcompleteTranslated : ¬ active.2 ≤ (target - offset) -
                  (translateNonpreemptivePriorityWorkState offset state).currentTime := by
                rw [← hgap]
                exact hcomplete
              simp [advanceNonpreemptivePriorityWorkState,
                translateNonpreemptivePriorityWorkState,
                htarget, hactive, hcomplete]

/-- Advancing to a shifted arrival and admitting it commutes with a change of
time origin. -/
theorem translateNonpreemptivePriorityWorkState_advanceThenAdmit
    {n : ℕ} {JobId : Type*} (offset : ℝ) (fuel : ℕ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) :
    translateNonpreemptivePriorityWorkState offset
        (advanceThenAdmitNonpreemptivePriorityJob fuel state job) =
      advanceThenAdmitNonpreemptivePriorityJob fuel
        (translateNonpreemptivePriorityWorkState offset state)
        (translateNonpreemptivePriorityJob offset job) := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [translateNonpreemptivePriorityWorkState_admit,
    translateNonpreemptivePriorityWorkState_advance]
  rfl

/-- Executing a finite translated arrival list gives precisely the translated
final queue state. -/
theorem translateNonpreemptivePriorityWorkState_run
    {n : ℕ} {JobId : Type*} (offset : ℝ)
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    translateNonpreemptivePriorityWorkState offset
        (runNonpreemptivePriorityArrivalTrace initial jobs) =
      runNonpreemptivePriorityArrivalTrace
        (translateNonpreemptivePriorityWorkState offset initial)
        (jobs.map (translateNonpreemptivePriorityJob offset)) := by
  induction jobs generalizing initial with
  | nil =>
      rfl
  | cons job jobs ih =>
      change translateNonpreemptivePriorityWorkState offset
          (runNonpreemptivePriorityArrivalTrace
            (advanceThenAdmitNonpreemptivePriorityJob
              (totalNonpreemptivePriorityWorkJobs initial) initial job) jobs) =
        runNonpreemptivePriorityArrivalTrace
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs
              (translateNonpreemptivePriorityWorkState offset initial))
            (translateNonpreemptivePriorityWorkState offset initial)
            (translateNonpreemptivePriorityJob offset job))
          (jobs.map (translateNonpreemptivePriorityJob offset))
      rw [ih]
      rw [translateNonpreemptivePriorityWorkState_advanceThenAdmit,
        totalNonpreemptivePriorityWorkJobs_translate]

end

end Queueing
end AppliedModelingLib
