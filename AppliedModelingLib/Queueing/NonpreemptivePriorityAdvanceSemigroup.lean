import AppliedModelingLib.Queueing.NonpreemptivePriorityServiceAccounting

/-!
# Semigroup laws for finite nonpreemptive-priority service evolution

With sufficient completion fuel, advancing a finite priority state never
creates live jobs and is insensitive to unused fuel.  These elementary facts
support deterministic cuts of an arrival trace at a physical time.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Advancing a finite priority state can only remove resident jobs; it never
creates a new active or waiting record. -/
theorem totalNonpreemptivePriorityWorkJobs_advance_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityWorkJobs
      (advanceNonpreemptivePriorityWorkState fuel target state) ≤
      totalNonpreemptivePriorityWorkJobs state := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none => simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
          totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
        | some active => simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
          totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none => simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
          totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hnextCount : totalNonpreemptivePriorityWorkJobs
                  (completeNonpreemptivePriorityWorkJob completedState) + 1 =
                  totalNonpreemptivePriorityWorkJobs state := by
                have hcompleteCount := totalNonpreemptivePriorityWorkJobs_complete_of_active
                  completedState active (by simp [completedState, hactive])
                simpa [completedState] using hcompleteCount
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState)
              rw [show advanceNonpreemptivePriorityWorkState (fuel + 1) target state =
                  advanceNonpreemptivePriorityWorkState fuel target
                    (completeNonpreemptivePriorityWorkJob completedState) by
                    simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                      hcomplete, completedState]]
              exact hind.trans (by omega)
            · simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete,
                totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]

/-- Once the completion fuel already covers every live job, one additional
unit of fuel leaves a finite service evolution unchanged. -/
theorem advanceNonpreemptivePriorityWorkState_fuel_succ_eq_of_total_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    advanceNonpreemptivePriorityWorkState (fuel + 1) target state =
      advanceNonpreemptivePriorityWorkState fuel target state := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, _⟩
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simp [advanceNonpreemptivePriorityWorkState, htarget]
      · cases hactive : state.active with
        | none => simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hnextCount : totalNonpreemptivePriorityWorkJobs
                  (completeNonpreemptivePriorityWorkJob completedState) ≤ fuel := by
                have hcompleteCount := totalNonpreemptivePriorityWorkJobs_complete_of_active
                  completedState active (by simp [completedState, hactive])
                have htimeCount : totalNonpreemptivePriorityWorkJobs completedState =
                    totalNonpreemptivePriorityWorkJobs state := by
                  rfl
                omega
              have hind := ih (completeNonpreemptivePriorityWorkJob completedState) hnextCount
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedState] using hind
            · simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]

/-- Once the recursion fuel covers every resident job, additional fuel does
not change a finite service evolution.  This permits cutpoint arguments to
compare replays whose intermediate resident populations have different
sizes. -/
theorem advanceNonpreemptivePriorityWorkState_eq_of_total_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    advanceNonpreemptivePriorityWorkState fuel target state =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) target state := by
  induction fuel with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      simp [hcount]
  | succ fuel ih =>
      by_cases hcount : totalNonpreemptivePriorityWorkJobs state = fuel + 1
      · simp [hcount]
      · have hle : totalNonpreemptivePriorityWorkJobs state ≤ fuel := by
          omega
        rw [advanceNonpreemptivePriorityWorkState_fuel_succ_eq_of_total_le
          fuel target state hle]
        exact ih hle

/-- With enough fuel for the currently resident jobs, finite service
evolution may be split at any intermediate physical time.  The completion
ledger as well as the live queue agree with direct evolution to the terminal
time. -/
theorem advanceNonpreemptivePriorityWorkState_split_of_total_le
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (cutoff terminal : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ cutoff)
    (hcutoff : cutoff ≤ terminal)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    advanceNonpreemptivePriorityWorkState fuel terminal state =
      advanceNonpreemptivePriorityWorkState fuel terminal
        (advanceNonpreemptivePriorityWorkState fuel cutoff state) := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, _⟩
      by_cases hcutoffState : cutoff ≤ state.currentTime
      · have hcutoffEq : cutoff = state.currentTime := le_antisymm hcutoffState hcurrent
        simp [advanceNonpreemptivePriorityWorkState, hcutoffEq]
      · have hstateCutoff : state.currentTime < cutoff := lt_of_not_ge hcutoffState
        have hterminalState : ¬ terminal ≤ state.currentTime := by
          exact not_le_of_gt (lt_of_lt_of_le hstateCutoff hcutoff)
        by_cases hterminalCutoff : terminal ≤ cutoff
        · have hterminalEq : terminal = cutoff := le_antisymm hterminalCutoff hcutoff
          simp [advanceNonpreemptivePriorityWorkState, hterminalEq, hcutoffState, hactive]
        · simp [advanceNonpreemptivePriorityWorkState, hcutoffState,
            hterminalState, hterminalCutoff, hactive]
  | succ fuel ih =>
      classical
      by_cases hcutoffState : cutoff ≤ state.currentTime
      · have hcutoffEq : cutoff = state.currentTime := le_antisymm hcutoffState hcurrent
        simp [advanceNonpreemptivePriorityWorkState, hcutoffEq]
      · have hstateCutoff : state.currentTime < cutoff := lt_of_not_ge hcutoffState
        have hterminalState : ¬ terminal ≤ state.currentTime := by
          exact not_le_of_gt (lt_of_lt_of_le hstateCutoff hcutoff)
        cases hactive : state.active with
        | none =>
            by_cases hterminalCutoff : terminal ≤ cutoff
            · have hterminalEq : terminal = cutoff := le_antisymm hterminalCutoff hcutoff
              simp [advanceNonpreemptivePriorityWorkState, hcutoffState, hactive, hterminalEq]
            · simp [advanceNonpreemptivePriorityWorkState, hcutoffState,
                hterminalState, hactive, hterminalCutoff]
        | some active =>
            by_cases hcompleteCutoff : active.2 ≤ cutoff - state.currentTime
            · let completedState : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              let nextState := completeNonpreemptivePriorityWorkJob completedState
              have hnextFuel : totalNonpreemptivePriorityWorkJobs nextState ≤ fuel := by
                have hcompleteCount := totalNonpreemptivePriorityWorkJobs_complete_of_active
                  completedState active (by simp [completedState, hactive])
                have htimeCount : totalNonpreemptivePriorityWorkJobs completedState =
                    totalNonpreemptivePriorityWorkJobs state := by
                  rfl
                dsimp [nextState]
                omega
              have hnextCurrent : nextState.currentTime ≤ cutoff := by
                change (completeNonpreemptivePriorityWorkJob completedState).currentTime ≤ cutoff
                rw [completeNonpreemptivePriorityWorkJob_currentTime]
                dsimp [completedState]
                linarith
              have hcompleteTerminal : active.2 ≤ terminal - state.currentTime := by
                linarith
              have hsplit := ih nextState hnextCurrent hnextFuel
              have hafterFuel : totalNonpreemptivePriorityWorkJobs
                  (advanceNonpreemptivePriorityWorkState fuel cutoff nextState) ≤ fuel :=
                (totalNonpreemptivePriorityWorkJobs_advance_le fuel cutoff nextState).trans hnextFuel
              calc
                advanceNonpreemptivePriorityWorkState (fuel + 1) terminal state =
                    advanceNonpreemptivePriorityWorkState fuel terminal nextState := by
                      simp [advanceNonpreemptivePriorityWorkState, hterminalState, hactive,
                        hcompleteTerminal, completedState, nextState]
                _ = advanceNonpreemptivePriorityWorkState fuel terminal
                    (advanceNonpreemptivePriorityWorkState fuel cutoff nextState) := hsplit
                _ = advanceNonpreemptivePriorityWorkState (fuel + 1) terminal
                    (advanceNonpreemptivePriorityWorkState fuel cutoff nextState) := by
                      symm
                      exact advanceNonpreemptivePriorityWorkState_fuel_succ_eq_of_total_le
                        fuel terminal
                        (advanceNonpreemptivePriorityWorkState fuel cutoff nextState) hafterFuel
                _ = advanceNonpreemptivePriorityWorkState (fuel + 1) terminal
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) cutoff state) := by
                      simp [advanceNonpreemptivePriorityWorkState, hcutoffState, hactive,
                        hcompleteCutoff, completedState, nextState]
            · let cutoffState : NonpreemptivePriorityWorkState n JobId :=
                { state with
                  currentTime := cutoff,
                  active := some (active.1,
                    active.2 - (cutoff - state.currentTime)) }
              by_cases hcompleteTerminal : active.2 ≤ terminal - state.currentTime
              · let completedState : NonpreemptivePriorityWorkState n JobId :=
                  { state with currentTime := state.currentTime + active.2 }
                let nextState := completeNonpreemptivePriorityWorkJob completedState
                have hcutoffActive : cutoffState.active =
                    some (active.1, active.2 - (cutoff - state.currentTime)) := rfl
                have hcompleteFromCutoff : active.2 - (cutoff - state.currentTime) ≤
                    terminal - cutoff := by
                  linarith
                have hterminalCutoff : ¬ terminal ≤ cutoff := by
                  apply not_le_of_gt
                  linarith
                have hcompletedEq :
                    completeNonpreemptivePriorityWorkJob
                      { cutoffState with currentTime :=
                        cutoffState.currentTime +
                          (active.2 - (cutoff - state.currentTime)) } = nextState := by
                  have htime : cutoff + (active.2 - (cutoff - state.currentTime)) =
                      state.currentTime + active.2 := by ring
                  simp [cutoffState, completedState, nextState,
                    completeNonpreemptivePriorityWorkJob, htime, hactive]
                simp [advanceNonpreemptivePriorityWorkState, hterminalState, hactive,
                  hcompleteTerminal, hcutoffState, hcompleteCutoff, cutoffState,
                  hcutoffActive, hcompleteFromCutoff, completedState, nextState,
                  hcompletedEq, hterminalCutoff]
              · have hpartialFromCutoff : ¬
                    (active.2 - (cutoff - state.currentTime) ≤ terminal - cutoff) := by
                  intro h
                  exact hcompleteTerminal (by linarith)
                by_cases hterminalCutoff : terminal ≤ cutoff
                · have hterminalEq : terminal = cutoff := le_antisymm hterminalCutoff hcutoff
                  simp [advanceNonpreemptivePriorityWorkState, hactive,
                    hcutoffState, hcompleteCutoff, hterminalEq]
                · simp [advanceNonpreemptivePriorityWorkState, hterminalState, hactive,
                    hcompleteTerminal, hcutoffState, hcompleteCutoff,
                    hpartialFromCutoff, hterminalCutoff]
                  ring

/-- A finite arrival replay may be cut at a time no later than every input
arrival: advancing at the cut before replaying the suffix gives the same
terminal queue state.  The empty-suffix case is the service-evolution
semigroup law; otherwise the first arrival absorbs the cut. -/
theorem advance_runNonpreemptivePriorityArrivalTrace_cut
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (cutoff terminal : ℝ)
    (hcurrent : initial.currentTime ≤ cutoff)
    (hcutoff : cutoff ≤ terminal)
    (hjobs : ∀ job ∈ jobs, cutoff ≤ job.arrivalTime) :
    advanceNonpreemptivePriorityWorkState
      (totalNonpreemptivePriorityWorkJobs
        (runNonpreemptivePriorityArrivalTrace initial jobs)) terminal
      (runNonpreemptivePriorityArrivalTrace initial jobs) =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace
            (advanceNonpreemptivePriorityWorkState
              (totalNonpreemptivePriorityWorkJobs initial) cutoff initial) jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) cutoff initial) jobs) := by
  cases jobs with
  | nil =>
      simp only [runNonpreemptivePriorityArrivalTrace, List.foldl_nil]
      let fuel := totalNonpreemptivePriorityWorkJobs initial
      let cutState := advanceNonpreemptivePriorityWorkState fuel cutoff initial
      have hcutCount : totalNonpreemptivePriorityWorkJobs cutState ≤ fuel := by
        exact totalNonpreemptivePriorityWorkJobs_advance_le fuel cutoff initial
      change advanceNonpreemptivePriorityWorkState fuel terminal initial =
        advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs cutState) terminal cutState
      rw [← advanceNonpreemptivePriorityWorkState_eq_of_total_le
        fuel terminal cutState hcutCount]
      exact advanceNonpreemptivePriorityWorkState_split_of_total_le
        fuel cutoff terminal initial hcurrent hcutoff le_rfl
  | cons job tail =>
      let fuel := totalNonpreemptivePriorityWorkJobs initial
      let cutState := advanceNonpreemptivePriorityWorkState fuel cutoff initial
      have hcutCount : totalNonpreemptivePriorityWorkJobs cutState ≤ fuel := by
        exact totalNonpreemptivePriorityWorkJobs_advance_le fuel cutoff initial
      have hjob : cutoff ≤ job.arrivalTime := hjobs job (by simp)
      have hevolve : advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial =
          advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs cutState) job.arrivalTime cutState := by
        calc
          advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial =
              advanceNonpreemptivePriorityWorkState fuel job.arrivalTime cutState := by
                exact advanceNonpreemptivePriorityWorkState_split_of_total_le
                  fuel cutoff job.arrivalTime initial hcurrent hjob le_rfl
          _ = advanceNonpreemptivePriorityWorkState
              (totalNonpreemptivePriorityWorkJobs cutState) job.arrivalTime cutState := by
                exact advanceNonpreemptivePriorityWorkState_eq_of_total_le
                  fuel job.arrivalTime cutState hcutCount
      have hstep : advanceThenAdmitNonpreemptivePriorityJob fuel initial job =
          advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs cutState) cutState job := by
        exact congrArg (fun state => admitNonpreemptivePriorityJob state job) hevolve
      simp only [runNonpreemptivePriorityArrivalTrace, List.foldl_cons]
      rw [show totalNonpreemptivePriorityWorkJobs initial = fuel by rfl,
        show advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) cutoff initial = cutState by rfl,
        hstep]

end

end AppliedModelingLib.Queueing
