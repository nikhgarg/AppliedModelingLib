import AppliedModelingLib.Queueing.NonpreemptivePriorityPopulation
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkConservation
import AppliedModelingLib.Queueing.NonpreemptivePriorityWorkload
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Service accounting for finite nonpreemptive-priority queues

For a work-conserving finite state with positive residual work, service reduces
total residual work exactly at rate one until the state empties.  The result is
independent of the priority order and is the deterministic accounting bridge
for stationary workload constructions.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-- The residual service work over a nonnegative uninterrupted service interval
has triangular area equal to half the squared service requirement.  This is
the deterministic per-customer contribution used by stationary residual-work
occupation arguments. -/
theorem integral_residualServiceWork_over_serviceInterval
    (start serviceWork : ℝ) (hserviceWork : 0 ≤ serviceWork) :
    ∫ t in start..(start + serviceWork), (start + serviceWork - t) =
      serviceWork ^ 2 / 2 := by
  have htranslate :
      (∫ t in start..(start + serviceWork), serviceWork - (t - start)) =
        ∫ t in (0 : ℝ)..serviceWork, serviceWork - t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_comp_sub_right
        (fun t : ℝ => serviceWork - t) start (a := start) (b := start + serviceWork))
  calc
    ∫ t in start..(start + serviceWork), (start + serviceWork - t) =
        ∫ t in start..(start + serviceWork), serviceWork - (t - start) := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
    _ = ∫ t in (0 : ℝ)..serviceWork, serviceWork - t := htranslate
    _ = serviceWork ^ 2 / 2 := by
          have hconstant : IntervalIntegrable (fun _ : ℝ => serviceWork)
              MeasureTheory.volume 0 serviceWork :=
            continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
          have hidIntegral : IntervalIntegrable (fun t : ℝ => t)
              MeasureTheory.volume 0 serviceWork :=
            continuous_id.intervalIntegrable (μ := MeasureTheory.volume) _ _
          rw [intervalIntegral.integral_sub hconstant hidIntegral]
          rw [intervalIntegral.integral_const]
          have hid : (∫ t in (0 : ℝ)..serviceWork, t) = serviceWork ^ 2 / 2 := by
            simpa using (intervalIntegral.integral_pow (a := (0 : ℝ)) (b := serviceWork) 1)
          simp only [smul_eq_mul, sub_zero]
          rw [hid]
          ring

/-- The residual area accumulated during an initial elapsed part of a service
interval.  The whole-service triangle is the special case `elapsed =
serviceWork`; this form is the one used by the partial branch of a finite
service evolution. -/
theorem integral_residualServiceWork_over_elapsedInterval
    (start elapsed serviceWork : ℝ) (helapsed : 0 ≤ elapsed) :
    ∫ t in start..(start + elapsed), serviceWork - (t - start) =
      serviceWork * elapsed - elapsed ^ 2 / 2 := by
  have htranslate :
      (∫ t in start..(start + elapsed), serviceWork - (t - start)) =
        ∫ t in (0 : ℝ)..elapsed, serviceWork - t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (intervalIntegral.integral_comp_sub_right
        (fun t : ℝ => serviceWork - t) start (a := start) (b := start + elapsed))
  rw [htranslate]
  have hconstant : IntervalIntegrable (fun _ : ℝ => serviceWork)
      MeasureTheory.volume 0 elapsed :=
    continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
  have hidIntegral : IntervalIntegrable (fun t : ℝ => t)
      MeasureTheory.volume 0 elapsed :=
    continuous_id.intervalIntegrable (μ := MeasureTheory.volume) _ _
  rw [intervalIntegral.integral_sub hconstant hidIntegral]
  rw [intervalIntegral.integral_const]
  have hid : (∫ t in (0 : ℝ)..elapsed, t) = elapsed ^ 2 / 2 := by
    simpa using (intervalIntegral.integral_pow (a := (0 : ℝ)) (b := elapsed) 1)
  simp only [smul_eq_mul, sub_zero]
  rw [hid]
  ring

/-- During the initial service interval of an active positive-work job, the
finite service recursion has exactly the residual-service triangle as its
active-work trajectory.  The completion endpoint is immaterial to the
interval integral because it is a volume-null singleton. -/
theorem integral_activeNonpreemptivePriorityResidualWork_advance_initialService
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active) (hresidual : 0 < active.2) :
    ∫ t in state.currentTime..(state.currentTime + active.2),
      activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState (fuel + 1) t state) =
      active.2 ^ 2 / 2 := by
  calc
    ∫ t in state.currentTime..(state.currentTime + active.2),
        activeNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState (fuel + 1) t state) =
        ∫ t in state.currentTime..(state.currentTime + active.2),
          active.2 - (t - state.currentTime) := by
            apply intervalIntegral.integral_congr_ae
            have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
                t ≠ state.currentTime + active.2 := by
              simp [MeasureTheory.ae_iff]
            filter_upwards [hne] with t hne ht
            have htime : state.currentTime ≤ state.currentTime + active.2 := by linarith
            rw [Set.uIoc_of_le htime] at ht
            have hlt : t < state.currentTime + active.2 :=
              lt_of_le_of_ne ht.2 hne
            have htarget : ¬ t ≤ state.currentTime := not_le_of_gt ht.1
            have hcomplete : ¬ active.2 ≤ t - state.currentTime := by linarith
            exact activeNonpreemptivePriorityResidualWork_advance_partial
              fuel t state active htarget hactive hcomplete
    _ = ∫ t in state.currentTime..(state.currentTime + active.2),
        state.currentTime + active.2 - t := by
          apply intervalIntegral.integral_congr
          intro t _
          ring
    _ = active.2 ^ 2 / 2 :=
      integral_residualServiceWork_over_serviceInterval state.currentTime active.2 hresidual.le

/-- A time-only state update leaves total resident work unchanged. -/
theorem totalNonpreemptivePriorityResidualWork_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (time : ℝ) :
    totalNonpreemptivePriorityResidualWork { state with currentTime := time } =
      totalNonpreemptivePriorityResidualWork state := by
  rfl

/-- For a finite positive work-conserving priority state with enough completion
fuel, the active-residual trajectory is interval-integrable until the state
drains, and its exact area is half the squared-residual ledger.  The proof
splits at the first concrete service completion and recurses on the resulting
state. -/
theorem intervalIntegrable_and_integral_activeNonpreemptivePriorityResidualWork_advance_to_drain
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    IntervalIntegrable
      (fun t => activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState fuel t state))
      MeasureTheory.volume state.currentTime
      (state.currentTime + totalNonpreemptivePriorityResidualWork state) ∧
    (∫ t in state.currentTime..(state.currentTime + totalNonpreemptivePriorityResidualWork state),
      activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState fuel t state)) =
      totalNonpreemptivePrioritySquaredResidualWork state / 2 := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, hwaiting⟩
      have hzero : ∀ t : ℝ,
          activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState 0 t state) = 0 := by
        intro t
        by_cases htarget : t ≤ state.currentTime
        · simp [advanceNonpreemptivePriorityWorkState, htarget,
            activeNonpreemptivePriorityResidualWork, hactive]
        · simp [advanceNonpreemptivePriorityWorkState, htarget,
            activeNonpreemptivePriorityResidualWork, hactive]
      have hzeroFun :
          (fun t : ℝ => activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState 0 t state)) = fun _ => 0 := by
        funext t
        exact hzero t
      constructor
      · rw [hzeroFun]
        exact continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
      · rw [hzeroFun]
        simp [totalNonpreemptivePrioritySquaredResidualWork,
          activeNonpreemptivePriorityResidualWork, hactive, hwaiting]
  | succ fuel ih =>
      classical
      cases hactive : state.active with
      | none =>
          have hwaiting : ∀ i, state.waiting i = [] := by
            intro i
            cases hlist : state.waiting i with
            | nil => simp
            | cons head tail =>
                exact False.elim (hwork hactive ⟨i, by simp [hlist]⟩)
          have hzero : ∀ t : ℝ,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state) = 0 := by
            intro t
            by_cases htarget : t ≤ state.currentTime
            · simp [advanceNonpreemptivePriorityWorkState, htarget,
                activeNonpreemptivePriorityResidualWork, hactive]
            · simp [advanceNonpreemptivePriorityWorkState, htarget,
                activeNonpreemptivePriorityResidualWork, hactive]
          have hzeroFun :
              (fun t : ℝ => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) = fun _ => 0 := by
            funext t
            exact hzero t
          constructor
          · rw [hzeroFun]
            exact continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
          · rw [hzeroFun]
            simp [totalNonpreemptivePrioritySquaredResidualWork,
              activeNonpreemptivePriorityResidualWork, hactive, hwaiting]
      | some active =>
          have hresidual : 0 < active.2 := hpositive.1 active hactive
          let completedAt : NonpreemptivePriorityWorkState n JobId :=
            { state with currentTime := state.currentTime + active.2 }
          let next : NonpreemptivePriorityWorkState n JobId :=
            completeNonpreemptivePriorityWorkJob completedAt
          have hcompletedAtPositive :
              positiveNonpreemptivePriorityResidualWork completedAt := by
            simpa [completedAt] using hpositive
          have hcompletedAtWork : nonpreemptivePriorityWorkConserving completedAt := by
            intro hnone
            exact (Option.some_ne_none active
              (by simpa [completedAt, hactive] using hnone)).elim
          have hnextPositive : positiveNonpreemptivePriorityResidualWork next := by
            dsimp [next]
            exact positiveNonpreemptivePriorityResidualWork_complete
              completedAt hcompletedAtPositive
          have hnextWork : nonpreemptivePriorityWorkConserving next := by
            dsimp [next]
            exact nonpreemptivePriorityWorkConserving_complete completedAt hcompletedAtWork
          have hnextCount : totalNonpreemptivePriorityWorkJobs next ≤ fuel := by
            have hcompletionCount :
                totalNonpreemptivePriorityWorkJobs
                    (completeNonpreemptivePriorityWorkJob completedAt) + 1 =
                  totalNonpreemptivePriorityWorkJobs completedAt := by
              apply totalNonpreemptivePriorityWorkJobs_complete_of_active completedAt active
              simp [completedAt, hactive]
            have htimeCount : totalNonpreemptivePriorityWorkJobs completedAt =
                totalNonpreemptivePriorityWorkJobs state := by
              rfl
            dsimp [next]
            omega
          have htail := ih next hnextPositive hnextWork hnextCount
          have hwaitingNonneg :
              0 ≤ ∑ i, priorityWaitingResidualWork state i := by
            apply Finset.sum_nonneg
            intro i _
            exact priorityWaitingResidualWork_nonneg state hpositive.nonnegative i
          have htotal : totalNonpreemptivePriorityResidualWork state =
              active.2 + ∑ i, priorityWaitingResidualWork state i := by
            unfold totalNonpreemptivePriorityResidualWork
              activeNonpreemptivePriorityResidualWork
            simp [hactive]
          have hcompletion_le_terminal : state.currentTime + active.2 ≤
              state.currentTime + totalNonpreemptivePriorityResidualWork state := by
            rw [htotal]
            linarith
          have hnextTime : next.currentTime = state.currentTime + active.2 := by
            dsimp [next]
            rw [completeNonpreemptivePriorityWorkJob_currentTime]
          have hnextResidual : totalNonpreemptivePriorityResidualWork next =
              totalNonpreemptivePriorityResidualWork state - active.2 := by
            calc
              totalNonpreemptivePriorityResidualWork next =
                  totalNonpreemptivePriorityResidualWork completedAt - active.2 := by
                    dsimp [next]
                    apply totalNonpreemptivePriorityResidualWork_complete completedAt active
                    simp [completedAt, hactive]
              _ = totalNonpreemptivePriorityResidualWork state - active.2 := by
                    rw [totalNonpreemptivePriorityResidualWork_timeUpdate]
          have hterminal : next.currentTime +
              totalNonpreemptivePriorityResidualWork next =
              state.currentTime + totalNonpreemptivePriorityResidualWork state := by
            rw [hnextTime, hnextResidual]
            ring
          have hnextSquared : totalNonpreemptivePrioritySquaredResidualWork next =
              totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
            calc
              totalNonpreemptivePrioritySquaredResidualWork next =
                  totalNonpreemptivePrioritySquaredResidualWork completedAt - active.2 ^ 2 := by
                    dsimp [next]
                    apply totalNonpreemptivePrioritySquaredResidualWork_complete completedAt active
                    simp [completedAt, hactive]
              _ = totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
                    rw [totalNonpreemptivePrioritySquaredResidualWork_timeUpdate]
          have hfirstLinear : IntervalIntegrable
              (fun t : ℝ => active.2 - (t - state.currentTime))
              MeasureTheory.volume state.currentTime (state.currentTime + active.2) := by
            exact (continuous_const.sub (continuous_id.sub continuous_const)).intervalIntegrable
              (μ := MeasureTheory.volume) _ _
          have hfirst : IntervalIntegrable
              (fun t => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
              MeasureTheory.volume state.currentTime (state.currentTime + active.2) := by
            apply hfirstLinear.congr_ae
            have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
                t ≠ state.currentTime + active.2 := by
              simp [MeasureTheory.ae_iff]
            filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
              MeasureTheory.ae_restrict_of_ae hne] with t ht hne
            rw [Set.uIoc_of_le (by linarith [hresidual])] at ht
            have htarget : ¬ t ≤ state.currentTime := not_le_of_gt ht.1
            have hcomplete : ¬ active.2 ≤ t - state.currentTime := by
              have hlt : t < state.currentTime + active.2 :=
                lt_of_le_of_ne ht.2 hne
              linarith
            rw [activeNonpreemptivePriorityResidualWork_advance_partial
              fuel t state active htarget hactive hcomplete]
          have htailEq : Set.EqOn
              (fun t => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
              (fun t => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t next))
              (Set.uIcc (state.currentTime + active.2)
                (state.currentTime + totalNonpreemptivePriorityResidualWork state)) := by
            intro t ht
            rw [Set.uIcc_of_le hcompletion_le_terminal] at ht
            have htarget : ¬ t ≤ state.currentTime := by
              linarith [ht.1, hresidual]
            have hcomplete : active.2 ≤ t - state.currentTime := by
              linarith [ht.1]
            simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete,
              completedAt, next]
          have htailIntegrableNext : IntervalIntegrable
              (fun t => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t next))
              MeasureTheory.volume (state.currentTime + active.2)
              (state.currentTime + totalNonpreemptivePriorityResidualWork state) := by
            have htailIntegrableRaw := htail.1
            rw [hterminal, hnextTime] at htailIntegrableRaw
            exact htailIntegrableRaw
          have htailIntegrable : IntervalIntegrable
              (fun t => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
              MeasureTheory.volume (state.currentTime + active.2)
              (state.currentTime + totalNonpreemptivePriorityResidualWork state) :=
            htailIntegrableNext.congr
              (htailEq.symm.mono Set.uIoc_subset_uIcc)
          have htailIntegral :
              (∫ t in (state.currentTime + active.2)..
                (state.currentTime + totalNonpreemptivePriorityResidualWork state),
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                totalNonpreemptivePrioritySquaredResidualWork next / 2 := by
            rw [intervalIntegral.integral_congr htailEq]
            have htailIntegralRaw := htail.2
            rw [hterminal, hnextTime] at htailIntegralRaw
            exact htailIntegralRaw
          constructor
          · exact hfirst.trans htailIntegrable
          · calc
              (∫ t in state.currentTime..
                  (state.currentTime + totalNonpreemptivePriorityResidualWork state),
                  activeNonpreemptivePriorityResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                  (∫ t in state.currentTime..(state.currentTime + active.2),
                    activeNonpreemptivePriorityResidualWork
                      (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) +
                    ∫ t in (state.currentTime + active.2)..
                      (state.currentTime + totalNonpreemptivePriorityResidualWork state),
                      activeNonpreemptivePriorityResidualWork
                        (advanceNonpreemptivePriorityWorkState (fuel + 1) t state) := by
                      exact (intervalIntegral.integral_add_adjacent_intervals
                        hfirst htailIntegrable).symm
              _ = active.2 ^ 2 / 2 +
                  totalNonpreemptivePrioritySquaredResidualWork next / 2 := by
                    rw [integral_activeNonpreemptivePriorityResidualWork_advance_initialService
                      fuel state active hactive hresidual, htailIntegral]
              _ = totalNonpreemptivePrioritySquaredResidualWork state / 2 := by
                    rw [hnextSquared]
                    ring

/-- Along any finite arrival-free service evolution, the squared-residual
ledger obeys an exact energy balance: its loss is twice the accumulated active
residual work.  This formulation applies at an arbitrary terminal time, so it
can be spliced between successive arrivals in a finite queue trace. -/
theorem intervalIntegrable_and_squaredResidualWork_energy_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    IntervalIntegrable
      (fun t => activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState fuel t state))
      MeasureTheory.volume state.currentTime target ∧
    totalNonpreemptivePrioritySquaredResidualWork
        (advanceNonpreemptivePriorityWorkState fuel target state) +
      2 * (∫ t in state.currentTime..target,
        activeNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState fuel t state)) =
        totalNonpreemptivePrioritySquaredResidualWork state := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, hwaiting⟩
      have hzero : ∀ t : ℝ,
          activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState 0 t state) = 0 := by
        intro t
        by_cases htarget : t ≤ state.currentTime
        · simp [advanceNonpreemptivePriorityWorkState, htarget,
            activeNonpreemptivePriorityResidualWork, hactive]
        · simp [advanceNonpreemptivePriorityWorkState, htarget,
            activeNonpreemptivePriorityResidualWork, hactive]
      have hzeroFun :
          (fun t : ℝ => activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState 0 t state)) = fun _ => 0 := by
        funext t
        exact hzero t
      have hwaitingAdvance : ∀ t : ℝ,
          (advanceNonpreemptivePriorityWorkState 0 t state).waiting = state.waiting := by
        intro t
        by_cases htarget : t ≤ state.currentTime <;>
          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
      have hwaitingSquared :
          (∑ i, ((state.waiting i).map
            (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [hwaiting i]
        simp
      have hstate : totalNonpreemptivePrioritySquaredResidualWork state = 0 := by
        have hactiveZero : activeNonpreemptivePriorityResidualWork state = 0 := by
          unfold activeNonpreemptivePriorityResidualWork
          simp [hactive]
        unfold totalNonpreemptivePrioritySquaredResidualWork
        rw [hactiveZero, hwaitingSquared]
        norm_num
      have hfinal : totalNonpreemptivePrioritySquaredResidualWork
          (advanceNonpreemptivePriorityWorkState 0 target state) = 0 := by
        unfold totalNonpreemptivePrioritySquaredResidualWork
        rw [hzero target, hwaitingAdvance target, hwaitingSquared]
        norm_num
      constructor
      · rw [hzeroFun]
        exact continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
      · rw [hzeroFun, hfinal, hstate]
        simp
  | succ fuel ih =>
      classical
      by_cases htime : target = state.currentTime
      · subst target
        constructor
        · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le le_rfl]
          simp
        · simp [advanceNonpreemptivePriorityWorkState]
      have htarget : ¬ target ≤ state.currentTime := by
        intro hle
        exact htime (le_antisymm hle hcurrent)
      cases hactive : state.active with
      | none =>
          have hwaiting : ∀ i, state.waiting i = [] := by
            intro i
            cases hlist : state.waiting i with
            | nil => simp
            | cons head tail =>
                exact False.elim (hwork hactive ⟨i, by simp [hlist]⟩)
          have hzero : ∀ t : ℝ,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state) = 0 := by
            intro t
            by_cases htime' : t ≤ state.currentTime
            · simp [advanceNonpreemptivePriorityWorkState, htime',
                activeNonpreemptivePriorityResidualWork, hactive]
            · simp [advanceNonpreemptivePriorityWorkState, htime',
                activeNonpreemptivePriorityResidualWork, hactive]
          have hzeroFun :
              (fun t : ℝ => activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) = fun _ => 0 := by
            funext t
            exact hzero t
          have hwaitingAdvance : ∀ t : ℝ,
              (advanceNonpreemptivePriorityWorkState (fuel + 1) t state).waiting =
                state.waiting := by
            intro t
            by_cases htime' : t ≤ state.currentTime <;>
              simp [advanceNonpreemptivePriorityWorkState, htime', hactive]
          have hwaitingSquared :
              (∑ i, ((state.waiting i).map
                (fun (job : NonpreemptivePriorityJob n JobId) => job.serviceWork ^ 2)).sum) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [hwaiting i]
            simp
          have hstate : totalNonpreemptivePrioritySquaredResidualWork state = 0 := by
            have hactiveZero : activeNonpreemptivePriorityResidualWork state = 0 := by
              unfold activeNonpreemptivePriorityResidualWork
              simp [hactive]
            unfold totalNonpreemptivePrioritySquaredResidualWork
            rw [hactiveZero, hwaitingSquared]
            norm_num
          have hfinal : totalNonpreemptivePrioritySquaredResidualWork
              (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) = 0 := by
            unfold totalNonpreemptivePrioritySquaredResidualWork
            rw [hzero target, hwaitingAdvance target, hwaitingSquared]
            norm_num
          constructor
          · rw [hzeroFun]
            exact continuous_const.intervalIntegrable (μ := MeasureTheory.volume) _ _
          · rw [hzeroFun, hfinal, hstate]
            simp
      | some active =>
          have hresidual : 0 < active.2 := hpositive.1 active hactive
          by_cases hcomplete : active.2 ≤ target - state.currentTime
          · let completedAt : NonpreemptivePriorityWorkState n JobId :=
              { state with currentTime := state.currentTime + active.2 }
            let next : NonpreemptivePriorityWorkState n JobId :=
              completeNonpreemptivePriorityWorkJob completedAt
            have hcompletedAtPositive :
                positiveNonpreemptivePriorityResidualWork completedAt := by
              simpa [completedAt] using hpositive
            have hcompletedAtWork : nonpreemptivePriorityWorkConserving completedAt := by
              intro hnone
              exact (Option.some_ne_none active
                (by simpa [completedAt, hactive] using hnone)).elim
            have hnextPositive : positiveNonpreemptivePriorityResidualWork next := by
              dsimp [next]
              exact positiveNonpreemptivePriorityResidualWork_complete
                completedAt hcompletedAtPositive
            have hnextWork : nonpreemptivePriorityWorkConserving next := by
              dsimp [next]
              exact nonpreemptivePriorityWorkConserving_complete completedAt hcompletedAtWork
            have hnextCount : totalNonpreemptivePriorityWorkJobs next ≤ fuel := by
              have hcompletionCount :
                  totalNonpreemptivePriorityWorkJobs
                      (completeNonpreemptivePriorityWorkJob completedAt) + 1 =
                    totalNonpreemptivePriorityWorkJobs completedAt := by
                apply totalNonpreemptivePriorityWorkJobs_complete_of_active completedAt active
                simp [completedAt, hactive]
              have htimeCount : totalNonpreemptivePriorityWorkJobs completedAt =
                  totalNonpreemptivePriorityWorkJobs state := by
                rfl
              dsimp [next]
              omega
            have hnextTime : next.currentTime = state.currentTime + active.2 := by
              dsimp [next]
              rw [completeNonpreemptivePriorityWorkJob_currentTime]
            have hnextCurrent : next.currentTime ≤ target := by
              rw [hnextTime]
              linarith
            have htail := ih next hnextCurrent hnextPositive hnextWork hnextCount
            have hnextSquared : totalNonpreemptivePrioritySquaredResidualWork next =
                totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
              calc
                totalNonpreemptivePrioritySquaredResidualWork next =
                    totalNonpreemptivePrioritySquaredResidualWork completedAt - active.2 ^ 2 := by
                      dsimp [next]
                      apply totalNonpreemptivePrioritySquaredResidualWork_complete completedAt active
                      simp [completedAt, hactive]
                _ = totalNonpreemptivePrioritySquaredResidualWork state - active.2 ^ 2 := by
                      rw [totalNonpreemptivePrioritySquaredResidualWork_timeUpdate]
            have hfirstLinear : IntervalIntegrable
                (fun t : ℝ => active.2 - (t - state.currentTime))
                MeasureTheory.volume state.currentTime (state.currentTime + active.2) := by
              exact (continuous_const.sub (continuous_id.sub continuous_const)).intervalIntegrable
                (μ := MeasureTheory.volume) _ _
            have hfirst : IntervalIntegrable
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
                MeasureTheory.volume state.currentTime (state.currentTime + active.2) := by
              apply hfirstLinear.congr_ae
              have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
                  t ≠ state.currentTime + active.2 := by
                simp [MeasureTheory.ae_iff]
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
                MeasureTheory.ae_restrict_of_ae hne] with t ht hne
              rw [Set.uIoc_of_le (by linarith [hresidual])] at ht
              have htarget' : ¬ t ≤ state.currentTime := not_le_of_gt ht.1
              have hcomplete' : ¬ active.2 ≤ t - state.currentTime := by
                have hlt : t < state.currentTime + active.2 :=
                  lt_of_le_of_ne ht.2 hne
                linarith
              rw [activeNonpreemptivePriorityResidualWork_advance_partial
                fuel t state active htarget' hactive hcomplete']
            have htailEq : Set.EqOn
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t next))
                (Set.uIcc (state.currentTime + active.2) target) := by
              intro t ht
              rw [← hnextTime, Set.uIcc_of_le hnextCurrent] at ht
              have htarget' : ¬ t ≤ state.currentTime := by
                exact not_le_of_gt (by linarith [ht.1, hresidual])
              have hcomplete' : active.2 ≤ t - state.currentTime := by
                linarith [ht.1]
              simp [advanceNonpreemptivePriorityWorkState, htarget', hactive, hcomplete',
                completedAt, next]
            have htailIntegrableNext : IntervalIntegrable
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t next))
                MeasureTheory.volume (state.currentTime + active.2) target := by
              have htailRaw := htail.1
              rw [hnextTime] at htailRaw
              exact htailRaw
            have htailIntegrable : IntervalIntegrable
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
                MeasureTheory.volume (state.currentTime + active.2) target :=
              htailIntegrableNext.congr
                (htailEq.symm.mono Set.uIoc_subset_uIcc)
            have htailIntegral :
                (∫ t in (state.currentTime + active.2)..target,
                  activeNonpreemptivePriorityResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                  ∫ t in (state.currentTime + active.2)..target,
                    activeNonpreemptivePriorityResidualWork
                      (advanceNonpreemptivePriorityWorkState fuel t next) := by
              exact intervalIntegral.integral_congr htailEq
            have hfinal :
                totalNonpreemptivePrioritySquaredResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
                  totalNonpreemptivePrioritySquaredResidualWork
                    (advanceNonpreemptivePriorityWorkState fuel target next) := by
              simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete,
                completedAt, next]
            constructor
            · exact hfirst.trans htailIntegrable
            · calc
                totalNonpreemptivePrioritySquaredResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) +
                    2 * (∫ t in state.currentTime..target,
                      activeNonpreemptivePriorityResidualWork
                        (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                    totalNonpreemptivePrioritySquaredResidualWork
                      (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) +
                      2 * ((∫ t in state.currentTime..(state.currentTime + active.2),
                        activeNonpreemptivePriorityResidualWork
                          (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) +
                        ∫ t in (state.currentTime + active.2)..target,
                          activeNonpreemptivePriorityResidualWork
                            (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) := by
                      rw [← intervalIntegral.integral_add_adjacent_intervals
                        hfirst htailIntegrable]
                _ = totalNonpreemptivePrioritySquaredResidualWork
                      (advanceNonpreemptivePriorityWorkState fuel target next) +
                    2 * (active.2 ^ 2 / 2 +
                      ∫ t in (state.currentTime + active.2)..target,
                        activeNonpreemptivePriorityResidualWork
                          (advanceNonpreemptivePriorityWorkState fuel t next)) := by
                      rw [hfinal,
                        integral_activeNonpreemptivePriorityResidualWork_advance_initialService
                          fuel state active hactive hresidual,
                        htailIntegral]
                _ = (totalNonpreemptivePrioritySquaredResidualWork
                      (advanceNonpreemptivePriorityWorkState fuel target next) +
                    2 * (∫ t in (state.currentTime + active.2)..target,
                      activeNonpreemptivePriorityResidualWork
                        (advanceNonpreemptivePriorityWorkState fuel t next))) + active.2 ^ 2 := by
                      ring
                _ = totalNonpreemptivePrioritySquaredResidualWork next + active.2 ^ 2 := by
                      have htail' := congrArg (fun x : ℝ => x + active.2 ^ 2) htail.2
                      simpa [hnextTime] using htail'
                _ = totalNonpreemptivePrioritySquaredResidualWork state := by
                      rw [hnextSquared]
                      ring
          · have hlinear : IntervalIntegrable
                (fun t : ℝ => active.2 - (t - state.currentTime))
                MeasureTheory.volume state.currentTime target := by
              exact (continuous_const.sub (continuous_id.sub continuous_const)).intervalIntegrable
                (μ := MeasureTheory.volume) _ _
            have htrajectory : IntervalIntegrable
                (fun t => activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) t state))
                MeasureTheory.volume state.currentTime target := by
              apply hlinear.congr_ae
              have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ target := by
                simp [MeasureTheory.ae_iff]
              filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
                MeasureTheory.ae_restrict_of_ae hne] with t ht hne
              rw [Set.uIoc_of_le hcurrent] at ht
              have htarget' : ¬ t ≤ state.currentTime := not_le_of_gt ht.1
              have hcomplete' : ¬ active.2 ≤ t - state.currentTime := by
                have hlt : t < target := lt_of_le_of_ne ht.2 hne
                have hstrict : target - state.currentTime < active.2 :=
                  lt_of_not_ge hcomplete
                linarith
              rw [activeNonpreemptivePriorityResidualWork_advance_partial
                fuel t state active htarget' hactive hcomplete']
            have harea :
                (∫ t in state.currentTime..target,
                  activeNonpreemptivePriorityResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                  active.2 * (target - state.currentTime) -
                    (target - state.currentTime) ^ 2 / 2 := by
              calc
                (∫ t in state.currentTime..target,
                    activeNonpreemptivePriorityResidualWork
                      (advanceNonpreemptivePriorityWorkState (fuel + 1) t state)) =
                    ∫ t in state.currentTime..target,
                      active.2 - (t - state.currentTime) := by
                        apply intervalIntegral.integral_congr_ae
                        have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ target := by
                          simp [MeasureTheory.ae_iff]
                        filter_upwards [hne] with t hne ht
                        rw [Set.uIoc_of_le hcurrent] at ht
                        have htarget' : ¬ t ≤ state.currentTime := not_le_of_gt ht.1
                        have hcomplete' : ¬ active.2 ≤ t - state.currentTime := by
                          have hlt : t < target := lt_of_le_of_ne ht.2 hne
                          have hstrict : target - state.currentTime < active.2 :=
                            lt_of_not_ge hcomplete
                          linarith
                        rw [activeNonpreemptivePriorityResidualWork_advance_partial
                          fuel t state active htarget' hactive hcomplete']
                _ = active.2 * (target - state.currentTime) -
                      (target - state.currentTime) ^ 2 / 2 := by
                        have hraw := integral_residualServiceWork_over_elapsedInterval
                          state.currentTime (target - state.currentTime) active.2
                          (sub_nonneg.mpr hcurrent)
                        have hendpoint : state.currentTime +
                            (target - state.currentTime) = target := by ring
                        rw [hendpoint] at hraw
                        exact hraw
            have hsquare := totalNonpreemptivePrioritySquaredResidualWork_advance_partial
              fuel target state active htarget hactive hcomplete
            constructor
            · exact htrajectory
            · rw [hsquare, harea]
              ring

/-- Splicing one arrival into an arrival-free service interval adds exactly
the arriving job's squared requirement to the finite energy balance.  This is
the one-event form used to assemble deterministic queue slabs. -/
theorem intervalIntegrable_and_squaredResidualWork_energy_advanceThenAdmit
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ job.arrivalTime)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    IntervalIntegrable
      (fun t => activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState fuel t state))
      MeasureTheory.volume state.currentTime job.arrivalTime ∧
    totalNonpreemptivePrioritySquaredResidualWork
        (advanceThenAdmitNonpreemptivePriorityJob fuel state job) +
      2 * (∫ t in state.currentTime..job.arrivalTime,
        activeNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState fuel t state)) =
        totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
  have hadvance := intervalIntegrable_and_squaredResidualWork_energy_advance
    fuel job.arrivalTime state hcurrent hpositive hwork hfuel
  constructor
  · exact hadvance.1
  · unfold advanceThenAdmitNonpreemptivePriorityJob
    calc
      totalNonpreemptivePrioritySquaredResidualWork
          (admitNonpreemptivePriorityJob
            (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime state) job) +
          2 * (∫ t in state.currentTime..job.arrivalTime,
            activeNonpreemptivePriorityResidualWork
              (advanceNonpreemptivePriorityWorkState fuel t state)) =
          (totalNonpreemptivePrioritySquaredResidualWork
            (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime state) +
              job.serviceWork ^ 2) +
            2 * (∫ t in state.currentTime..job.arrivalTime,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t state)) := by
              rw [totalNonpreemptivePrioritySquaredResidualWork_admit]
      _ = (totalNonpreemptivePrioritySquaredResidualWork
            (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime state) +
            2 * (∫ t in state.currentTime..job.arrivalTime,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t state))) +
              job.serviceWork ^ 2 := by ring
      _ = totalNonpreemptivePrioritySquaredResidualWork state + job.serviceWork ^ 2 := by
            rw [hadvance.2]

/-- A waiting job contributes its full service requirement throughout its
waiting interval.  This is the deterministic per-customer contribution used
by waiting-work occupation arguments. -/
theorem integral_waitingServiceWork_over_waitingInterval
    (arrival serviceStart serviceWork : ℝ) :
    ∫ t in arrival..serviceStart, serviceWork =
      serviceWork * (serviceStart - arrival) := by
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- With enough completion fuel to cover every resident job, evolution to a
future target ends at that physical target time. -/
theorem advanceNonpreemptivePriorityWorkState_currentTime_eq_target
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    (advanceNonpreemptivePriorityWorkState fuel target state).currentTime = target := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, _⟩
      by_cases htarget : target ≤ state.currentTime
      · have heq : target = state.currentTime := le_antisymm htarget hcurrent
        simp [advanceNonpreemptivePriorityWorkState, heq]
      · simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have heq : target = state.currentTime := le_antisymm htarget hcurrent
        simp [advanceNonpreemptivePriorityWorkState, heq]
      · cases hactive : state.active with
        | none =>
            simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAtTime : completedAt.currentTime ≤ target := by
                dsimp [completedAt]
                linarith
              have hstepCount :
                  totalNonpreemptivePriorityWorkJobs
                      (completeNonpreemptivePriorityWorkJob completedAt) ≤ fuel := by
                have hcompletionCount :
                    totalNonpreemptivePriorityWorkJobs
                        (completeNonpreemptivePriorityWorkJob completedAt) + 1 =
                      totalNonpreemptivePriorityWorkJobs completedAt := by
                  apply totalNonpreemptivePriorityWorkJobs_complete_of_active completedAt active
                  simp [completedAt, hactive]
                have htimeCount :
                    totalNonpreemptivePriorityWorkJobs completedAt =
                      totalNonpreemptivePriorityWorkJobs state := by
                  rfl
                omega
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt)
                (by
                  rw [completeNonpreemptivePriorityWorkJob_currentTime]
                  exact hcompletedAtTime) hstepCount
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, completedAt] using hind
            · simp [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]

/-- The supplied physical arrival is the clock of the state immediately
after sufficient service evolution and its admission. -/
theorem advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ job.arrivalTime)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    (advanceThenAdmitNonpreemptivePriorityJob fuel state job).currentTime = job.arrivalTime := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [admitNonpreemptivePriorityJob_currentTime]
  exact advanceNonpreemptivePriorityWorkState_currentTime_eq_target
    fuel job.arrivalTime state hcurrent hfuel

/-- The active-residual area accumulated across a finite chronological arrival
trace.  Each summand follows the literal service evolution up to the next
arrival, then recurses from the state after that arrival is admitted. -/
noncomputable def nonpreemptivePriorityArrivalTraceActiveResidualArea
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    List (NonpreemptivePriorityJob n JobId) → ℝ
  | [] => 0
  | job :: jobs =>
      (∫ t in state.currentTime..job.arrivalTime,
        activeNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs state) t state)) +
        nonpreemptivePriorityArrivalTraceActiveResidualArea
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs state) state job) jobs

/-- The squared-residual energy telescope over a finite chronological trace.
It records the exact active-residual occupation across every interarrival
service interval, with each arrival contributing the square of its declared
requirement. -/
theorem nonpreemptivePriorityArrivalTrace_squaredResidualWork_energy
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    totalNonpreemptivePrioritySquaredResidualWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) +
      2 * nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs =
        totalNonpreemptivePrioritySquaredResidualWork initial +
          (jobs.map (fun job => job.serviceWork ^ 2)).sum := by
  induction jobs generalizing initial with
  | nil =>
      simp [runNonpreemptivePriorityArrivalTrace,
        nonpreemptivePriorityArrivalTraceActiveResidualArea]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let fuel := totalNonpreemptivePriorityWorkJobs initial
      let next := advanceThenAdmitNonpreemptivePriorityJob fuel initial job
      have hcurrent : initial.currentTime ≤ job.arrivalTime := hstart job (by simp)
      have hstep := intervalIntegrable_and_squaredResidualWork_energy_advanceThenAdmit
        fuel initial job hcurrent hpositive hwork le_rfl
      have hadvancedPositive : positiveNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) := by
        exact positiveNonpreemptivePriorityResidualWork_advance
          fuel job.arrivalTime initial hpositive
      have hnextPositive : positiveNonpreemptivePriorityResidualWork next := by
        dsimp [next]
        unfold advanceThenAdmitNonpreemptivePriorityJob
        exact positiveNonpreemptivePriorityResidualWork_admit
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) job
          hadvancedPositive (hjobs job (by simp))
      have hnextWork : nonpreemptivePriorityWorkConserving next := by
        dsimp [next]
        unfold advanceThenAdmitNonpreemptivePriorityJob
        exact nonpreemptivePriorityWorkConserving_admit
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) job
      have hnextTime : next.currentTime = job.arrivalTime := by
        dsimp [next]
        exact advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
          fuel initial job hcurrent le_rfl
      have htailStart : ∀ other ∈ jobs, next.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hnextTime]
        exact hhead other hother
      have htailEnergy := ih next htailStart htail hnextPositive hnextWork
        (fun other hother => hjobs other (by simp [hother]))
      change totalNonpreemptivePrioritySquaredResidualWork
          (runNonpreemptivePriorityArrivalTrace next jobs) +
        2 * ((∫ t in initial.currentTime..job.arrivalTime,
          activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState fuel t initial)) +
          nonpreemptivePriorityArrivalTraceActiveResidualArea next jobs) =
          totalNonpreemptivePrioritySquaredResidualWork initial +
            ((job :: jobs).map (fun other => other.serviceWork ^ 2)).sum
      calc
        totalNonpreemptivePrioritySquaredResidualWork
            (runNonpreemptivePriorityArrivalTrace next jobs) +
          2 * ((∫ t in initial.currentTime..job.arrivalTime,
            activeNonpreemptivePriorityResidualWork
              (advanceNonpreemptivePriorityWorkState fuel t initial)) +
            nonpreemptivePriorityArrivalTraceActiveResidualArea next jobs) =
            (totalNonpreemptivePrioritySquaredResidualWork
              (runNonpreemptivePriorityArrivalTrace next jobs) +
              2 * nonpreemptivePriorityArrivalTraceActiveResidualArea next jobs) +
              2 * (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t initial)) := by ring
        _ = (totalNonpreemptivePrioritySquaredResidualWork next +
              (jobs.map (fun other => other.serviceWork ^ 2)).sum) +
              2 * (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t initial)) := by
              rw [htailEnergy]
        _ = (totalNonpreemptivePrioritySquaredResidualWork next +
              2 * (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t initial))) +
              (jobs.map (fun other => other.serviceWork ^ 2)).sum := by ring
        _ = (totalNonpreemptivePrioritySquaredResidualWork initial + job.serviceWork ^ 2) +
              (jobs.map (fun other => other.serviceWork ^ 2)).sum := by
              rw [hstep.2]
        _ = totalNonpreemptivePrioritySquaredResidualWork initial +
              ((job :: jobs).map (fun other => other.serviceWork ^ 2)).sum := by
              simp
              ring

/-- The active-residual area of a finite trace through a prescribed terminal
time.  It appends the final arrival-free service interval to the chronological
interarrival area. -/
noncomputable def nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (terminal : ℝ) : ℝ :=
  nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs +
    ∫ t in (runNonpreemptivePriorityArrivalTrace initial jobs).currentTime..terminal,
      activeNonpreemptivePriorityResidualWork
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial jobs)) t
          (runNonpreemptivePriorityArrivalTrace initial jobs))

/-- The literal finite queue state at a physical time during a supplied
chronological trace.  Before the next arrival it is the deterministic service
evolution of the current state; at and after that arrival it continues from
the admitted state on the remaining suffix. -/
noncomputable def nonpreemptivePriorityArrivalTraceStateAt
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    List (NonpreemptivePriorityJob n JobId) → ℝ →
      NonpreemptivePriorityWorkState n JobId
  | [], time =>
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs state) time state
  | job :: jobs, time =>
      if time < job.arrivalTime then
        advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs state) time state
      else
        nonpreemptivePriorityArrivalTraceStateAt
          (advanceThenAdmitNonpreemptivePriorityJob
            (totalNonpreemptivePriorityWorkJobs state) state job) jobs time

/-- At a terminal time after every arrival of a chronological finite trace,
the recursive state-at-time path is exactly the usual run followed by final
arrival-free service evolution. -/
theorem nonpreemptivePriorityArrivalTraceStateAt_terminal_eq_advance_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (terminal : ℝ)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hterminal : ∀ job ∈ jobs, job.arrivalTime ≤ terminal) :
    nonpreemptivePriorityArrivalTraceStateAt initial jobs terminal =
      advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace initial jobs)) terminal
        (runNonpreemptivePriorityArrivalTrace initial jobs) := by
  induction jobs generalizing initial with
  | nil =>
      rfl
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let fuel := totalNonpreemptivePriorityWorkJobs initial
      let next := advanceThenAdmitNonpreemptivePriorityJob fuel initial job
      have hcurrent : initial.currentTime ≤ job.arrivalTime := hstart job (by simp)
      have hnextTime : next.currentTime = job.arrivalTime := by
        dsimp [next]
        exact advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
          fuel initial job hcurrent le_rfl
      have htailStart : ∀ other ∈ jobs, next.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hnextTime]
        exact hhead other hother
      have htailTerminal : ∀ other ∈ jobs, other.arrivalTime ≤ terminal := by
        intro other hother
        exact hterminal other (by simp [hother])
      have hrec := ih next htailStart htail htailTerminal
      have hjobTerminal : ¬ terminal < job.arrivalTime :=
        not_lt_of_ge (hterminal job (by simp))
      change (if terminal < job.arrivalTime then
        advanceNonpreemptivePriorityWorkState fuel terminal initial else
          nonpreemptivePriorityArrivalTraceStateAt next jobs terminal) =
        advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial (job :: jobs))) terminal
          (runNonpreemptivePriorityArrivalTrace initial (job :: jobs))
      rw [if_neg hjobTerminal, hrec]
      simp [runNonpreemptivePriorityArrivalTrace, fuel, next,
        advanceThenAdmitNonpreemptivePriorityJob]

/-- Future arrivals strictly after a target time do not affect the finite
trace state at that target.  This is a deterministic prefix principle; the
weak inequality on the prefix intentionally permits an arrival exactly at the
target to be included in the state. -/
theorem nonpreemptivePriorityArrivalTraceStateAt_append_of_target_lt
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId)) (target : ℝ)
    (hfront : ∀ job ∈ front, job.arrivalTime ≤ target)
    (htail : ∀ job ∈ tail, target < job.arrivalTime) :
    nonpreemptivePriorityArrivalTraceStateAt initial (front ++ tail) target =
      nonpreemptivePriorityArrivalTraceStateAt initial front target := by
  induction front generalizing initial with
  | nil =>
      cases tail with
      | nil => rfl
      | cons job tail =>
          have htarget : target < job.arrivalTime := htail job (by simp)
          simp [nonpreemptivePriorityArrivalTraceStateAt, htarget]
  | cons job front ih =>
      have hjob : job.arrivalTime ≤ target := hfront job (by simp)
      have hnot : ¬ target < job.arrivalTime := not_lt_of_ge hjob
      have hrec := ih
        (advanceThenAdmitNonpreemptivePriorityJob
          (totalNonpreemptivePriorityWorkJobs initial) initial job)
        (by
          intro other hother
          exact hfront other (by simp [hother]))
      simpa [nonpreemptivePriorityArrivalTraceStateAt, hnot] using hrec

/-- A finite arrival trace has no arrival at almost every physical time. -/
theorem ae_forall_mem_nonpreemptivePriorityArrivalTrace_arrivalTime_ne
    {n : ℕ} {JobId : Type*}
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    ∀ᵐ t : ℝ ∂MeasureTheory.volume,
      ∀ job ∈ jobs, job.arrivalTime ≠ t := by
  induction jobs with
  | nil =>
      exact Filter.Eventually.of_forall fun t job hjob => by
        simp at hjob
  | cons job jobs ih =>
      have hhead : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
          job.arrivalTime ≠ t := by
        have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
            t ≠ job.arrivalTime := by
          simp [MeasureTheory.ae_iff]
        filter_upwards [hne] with t ht
        exact Ne.symm ht
      filter_upwards [hhead, ih] with t hhead htail
      intro other hother
      rcases List.mem_cons.mp hother with hother | hother
      · subst other
        exact hhead
      · exact htail other hother

/-- The explicit finite trace state path is interval-integrable, and its
active-residual integral is exactly the recursively assembled trace area. -/
theorem intervalIntegrable_and_integral_activeNonpreemptivePriorityArrivalTraceStateAt
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (terminal : ℝ)
    (hinitialTerminal : initial.currentTime ≤ terminal)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hterminal : ∀ job ∈ jobs, job.arrivalTime ≤ terminal)
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    IntervalIntegrable
      (fun t => activeNonpreemptivePriorityResidualWork
        (nonpreemptivePriorityArrivalTraceStateAt initial jobs t))
      MeasureTheory.volume initial.currentTime terminal ∧
    (∫ t in initial.currentTime..terminal,
      activeNonpreemptivePriorityResidualWork
        (nonpreemptivePriorityArrivalTraceStateAt initial jobs t)) =
      nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough initial jobs terminal := by
  induction jobs generalizing initial with
  | nil =>
      have hadvance := intervalIntegrable_and_squaredResidualWork_energy_advance
        (totalNonpreemptivePriorityWorkJobs initial) terminal initial
        hinitialTerminal hpositive hwork le_rfl
      constructor
      · simpa [nonpreemptivePriorityArrivalTraceStateAt] using hadvance.1
      · simp [nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough,
          nonpreemptivePriorityArrivalTraceActiveResidualArea,
          nonpreemptivePriorityArrivalTraceStateAt,
          runNonpreemptivePriorityArrivalTrace]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let fuel := totalNonpreemptivePriorityWorkJobs initial
      let next := advanceThenAdmitNonpreemptivePriorityJob fuel initial job
      have hcurrent : initial.currentTime ≤ job.arrivalTime := hstart job (by simp)
      have hjobTerminal : job.arrivalTime ≤ terminal := hterminal job (by simp)
      have hstep := intervalIntegrable_and_squaredResidualWork_energy_advance
        fuel job.arrivalTime initial hcurrent hpositive hwork le_rfl
      have hadvancedPositive : positiveNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) := by
        exact positiveNonpreemptivePriorityResidualWork_advance
          fuel job.arrivalTime initial hpositive
      have hnextPositive : positiveNonpreemptivePriorityResidualWork next := by
        dsimp [next]
        unfold advanceThenAdmitNonpreemptivePriorityJob
        exact positiveNonpreemptivePriorityResidualWork_admit
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) job
          hadvancedPositive (hjobs job (by simp))
      have hnextWork : nonpreemptivePriorityWorkConserving next := by
        dsimp [next]
        unfold advanceThenAdmitNonpreemptivePriorityJob
        exact nonpreemptivePriorityWorkConserving_admit
          (advanceNonpreemptivePriorityWorkState fuel job.arrivalTime initial) job
      have hnextTime : next.currentTime = job.arrivalTime := by
        dsimp [next]
        exact advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
          fuel initial job hcurrent le_rfl
      have htailStart : ∀ other ∈ jobs, next.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hnextTime]
        exact hhead other hother
      have htailTerminal : ∀ other ∈ jobs, other.arrivalTime ≤ terminal := by
        intro other hother
        exact hterminal other (by simp [hother])
      have hnextTerminal : next.currentTime ≤ terminal := by
        rw [hnextTime]
        exact hjobTerminal
      have htailIntegral := ih next hnextTerminal htailStart htail htailTerminal
        hnextPositive hnextWork (fun other hother => hjobs other (by simp [hother]))
      have hleftAERestrict :
          (fun t => activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState fuel t initial)) =ᵐ[
              MeasureTheory.volume.restrict
                (Set.uIoc initial.currentTime job.arrivalTime)]
            fun t => activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t) := by
        have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ job.arrivalTime := by
          simp [MeasureTheory.ae_iff]
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
          MeasureTheory.ae_restrict_of_ae hne] with t ht hne
        rw [Set.uIoc_of_le hcurrent] at ht
        have hlt : t < job.arrivalTime := lt_of_le_of_ne ht.2 hne
        simp [nonpreemptivePriorityArrivalTraceStateAt, hlt, fuel]
      have hleftAEInterval : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
          t ∈ Set.uIoc initial.currentTime job.arrivalTime →
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t) =
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t initial) := by
        have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ job.arrivalTime := by
          simp [MeasureTheory.ae_iff]
        filter_upwards [hne] with t hne ht
        rw [Set.uIoc_of_le hcurrent] at ht
        have hlt : t < job.arrivalTime := lt_of_le_of_ne ht.2 hne
        simp [nonpreemptivePriorityArrivalTraceStateAt, hlt, fuel]
      have hleft : IntervalIntegrable
          (fun t => activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t))
          MeasureTheory.volume initial.currentTime job.arrivalTime :=
        hstep.1.congr_ae hleftAERestrict
      have hrightAERestrict :
          (fun t => activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt next jobs t)) =ᵐ[
              MeasureTheory.volume.restrict (Set.uIoc next.currentTime terminal)]
            fun t => activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht
        rw [hnextTime, Set.uIoc_of_le hjobTerminal] at ht
        have hnot : ¬ t < job.arrivalTime := not_lt_of_ge ht.1.le
        simp [nonpreemptivePriorityArrivalTraceStateAt, hnot, next, fuel]
      have hrightAEInterval : ∀ᵐ t : ℝ ∂MeasureTheory.volume,
          t ∈ Set.uIoc next.currentTime terminal →
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t) =
              activeNonpreemptivePriorityResidualWork
                (nonpreemptivePriorityArrivalTraceStateAt next jobs t) := by
        filter_upwards with t ht
        rw [hnextTime, Set.uIoc_of_le hjobTerminal] at ht
        have hnot : ¬ t < job.arrivalTime := not_lt_of_ge ht.1.le
        simp [nonpreemptivePriorityArrivalTraceStateAt, hnot, next, fuel]
      have hrightRaw : IntervalIntegrable
          (fun t => activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t))
          MeasureTheory.volume next.currentTime terminal :=
        htailIntegral.1.congr_ae hrightAERestrict
      have hright : IntervalIntegrable
          (fun t => activeNonpreemptivePriorityResidualWork
            (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t))
          MeasureTheory.volume job.arrivalTime terminal := by
        rw [← hnextTime]
        exact hrightRaw
      have hleftIntegral :
          (∫ t in initial.currentTime..job.arrivalTime,
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t)) =
            ∫ t in initial.currentTime..job.arrivalTime,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t initial) := by
          exact intervalIntegral.integral_congr_ae hleftAEInterval
      have hrightIntegral :
          (∫ t in job.arrivalTime..terminal,
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t)) =
            ∫ t in job.arrivalTime..terminal,
              activeNonpreemptivePriorityResidualWork
                (nonpreemptivePriorityArrivalTraceStateAt next jobs t) := by
          rw [← hnextTime]
          exact intervalIntegral.integral_congr_ae hrightAEInterval
      have harea : nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough
          initial (job :: jobs) terminal =
            (∫ t in initial.currentTime..job.arrivalTime,
              activeNonpreemptivePriorityResidualWork
                (advanceNonpreemptivePriorityWorkState fuel t initial)) +
              nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough next jobs terminal := by
        simp [nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough,
          nonpreemptivePriorityArrivalTraceActiveResidualArea,
          runNonpreemptivePriorityArrivalTrace, next, fuel,
          advanceThenAdmitNonpreemptivePriorityJob]
        ring
      have htailIntegralAtArrival :
          (∫ t in job.arrivalTime..terminal,
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt next jobs t)) =
            nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough next jobs terminal := by
        simpa only [hnextTime] using htailIntegral.2
      constructor
      · exact hleft.trans hright
      · calc
          (∫ t in initial.currentTime..terminal,
            activeNonpreemptivePriorityResidualWork
              (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t)) =
              (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t)) +
                ∫ t in job.arrivalTime..terminal,
                  activeNonpreemptivePriorityResidualWork
                    (nonpreemptivePriorityArrivalTraceStateAt initial (job :: jobs) t) := by
                    exact (intervalIntegral.integral_add_adjacent_intervals
                      hleft hright).symm
          _ = (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t initial)) +
                ∫ t in job.arrivalTime..terminal,
                  activeNonpreemptivePriorityResidualWork
                    (nonpreemptivePriorityArrivalTraceStateAt next jobs t) := by
                    rw [hleftIntegral, hrightIntegral]
          _ = (∫ t in initial.currentTime..job.arrivalTime,
                activeNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState fuel t initial)) +
                nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough next jobs terminal := by
                  exact congrArg (fun x : ℝ =>
                    (∫ t in initial.currentTime..job.arrivalTime,
                      activeNonpreemptivePriorityResidualWork
                        (advanceNonpreemptivePriorityWorkState fuel t initial)) + x)
                    htailIntegralAtArrival
          _ = nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough
                initial (job :: jobs) terminal := harea.symm

/-- The finite chronological-trace energy telescope through a terminal
physical time.  This is the deterministic slab identity: the final squared
ledger plus twice the active-residual area equals the initial squared ledger
plus the sum of squared requirements admitted in the slab. -/
theorem nonpreemptivePriorityArrivalTrace_squaredResidualWork_energy_through
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (terminal : ℝ)
    (hinitialTerminal : initial.currentTime ≤ terminal)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hterminal : ∀ job ∈ jobs, job.arrivalTime ≤ terminal)
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hjobs : ∀ job ∈ jobs, 0 < job.serviceWork) :
    totalNonpreemptivePrioritySquaredResidualWork
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs
            (runNonpreemptivePriorityArrivalTrace initial jobs)) terminal
          (runNonpreemptivePriorityArrivalTrace initial jobs)) +
      2 * nonpreemptivePriorityArrivalTraceActiveResidualAreaThrough initial jobs terminal =
        totalNonpreemptivePrioritySquaredResidualWork initial +
          (jobs.map (fun job => job.serviceWork ^ 2)).sum := by
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hafterCurrent : afterArrivals.currentTime ≤ terminal := by
    dsimp [afterArrivals]
    apply runNonpreemptivePriorityArrivalTrace_currentTime_le initial jobs terminal
    · exact hinitialTerminal
    · exact hterminal
  have hafterPositive : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using
      positiveNonpreemptivePriorityResidualWork_run initial jobs hpositive hjobs
  have hafterWork : nonpreemptivePriorityWorkConserving afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityWorkConserving_run initial jobs hwork
  have hfinalEnergy := intervalIntegrable_and_squaredResidualWork_energy_advance
    (totalNonpreemptivePriorityWorkJobs afterArrivals) terminal afterArrivals
    hafterCurrent hafterPositive hafterWork le_rfl
  have htraceEnergy := nonpreemptivePriorityArrivalTrace_squaredResidualWork_energy
    initial jobs hstart hsorted hpositive hwork hjobs
  change totalNonpreemptivePrioritySquaredResidualWork
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) terminal afterArrivals) +
    2 * (nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs +
      ∫ t in afterArrivals.currentTime..terminal,
        activeNonpreemptivePriorityResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)) =
      totalNonpreemptivePrioritySquaredResidualWork initial +
        (jobs.map (fun job => job.serviceWork ^ 2)).sum
  calc
    totalNonpreemptivePrioritySquaredResidualWork
        (advanceNonpreemptivePriorityWorkState
          (totalNonpreemptivePriorityWorkJobs afterArrivals) terminal afterArrivals) +
      2 * (nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs +
        ∫ t in afterArrivals.currentTime..terminal,
          activeNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState
              (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals)) =
        (totalNonpreemptivePrioritySquaredResidualWork
          (advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs afterArrivals) terminal afterArrivals) +
          2 * (∫ t in afterArrivals.currentTime..terminal,
            activeNonpreemptivePriorityResidualWork
              (advanceNonpreemptivePriorityWorkState
                (totalNonpreemptivePriorityWorkJobs afterArrivals) t afterArrivals))) +
          2 * nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs := by ring
    _ = totalNonpreemptivePrioritySquaredResidualWork afterArrivals +
          2 * nonpreemptivePriorityArrivalTraceActiveResidualArea initial jobs := by
          rw [hfinalEnergy.2]
    _ = totalNonpreemptivePrioritySquaredResidualWork initial +
          (jobs.map (fun job => job.serviceWork ^ 2)).sum := by
          simpa [afterArrivals] using htraceEnergy

/-- A state with no active job and no waiting jobs has zero residual work. -/
theorem totalNonpreemptivePriorityResidualWork_eq_zero_of_empty
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (hactive : state.active = none)
    (hwaiting : ∀ i, state.waiting i = []) :
    totalNonpreemptivePriorityResidualWork state = 0 := by
  unfold totalNonpreemptivePriorityResidualWork
    activeNonpreemptivePriorityResidualWork
  simp only [hactive, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  simp [priorityWaitingResidualWork, hwaiting i]

/-- With at least as much completion fuel as resident jobs, a work-conserving
positive-residual finite state loses exactly its elapsed service capacity,
clipped at zero. -/
theorem totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) =
      max 0 (totalNonpreemptivePriorityResidualWork state -
        (target - state.currentTime)) := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, hwaiting⟩
      have htotal : totalNonpreemptivePriorityResidualWork state = 0 :=
        totalNonpreemptivePriorityResidualWork_eq_zero_of_empty state hactive hwaiting
      have hsub : 0 - (target - state.currentTime) ≤ 0 := by
        linarith
      calc
        totalNonpreemptivePriorityResidualWork
            (advanceNonpreemptivePriorityWorkState 0 target state) = 0 := by
              by_cases htarget : target ≤ state.currentTime
              · simpa [advanceNonpreemptivePriorityWorkState, htarget] using htotal
              · calc
                  totalNonpreemptivePriorityResidualWork
                      (advanceNonpreemptivePriorityWorkState 0 target state) =
                      totalNonpreemptivePriorityResidualWork
                        { state with currentTime := target } := by
                        simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
                  _ = totalNonpreemptivePriorityResidualWork state :=
                    totalNonpreemptivePriorityResidualWork_timeUpdate state target
                  _ = 0 := htotal
        _ = max 0 (0 - (target - state.currentTime)) := (max_eq_left hsub).symm
        _ = max 0 (totalNonpreemptivePriorityResidualWork state -
              (target - state.currentTime)) := by rw [htotal]
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have heq : target = state.currentTime := le_antisymm htarget hcurrent
        subst target
        have hnonneg : 0 ≤ totalNonpreemptivePriorityResidualWork state :=
          totalNonpreemptivePriorityResidualWork_nonneg state hpositive.nonnegative
        simp [advanceNonpreemptivePriorityWorkState, max_eq_right hnonneg]
      · cases hactive : state.active with
        | none =>
            have hwaiting : ∀ i, state.waiting i = [] := by
              intro i
              cases hlist : state.waiting i with
              | nil => simp
              | cons head tail =>
                  exact False.elim (hwork hactive ⟨i, by simp [hlist]⟩)
            have htotal : totalNonpreemptivePriorityResidualWork state = 0 :=
              totalNonpreemptivePriorityResidualWork_eq_zero_of_empty state hactive hwaiting
            have hsub : 0 - (target - state.currentTime) ≤ 0 := by
              linarith
            calc
              totalNonpreemptivePriorityResidualWork
                  (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
                  totalNonpreemptivePriorityResidualWork
                    { state with currentTime := target } := by
                      simp [advanceNonpreemptivePriorityWorkState, htarget, hactive]
              _ = 0 := by rw [totalNonpreemptivePriorityResidualWork_timeUpdate, htotal]
              _ = max 0 (0 - (target - state.currentTime)) := (max_eq_left hsub).symm
              _ = max 0 (totalNonpreemptivePriorityResidualWork state -
                    (target - state.currentTime)) := by rw [htotal]
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hcompletedAtPositive :
                  positiveNonpreemptivePriorityResidualWork completedAt := by
                simpa [completedAt] using hpositive
              have hcompletedAtWork : nonpreemptivePriorityWorkConserving completedAt := by
                intro hnone
                exact (Option.some_ne_none active
                  (by simpa [completedAt, hactive] using hnone)).elim
              have hstepPositive :
                  positiveNonpreemptivePriorityResidualWork
                    (completeNonpreemptivePriorityWorkJob completedAt) :=
                positiveNonpreemptivePriorityResidualWork_complete
                  completedAt hcompletedAtPositive
              have hstepWork : nonpreemptivePriorityWorkConserving
                  (completeNonpreemptivePriorityWorkJob completedAt) :=
                nonpreemptivePriorityWorkConserving_complete completedAt hcompletedAtWork
              have hstepTime :
                  (completeNonpreemptivePriorityWorkJob completedAt).currentTime ≤ target := by
                rw [completeNonpreemptivePriorityWorkJob_currentTime]
                dsimp [completedAt]
                linarith
              have hstepCount :
                  totalNonpreemptivePriorityWorkJobs
                      (completeNonpreemptivePriorityWorkJob completedAt) ≤ fuel := by
                have hcompletionCount :
                    totalNonpreemptivePriorityWorkJobs
                        (completeNonpreemptivePriorityWorkJob completedAt) + 1 =
                      totalNonpreemptivePriorityWorkJobs completedAt := by
                  apply totalNonpreemptivePriorityWorkJobs_complete_of_active completedAt active
                  simp [completedAt, hactive]
                have htimeCount :
                    totalNonpreemptivePriorityWorkJobs completedAt =
                      totalNonpreemptivePriorityWorkJobs state := by
                  rfl
                omega
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt)
                hstepTime hstepPositive hstepWork hstepCount
              have hcompletionWork :
                  totalNonpreemptivePriorityResidualWork
                    (completeNonpreemptivePriorityWorkJob completedAt) =
                    totalNonpreemptivePriorityResidualWork state - active.2 := by
                calc
                  totalNonpreemptivePriorityResidualWork
                      (completeNonpreemptivePriorityWorkJob completedAt) =
                      totalNonpreemptivePriorityResidualWork completedAt - active.2 := by
                    apply totalNonpreemptivePriorityResidualWork_complete completedAt active
                    simp [completedAt, hactive]
                  _ = totalNonpreemptivePriorityResidualWork state - active.2 := by
                    rw [totalNonpreemptivePriorityResidualWork_timeUpdate]
              calc
                totalNonpreemptivePriorityResidualWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) =
                    totalNonpreemptivePriorityResidualWork
                      (advanceNonpreemptivePriorityWorkState fuel target
                        (completeNonpreemptivePriorityWorkJob completedAt)) := by
                      simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                        hcomplete, completedAt]
                _ = max 0 (totalNonpreemptivePriorityResidualWork
                      (completeNonpreemptivePriorityWorkJob completedAt) -
                    (target -
                      (completeNonpreemptivePriorityWorkJob completedAt).currentTime)) := hind
                _ = max 0 (totalNonpreemptivePriorityResidualWork state -
                    (target - state.currentTime)) := by
                      have hins :
                          totalNonpreemptivePriorityResidualWork
                              (completeNonpreemptivePriorityWorkJob completedAt) -
                            (target -
                              (completeNonpreemptivePriorityWorkJob completedAt).currentTime) =
                            totalNonpreemptivePriorityResidualWork state -
                              (target - state.currentTime) := by
                        rw [hcompletionWork,
                          completeNonpreemptivePriorityWorkJob_currentTime]
                        dsimp [completedAt]
                        ring
                      rw [hins]
            · have hpartial :=
                totalNonpreemptivePriorityResidualWork_advance_partial fuel target state active
                  htarget hactive hcomplete
              have hwaitingNonneg :
                  0 ≤ ∑ i, priorityWaitingResidualWork state i := by
                apply Finset.sum_nonneg
                intro i _
                exact priorityWaitingResidualWork_nonneg state hpositive.nonnegative i
              have hsubNonneg :
                  0 ≤ totalNonpreemptivePriorityResidualWork state -
                    (target - state.currentTime) := by
                unfold totalNonpreemptivePriorityResidualWork
                  activeNonpreemptivePriorityResidualWork
                simp [hactive]
                have hstrict : target - state.currentTime < active.2 :=
                  lt_of_not_ge hcomplete
                linarith
              rw [hpartial]
              exact (max_eq_right hsubNonneg).symm

/-- If positive residual work remains at the endpoint of an arrival-free
service interval, work-conserving service has supplied exactly the elapsed
capacity: the reflected workload formula is unreflected on that interval. -/
theorem totalNonpreemptivePriorityResidualWork_advance_eq_sub_of_workConserving_of_pos
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (htarget : 0 < totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state)) :
    totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel target state) =
      totalNonpreemptivePriorityResidualWork state -
        (target - state.currentTime) := by
  have hformula := totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
    fuel target state hcurrent hpositive hwork hfuel
  have hraw : 0 < totalNonpreemptivePriorityResidualWork state -
      (target - state.currentTime) := by
    by_contra hnot
    have hnonpos : totalNonpreemptivePriorityResidualWork state -
        (target - state.currentTime) ≤ 0 := le_of_not_gt hnot
    rw [hformula, max_eq_left hnonpos] at htarget
    linarith
  rw [hformula, max_eq_right hraw.le]

/-- Once a work-conserving positive-residual queue is empty at an intermediate
physical epoch, it is also empty at every later epoch with no intervening
arrivals.  This is the service-only semigroup property needed when a finite
arrival trace is split at a deterministic time. -/
theorem totalNonpreemptivePriorityResidualWork_advance_eq_zero_of_advance_eq_zero
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (cutoff terminal : ℝ)
    (hcurrentCutoff : state.currentTime ≤ cutoff)
    (hcutoffTerminal : cutoff ≤ terminal)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hcutoffZero : totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel cutoff state) = 0) :
    totalNonpreemptivePriorityResidualWork
      (advanceNonpreemptivePriorityWorkState fuel terminal state) = 0 := by
  have hcutoffFormula := totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
    fuel cutoff state hcurrentCutoff hpositive hwork hfuel
  have hremaining : totalNonpreemptivePriorityResidualWork state -
      (cutoff - state.currentTime) ≤ 0 := by
    calc
      totalNonpreemptivePriorityResidualWork state -
          (cutoff - state.currentTime) ≤
          max 0 (totalNonpreemptivePriorityResidualWork state -
            (cutoff - state.currentTime)) := le_max_right _ _
      _ = 0 := by rw [← hcutoffFormula, hcutoffZero]
  rw [totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
    fuel terminal state (hcurrentCutoff.trans hcutoffTerminal) hpositive hwork hfuel]
  apply max_eq_left
  linarith

/-- Between two physical arrivals, a work-conserving priority queue reflects
its unfinished work by elapsed time; admitting the next job then adds exactly
that job's service work. -/
theorem totalNonpreemptivePriorityResidualWork_advanceThenAdmit
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ job.arrivalTime)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel) :
    totalNonpreemptivePriorityResidualWork
      (advanceThenAdmitNonpreemptivePriorityJob fuel state job) =
      max 0 (totalNonpreemptivePriorityResidualWork state -
        (job.arrivalTime - state.currentTime)) + job.serviceWork := by
  unfold advanceThenAdmitNonpreemptivePriorityJob
  rw [totalNonpreemptivePriorityResidualWork_admit,
    totalNonpreemptivePriorityResidualWork_advance_eq_max_sub_of_workConserving
      fuel job.arrivalTime state hcurrent hpositive hwork hfuel]

end Queueing
end AppliedModelingLib
