import AppliedModelingLib.Queueing.NonpreemptivePriorityFiniteTrace

/-!
# Job population of finite nonpreemptive-priority traces

The finite trace uses a completion-fuel parameter.  These population identities
show that every actual completion consumes one resident job while priority
selection itself only relocates a waiting job into service.
-/

namespace AppliedModelingLib
namespace Queueing

/-- Starting a waiting job preserves the number of resident jobs. -/
theorem totalNonpreemptivePriorityWorkJobs_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) :
    totalNonpreemptivePriorityWorkJobs
      (startNextNonpreemptivePriorityJob state) =
      totalNonpreemptivePriorityWorkJobs state := by
  classical
  cases hactive : state.active with
  | some active =>
      simp [startNextNonpreemptivePriorityJob, hactive,
        totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hhead : state.waiting selected with
        | nil =>
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
              totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]
        | cons head tail =>
            have hwaitingLengths :
                (fun i => (startNextNonpreemptivePriorityJob state).waiting i |>.length) =
                  Function.update (fun i => (state.waiting i).length) selected tail.length := by
              funext i
              by_cases hi : i = selected
              · subst i
                simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
              · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead,
                  Function.update_of_ne hi]
            have hselectedLength : (state.waiting selected).length = tail.length + 1 := by
              simp [hhead]
            unfold totalNonpreemptivePriorityWorkJobs totalPriorityWaitingJobs
            rw [hwaitingLengths, Finset.sum_update_of_mem (Finset.mem_univ selected)]
            rw [← Finset.sum_erase_add _ (fun i => (state.waiting i).length)
              (Finset.mem_univ selected)]
            rw [Finset.sdiff_singleton_eq_erase, hselectedLength]
            simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hhead]
            all_goals omega
      · simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
          totalNonpreemptivePriorityWorkJobs, totalPriorityWaitingJobs]

/-- Completing an active job removes exactly one resident job, independent of
which waiting class begins the next nonpreemptive service. -/
theorem totalNonpreemptivePriorityWorkJobs_complete_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active) :
    totalNonpreemptivePriorityWorkJobs
      (completeNonpreemptivePriorityWorkJob state) + 1 =
      totalNonpreemptivePriorityWorkJobs state := by
  let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
    { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
  have hstart := totalNonpreemptivePriorityWorkJobs_startNext afterCompletion
  have hafter :
      totalNonpreemptivePriorityWorkJobs afterCompletion + 1 =
        totalNonpreemptivePriorityWorkJobs state := by
    unfold totalNonpreemptivePriorityWorkJobs totalPriorityWaitingJobs
    simp [afterCompletion, hactive]
    omega
  calc
    totalNonpreemptivePriorityWorkJobs
        (completeNonpreemptivePriorityWorkJob state) + 1 =
        totalNonpreemptivePriorityWorkJobs afterCompletion + 1 := by
          simpa only [completeNonpreemptivePriorityWorkJob, hactive] using
            congrArg (fun count => count + 1) hstart
    _ = totalNonpreemptivePriorityWorkJobs state := hafter

/-- A finite priority state with no resident jobs is concretely empty: it has
no active job and every class-FIFO list is empty. -/
theorem active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (htotal : totalNonpreemptivePriorityWorkJobs state = 0) :
    state.active = none ∧ ∀ i, state.waiting i = [] := by
  have hactive : state.active = none := by
    cases hstate : state.active with
    | none => simp
    | some active =>
        unfold totalNonpreemptivePriorityWorkJobs at htotal
        simp [hstate] at htotal
  constructor
  · exact hactive
  · intro i
    apply List.length_eq_zero_iff.mp
    have hwaiting : totalPriorityWaitingJobs state = 0 := by
      unfold totalNonpreemptivePriorityWorkJobs at htotal
      simpa [hactive] using htotal
    have hle : (state.waiting i).length ≤ totalPriorityWaitingJobs state := by
      unfold totalPriorityWaitingJobs
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j => (state.waiting j).length)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact Nat.eq_zero_of_le_zero (by simpa [hwaiting] using hle)

end Queueing
end AppliedModelingLib
