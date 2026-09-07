import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionChronology

/-!
# Live tagged jobs in finite priority states

This module separates a represented job that is still awaiting service from a
job already present in the completion ledger.  In a positive-work state, a
live job certifies strictly positive aggregate residual work and hence rules
out an idle interval.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- A job is live when it is either active or waiting, as opposed to appearing
only in the historical completion ledger. -/
def nonpreemptivePriorityWorkStateJobLive
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) : Prop :=
  (∃ residual, state.active = some (job, residual)) ∨
    ∃ priority, job ∈ state.waiting priority

/-- A represented job with no completion record is still live. -/
theorem nonpreemptivePriorityWorkStateJobLive_of_contains_of_not_completed
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state job)
    (hnotCompleted : ¬ ∃ completedAt, (job, completedAt) ∈ state.completed) :
    nonpreemptivePriorityWorkStateJobLive state job := by
  rcases hcontains with hactive | hwaiting | hcompleted
  · exact Or.inl hactive
  · exact Or.inr hwaiting
  · exact (hnotCompleted hcompleted).elim

/-- A live job in a positive-work priority state leaves strictly positive
aggregate residual work. -/
theorem totalNonpreemptivePriorityResidualWork_pos_of_jobLive
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hlive : nonpreemptivePriorityWorkStateJobLive state job) :
    0 < totalNonpreemptivePriorityResidualWork state := by
  rcases hlive with hactive | hwaiting
  · rcases hactive with ⟨residual, hactive⟩
    have hresidual : 0 < residual := hpositive.1 (job, residual) hactive
    have hwaitingNonnegative : 0 ≤ ∑ i, priorityWaitingResidualWork state i := by
      apply Finset.sum_nonneg
      intro i _
      unfold priorityWaitingResidualWork
      apply List.sum_nonneg
      intro work hmember
      rcases List.mem_map.mp hmember with ⟨other, hother, rfl⟩
      exact (hpositive.2 i other hother).le
    unfold totalNonpreemptivePriorityResidualWork activeNonpreemptivePriorityResidualWork
    simp [hactive]
    exact add_pos_of_pos_of_nonneg hresidual hwaitingNonnegative
  · rcases hwaiting with ⟨priority, hmember⟩
    have hwaitingPos : 0 < priorityWaitingResidualWork state priority :=
      priorityWaitingResidualWork_pos_of_mem state hpositive priority job hmember
    have hactiveNonnegative : 0 ≤ activeNonpreemptivePriorityResidualWork state := by
      unfold activeNonpreemptivePriorityResidualWork
      cases hactive : state.active with
      | none => simp
      | some active => exact (hpositive.1 active hactive).le
    have hsumPos : 0 < ∑ i, priorityWaitingResidualWork state i := by
      refine Finset.sum_pos' ?_ ?_
      · intro i _
        exact priorityWaitingResidualWork_nonneg state hpositive.nonnegative i
      · exact ⟨priority, Finset.mem_univ priority, hwaitingPos⟩
    unfold totalNonpreemptivePriorityResidualWork
    exact add_pos_of_nonneg_of_pos hactiveNonnegative hsumPos

end

end AppliedModelingLib.Queueing
