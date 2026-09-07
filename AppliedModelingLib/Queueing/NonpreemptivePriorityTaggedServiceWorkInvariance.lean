import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceLedger

/-!
# Tagged service-work invariance for finite priority traces

These deterministic lemmas isolate the fact that changing a waiting tag's own
declared service work does not alter the FIFO work preceding that tag.  They
are the local input for service-start predictability arguments.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- Replace only a job's declared service work, retaining its identifier,
priority class, and physical arrival time. -/
def nonpreemptivePriorityJobSetServiceWork
    {n : ℕ} {JobId : Type*}
    (serviceWork : ℝ) (job : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityJob n JobId :=
  { job with serviceWork }

theorem nonpreemptivePriorityJobSetServiceWork_identifier
    {n : ℕ} {JobId : Type*}
    (serviceWork : ℝ) (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobSetServiceWork serviceWork job).identifier = job.identifier := rfl

theorem nonpreemptivePriorityJobSetServiceWork_priority
    {n : ℕ} {JobId : Type*}
    (serviceWork : ℝ) (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobSetServiceWork serviceWork job).priority = job.priority := rfl

theorem nonpreemptivePriorityJobSetServiceWork_arrivalTime
    {n : ℕ} {JobId : Type*}
    (serviceWork : ℝ) (job : NonpreemptivePriorityJob n JobId) :
    (nonpreemptivePriorityJobSetServiceWork serviceWork job).arrivalTime = job.arrivalTime := rfl

/-- Replace one priority queue in a work state by a specified finite FIFO list. -/
def nonpreemptivePriorityWorkStateWithTaggedWaiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) :
    NonpreemptivePriorityWorkState n JobId :=
  { currentTime := state.currentTime
    active := state.active
    waiting := Function.update state.waiting tag.priority (front ++ [tag] ++ tail)
    completed := state.completed }

/-- Appending any finite suffix after a present FIFO tag does not affect the
work that precedes that tag. -/
theorem priorityWaitingResidualWorkBeforeTag_append_list_of_mem
    {n : ℕ} {JobId : Type*}
    (waiting suffix : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (hmem : tag ∈ waiting) :
    priorityWaitingResidualWorkBeforeTag (waiting ++ suffix) tag =
      priorityWaitingResidualWorkBeforeTag waiting tag := by
  induction suffix generalizing waiting with
  | nil => simp
  | cons newJob suffix ih =>
      have hmem' : tag ∈ waiting ++ [newJob] := List.mem_append_left _ hmem
      calc
        priorityWaitingResidualWorkBeforeTag (waiting ++ newJob :: suffix) tag =
            priorityWaitingResidualWorkBeforeTag ((waiting ++ [newJob]) ++ suffix) tag := by
              congr 1
              simp [List.append_assoc]
        _ = priorityWaitingResidualWorkBeforeTag (waiting ++ [newJob]) tag :=
          ih (waiting ++ [newJob]) hmem'
        _ = priorityWaitingResidualWorkBeforeTag waiting tag :=
        priorityWaitingResidualWorkBeforeTag_append_of_mem waiting tag newJob hmem

/-- FIFO work preceding a tag is nonnegative whenever every work requirement
in the list is nonnegative. -/
theorem priorityWaitingResidualWorkBeforeTag_nonneg
    {n : ℕ} {JobId : Type*}
    (waiting : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hwork : ∀ job ∈ waiting, 0 ≤ job.serviceWork) :
    0 ≤ priorityWaitingResidualWorkBeforeTag waiting tag := by
  induction waiting with
  | nil => simp [priorityWaitingResidualWorkBeforeTag]
  | cons head tail ih =>
      by_cases hhead : head = tag
      · simp [priorityWaitingResidualWorkBeforeTag, hhead]
      · rw [priorityWaitingResidualWorkBeforeTag_cons_of_ne head tag tail hhead]
        exact add_nonneg (hwork head (by simp))
          (ih (fun job hmem => hwork job (by simp [hmem])))

/-- In a work-conserving positive-work state, a tag that remains in a FIFO
list has strictly positive work to be served before it can start. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_pos_of_mem_waiting
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hconserving : nonpreemptivePriorityWorkConserving state)
    (hnotActive : ¬ ∃ residual, state.active = some (tag, residual))
    (hwaiting : tag ∈ state.waiting tag.priority) :
    0 < nonpreemptivePriorityTaggedPreServiceWork state tag := by
  have hactiveExists : state.active ≠ none := by
    intro hactive
    apply (hconserving hactive)
    exact ⟨tag.priority, List.length_pos_of_mem hwaiting⟩
  cases hactive : state.active with
  | none => exact (hactiveExists hactive).elim
  | some active =>
      have hactivePos : 0 < active.2 := hpositive.1 active hactive
      have hstrictNonneg : 0 ≤ priorityWaitingResidualWorkStrictlyMoreUrgent
          state tag.priority := by
        unfold priorityWaitingResidualWorkStrictlyMoreUrgent
        apply Finset.sum_nonneg
        intro priority _
        exact priorityWaitingResidualWork_nonneg state hpositive.nonnegative priority
      have hprefixNonneg : 0 ≤ priorityWaitingResidualWorkBeforeTag
          (state.waiting tag.priority) tag := by
        apply priorityWaitingResidualWorkBeforeTag_nonneg
        intro job hmem
        exact (hpositive.2 tag.priority job hmem).le
      unfold nonpreemptivePriorityTaggedPreServiceWork
      rw [if_neg hnotActive]
      simp only [activeNonpreemptivePriorityResidualWork, hactive]
      exact add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg hactivePos hstrictNonneg) hprefixNonneg

/-- If the FIFO prefix has no customer with the tag's identifier, replacing
the tag's service work leaves the total work ahead of it unchanged. -/
theorem priorityWaitingResidualWorkBeforeTag_append_setServiceWork_eq
    {n : ℕ} {JobId : Type*}
    (front tail : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (serviceWork : ℝ)
    (hfront : ∀ job ∈ front, job.identifier ≠ tag.identifier) :
    priorityWaitingResidualWorkBeforeTag
      (front ++ nonpreemptivePriorityJobSetServiceWork serviceWork tag :: tail)
      (nonpreemptivePriorityJobSetServiceWork serviceWork tag) =
    priorityWaitingResidualWorkBeforeTag (front ++ tag :: tail) tag := by
  let tag' := nonpreemptivePriorityJobSetServiceWork serviceWork tag
  have hnot : tag ∉ front := by
    intro hmem
    exact (hfront tag hmem) rfl
  have hnot' : tag' ∉ front := by
    intro hmem
    have hid : tag'.identifier = tag.identifier :=
      nonpreemptivePriorityJobSetServiceWork_identifier serviceWork tag
    exact (hfront tag' hmem) hid
  have hmem : tag ∈ front ++ [tag] := by simp
  have hmem' : tag' ∈ front ++ [tag'] := by simp
  calc
    priorityWaitingResidualWorkBeforeTag
        (front ++ tag' :: tail) tag' =
        priorityWaitingResidualWorkBeforeTag ((front ++ [tag']) ++ tail) tag' := by
          congr 1
          simp [List.append_assoc]
    _ = priorityWaitingResidualWorkBeforeTag (front ++ [tag']) tag' := by
      exact priorityWaitingResidualWorkBeforeTag_append_list_of_mem
        (front ++ [tag']) tail tag' hmem'
    _ = (front.map fun job => job.serviceWork).sum := by
      exact priorityWaitingResidualWorkBeforeTag_append_self_of_not_mem front tag' hnot'
    _ = priorityWaitingResidualWorkBeforeTag (front ++ [tag]) tag := by
      symm
      exact priorityWaitingResidualWorkBeforeTag_append_self_of_not_mem front tag hnot
    _ = priorityWaitingResidualWorkBeforeTag ((front ++ [tag]) ++ tail) tag := by
      symm
      exact priorityWaitingResidualWorkBeforeTag_append_list_of_mem
        (front ++ [tag]) tail tag hmem
    _ = priorityWaitingResidualWorkBeforeTag (front ++ tag :: tail) tag := by
      congr 1
      simp [List.append_assoc]

/-- The strict-arrival work ledger depends on a tag only through its priority
class, not through its identifier, arrival epoch, or own service work. -/
theorem nonpreemptivePriorityTaggedStrictArrivalWork_eq_of_priority_eq
    {n : ℕ} {JobId : Type*}
    (first second : NonpreemptivePriorityJob n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (hpriority : first.priority = second.priority) :
    nonpreemptivePriorityTaggedStrictArrivalWork first jobs =
      nonpreemptivePriorityTaggedStrictArrivalWork second jobs := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      simp only [nonpreemptivePriorityTaggedStrictArrivalWork]
      rw [hpriority, ih]

/-- Replacing the declared service work of a tag that is still waiting leaves
the finite pre-service ledger unchanged.  The state may contain arbitrary
other jobs; the hypotheses isolate the tag's FIFO occurrence and exclude it
from the active server. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_waiting_setServiceWork_eq
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (serviceWork : ℝ)
    (hactive : ¬ ∃ residual, state.active = some (tag, residual))
    (hactive' : ¬ ∃ residual, state.active = some
      (nonpreemptivePriorityJobSetServiceWork serviceWork tag, residual))
    (hfront : ∀ job ∈ front, job.identifier ≠ tag.identifier) :
    nonpreemptivePriorityTaggedPreServiceWork
      (nonpreemptivePriorityWorkStateWithTaggedWaiting state front tail
        (nonpreemptivePriorityJobSetServiceWork serviceWork tag))
      (nonpreemptivePriorityJobSetServiceWork serviceWork tag) =
    nonpreemptivePriorityTaggedPreServiceWork
      (nonpreemptivePriorityWorkStateWithTaggedWaiting state front tail tag)
      tag := by
  classical
  let tag' := nonpreemptivePriorityJobSetServiceWork serviceWork tag
  let old : NonpreemptivePriorityWorkState n JobId :=
    nonpreemptivePriorityWorkStateWithTaggedWaiting state front tail tag
  let new : NonpreemptivePriorityWorkState n JobId :=
    nonpreemptivePriorityWorkStateWithTaggedWaiting state front tail tag'
  have hnewActive : ¬ ∃ residual, new.active = some (tag', residual) := by
    simpa [new] using hactive'
  have holdActive : ¬ ∃ residual, old.active = some (tag, residual) := by
    simpa [old] using hactive
  have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent new tag'.priority =
      priorityWaitingResidualWorkStrictlyMoreUrgent old tag.priority := by
    unfold priorityWaitingResidualWorkStrictlyMoreUrgent
    apply Finset.sum_congr rfl
    intro priority hpriority
    have hne : priority ≠ tag.priority :=
      ne_of_lt (Finset.mem_filter.mp hpriority).2
    have hne' : priority ≠ tag'.priority := by
      simpa [tag'] using hne
    simp [new, old, tag', nonpreemptivePriorityWorkStateWithTaggedWaiting,
      priorityWaitingResidualWork, Function.update_of_ne hne,
      Function.update_of_ne hne']
  have hprefix : priorityWaitingResidualWorkBeforeTag (new.waiting tag'.priority) tag' =
      priorityWaitingResidualWorkBeforeTag (old.waiting tag.priority) tag := by
    simpa [new, old, tag', nonpreemptivePriorityWorkStateWithTaggedWaiting] using
      (priorityWaitingResidualWorkBeforeTag_append_setServiceWork_eq
        front tail tag serviceWork hfront)
  have hactiveWork : activeNonpreemptivePriorityResidualWork new =
      activeNonpreemptivePriorityResidualWork old := by
    rfl
  change nonpreemptivePriorityTaggedPreServiceWork new tag' =
    nonpreemptivePriorityTaggedPreServiceWork old tag
  unfold nonpreemptivePriorityTaggedPreServiceWork
  rw [if_neg hnewActive, if_neg holdActive, hactiveWork, hstrict, hprefix]

end

end AppliedModelingLib.Queueing
