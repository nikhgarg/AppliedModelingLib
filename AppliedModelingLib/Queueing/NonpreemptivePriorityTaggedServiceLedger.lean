import AppliedModelingLib.Queueing.NonpreemptivePriorityServiceAccounting
import AppliedModelingLib.Queueing.NonpreemptivePrioritySimultaneousArrivals
import AppliedModelingLib.Queueing.NonpreemptivePriorityTagWaiting
import AppliedModelingLib.Queueing.NonpreemptivePriorityArrivalTraceWorkload
import AppliedModelingLib.Queueing.NonpreemptivePriorityTaggedServiceInterval
import Mathlib.Data.List.TakeWhile

/-!
# Tagged service ledger for finite nonpreemptive-priority traces

This module records the deterministic work that must be served before a
distinguished FIFO customer can start service.  It is independent of a
probability law.  The stationary priority construction uses this ledger to
separate pre-arrival work from later strictly higher-priority arrivals.
-/

namespace AppliedModelingLib.Queueing

open scoped BigOperators

noncomputable section

/-- The declared service work in the FIFO prefix before the first occurrence
of a tagged job.  If the tag is absent, the whole list is returned; all uses
at a tag admission or service start supply the corresponding membership fact. -/
noncomputable def priorityWaitingResidualWorkBeforeTag
    {n : ℕ} {JobId : Type*}
    (waiting : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) : ℝ := by
  classical
  exact (waiting.takeWhile (fun job => !decide (job = tag))).map
    (fun job => job.serviceWork) |>.sum

/-- When the tagged customer is absent, the FIFO-prefix ledger is the whole
waiting workload. -/
theorem priorityWaitingResidualWorkBeforeTag_eq_waitingWork_of_not_mem
    {n : ℕ} {JobId : Type*}
    (waiting : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hnot : tag ∉ waiting) :
    priorityWaitingResidualWorkBeforeTag waiting tag =
      (waiting.map fun job => job.serviceWork).sum := by
  classical
  unfold priorityWaitingResidualWorkBeforeTag
  have htake : waiting.takeWhile (fun job => !decide (job = tag)) = waiting := by
    apply (List.takeWhile_eq_self_iff).mpr
    intro job hjob
    simp [ne_of_mem_of_not_mem hjob hnot]
  rw [htake]

/-- Appending a fresh tagged customer to a FIFO list leaves exactly the old
waiting work ahead of that customer. -/
theorem priorityWaitingResidualWorkBeforeTag_append_self_of_not_mem
    {n : ℕ} {JobId : Type*}
    (waiting : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
  (hnot : tag ∉ waiting) :
    priorityWaitingResidualWorkBeforeTag (waiting ++ [tag]) tag =
      (waiting.map fun job => job.serviceWork).sum := by
  classical
  unfold priorityWaitingResidualWorkBeforeTag
  induction waiting with
  | nil => simp
  | cons head tail ih =>
      have hhead : head ≠ tag := by
        intro h
        apply hnot
        simp [h]
      have htail : tag ∉ tail := by
        intro h
        exact hnot (by simp [h])
      simpa [hhead, ih htail]

/-- Appending any later FIFO arrival does not change the work before a tag
already present in that FIFO list. -/
theorem priorityWaitingResidualWorkBeforeTag_append_of_mem
    {n : ℕ} {JobId : Type*}
    (waiting : List (NonpreemptivePriorityJob n JobId))
    (tag newJob : NonpreemptivePriorityJob n JobId)
    (hmem : tag ∈ waiting) :
    priorityWaitingResidualWorkBeforeTag (waiting ++ [newJob]) tag =
      priorityWaitingResidualWorkBeforeTag waiting tag := by
  classical
  unfold priorityWaitingResidualWorkBeforeTag
  induction waiting with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases hhead : head = tag
      · subst head
        simp
      · have hhead' : tag ≠ head := Ne.symm hhead
        have htail : tag ∈ tail := by
          simpa [hhead, hhead'] using hmem
        simpa [hhead] using ih htail

/-- Removing no FIFO position: a non-tagged list head contributes its full
declared work to the prefix before the tag. -/
theorem priorityWaitingResidualWorkBeforeTag_cons_of_ne
    {n : ℕ} {JobId : Type*}
    (head tag : NonpreemptivePriorityJob n JobId)
    (tail : List (NonpreemptivePriorityJob n JobId))
    (hhead : head ≠ tag) :
    priorityWaitingResidualWorkBeforeTag (head :: tail) tag =
      head.serviceWork + priorityWaitingResidualWorkBeforeTag tail tag := by
  classical
  simp [priorityWaitingResidualWorkBeforeTag, hhead]

/-- The prefix before a tagged FIFO head is empty. -/
theorem priorityWaitingResidualWorkBeforeTag_cons_self
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId)
    (tail : List (NonpreemptivePriorityJob n JobId)) :
    priorityWaitingResidualWorkBeforeTag (tag :: tail) tag = 0 := by
  classical
  simp [priorityWaitingResidualWorkBeforeTag]

/-- Waiting work in priority classes strictly more urgent than a specified
class.  Lower `Fin` indices denote higher priority. -/
def priorityWaitingResidualWorkStrictlyMoreUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j => j < i), priorityWaitingResidualWork state j

/-- The inclusive urgent waiting ledger partitions into strictly more urgent
classes and the selected class itself. -/
theorem priorityWaitingResidualWorkAtLeastAsUrgent_eq_strictlyMoreUrgent_add_self
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId) (i : Fin n) :
    priorityWaitingResidualWorkAtLeastAsUrgent state i =
      priorityWaitingResidualWorkStrictlyMoreUrgent state i +
        priorityWaitingResidualWork state i := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j => j ≤ i)
  have hi : i ∈ s := by simp [s]
  have herase : s.erase i = Finset.univ.filter (fun j => j < i) := by
    ext j
    simp [s, lt_iff_le_and_ne, and_comm]
  unfold priorityWaitingResidualWorkAtLeastAsUrgent
    priorityWaitingResidualWorkStrictlyMoreUrgent
  change (∑ j ∈ s, priorityWaitingResidualWork state j) = _
  rw [← Finset.sum_erase_add _ _ hi, herase]

/-- The work that must still be served before a tagged job can start.  While
the tag is waiting, this is the active residual, all strictly more urgent
waiting work, and the same-class FIFO prefix before the tag.  It is zero once
the tag is active. -/
noncomputable def nonpreemptivePriorityTaggedPreServiceWork
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) : ℝ := by
  classical
  exact if ∃ residual, state.active = some (tag, residual) then 0 else
    activeNonpreemptivePriorityResidualWork state +
      priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority +
        priorityWaitingResidualWorkBeforeTag (state.waiting tag.priority) tag

/-- The tagged pre-service ledger vanishes at the instant the tag is active. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_eq_zero_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (tag, residual)) :
    nonpreemptivePriorityTaggedPreServiceWork state tag = 0 := by
  unfold nonpreemptivePriorityTaggedPreServiceWork
  simp [hactive]

/-- During a service interval of a non-tagged job, the pre-service ledger
decreases at unit rate.  This is a deterministic clock identity; admissible
finite traces separately ensure that the displayed residual stays
nonnegative. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_timeUpdate_of_active_ne_tag
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag activeJob : NonpreemptivePriorityJob n JobId)
    (residual target : ℝ)
    (hactive : state.active = some (activeJob, residual))
    (hactiveNe : activeJob ≠ tag) :
    nonpreemptivePriorityTaggedPreServiceWork
        { state with
          currentTime := target
          active := some (activeJob, residual - (target - state.currentTime)) } tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag -
        (target - state.currentTime) := by
  classical
  have hnotActive : ¬ ∃ r, state.active = some (tag, r) := by
    rintro ⟨r, htag⟩
    have hpairs : (activeJob, residual) = (tag, r) :=
      Option.some.inj (hactive.symm.trans htag)
    exact hactiveNe (congrArg Prod.fst hpairs)
  have hnotActiveUpdated : ¬ ∃ r,
      ({ state with
          currentTime := target
          active := some (activeJob, residual - (target - state.currentTime)) } :
        NonpreemptivePriorityWorkState n JobId).active = some (tag, r) := by
    rintro ⟨r, htag⟩
    have hpairs :
        (activeJob, residual - (target - state.currentTime)) = (tag, r) := by
      simpa using htag
    exact hactiveNe (congrArg Prod.fst hpairs)
  have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent
      { state with
        currentTime := target
        active := some (activeJob, residual - (target - state.currentTime)) } tag.priority =
      priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority := by
    unfold priorityWaitingResidualWorkStrictlyMoreUrgent
    apply Finset.sum_congr rfl
    intro j _
    rfl
  unfold nonpreemptivePriorityTaggedPreServiceWork
  rw [if_neg hnotActiveUpdated, if_neg hnotActive, hstrict]
  simp only [activeNonpreemptivePriorityResidualWork, hactive]
  ring

/-- On an arrival-free interval that does not reach the active customer's
completion, the recursive finite-trace evolution realizes the unit-rate
tagged-ledger decrease directly. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_advance_partial_of_active_ne_tag
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag activeJob : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (htarget : ¬ target ≤ state.currentTime)
    (hactive : state.active = some (activeJob, residual))
    (hcomplete : ¬ residual ≤ target - state.currentTime)
    (hactiveNe : activeJob ≠ tag) :
    nonpreemptivePriorityTaggedPreServiceWork
        (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag -
        (target - state.currentTime) := by
  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
    (nonpreemptivePriorityTaggedPreServiceWork_timeUpdate_of_active_ne_tag
      state tag activeJob residual target hactive hactiveNe)

/-- Service dispatch only removes FIFO positions, so a job still waiting after
dispatch was already waiting in the same class before dispatch. -/
theorem mem_waiting_startNextNonpreemptivePriorityJob_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hmem : job ∈ (startNextNonpreemptivePriorityJob state).waiting i) :
    job ∈ state.waiting i := by
  classical
  cases hactive : state.active with
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hactive] using hmem
  | none =>
      by_cases hwaiting : hasPriorityWaitingJob state
      · let selected := nextPriorityWaitingClass state hwaiting
        cases hlist : state.waiting selected with
        | nil =>
            simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
              selected, hlist] using hmem
        | cons head tail =>
            by_cases hi : i = selected
            · subst i
              have htail : job ∈ tail := by
                simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                  selected, hlist] using hmem
              rw [hlist]
              exact List.mem_cons_of_mem head htail
            · have hwaitingEq :
                (startNextNonpreemptivePriorityJob state).waiting i = state.waiting i := by
                  simp [startNextNonpreemptivePriorityJob, hactive, hwaiting,
                    selected, hlist, Function.update_of_ne hi]
              rwa [hwaitingEq] at hmem
      · simpa [startNextNonpreemptivePriorityJob, hactive, hwaiting] using hmem

/-- Completing the active service and dispatching its replacement never adds
FIFO entries.  Thus every post-completion waiting entry was already waiting
in its class just before the completion. -/
theorem mem_waiting_completeNonpreemptivePriorityWorkJob_reverse
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hmem : job ∈ (completeNonpreemptivePriorityWorkJob state).waiting i) :
    job ∈ state.waiting i := by
  classical
  cases hactive : state.active with
  | none =>
      simpa [completeNonpreemptivePriorityWorkJob, hactive] using hmem
  | some active =>
      let post : NonpreemptivePriorityWorkState n JobId :=
        { state with
          active := none
          completed := (active.1, state.currentTime) :: state.completed }
      have hcomplete : completeNonpreemptivePriorityWorkJob state =
          startNextNonpreemptivePriorityJob post := by
        simp [completeNonpreemptivePriorityWorkJob, post, hactive]
      rw [hcomplete] at hmem
      have hpost := mem_waiting_startNextNonpreemptivePriorityJob_reverse post job i hmem
      simpa [post] using hpost

/-- Arrival-free finite service evolution cannot create a FIFO entry.  This
reverse form permits a tagged-waiting invariant at a later horizon to be used
at each preceding completion in a trace induction. -/
theorem mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hmem : job ∈ (advanceNonpreemptivePriorityWorkState fuel target state).waiting i) :
    job ∈ state.waiting i := by
  induction fuel generalizing state with
  | zero =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hmem
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hmem
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hmem
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hmem
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hmem
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hafter : job ∈
                  (advanceNonpreemptivePriorityWorkState fuel target
                    (completeNonpreemptivePriorityWorkJob completedAt)).waiting i := by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete, completedAt] using hmem
              have hcompleted := ih
                (completeNonpreemptivePriorityWorkJob completedAt) hafter
              have hbefore := mem_waiting_completeNonpreemptivePriorityWorkJob_reverse
                completedAt job i hcompleted
              simpa [completedAt] using hbefore
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
              hcomplete] using hmem

/-- A tail admission of a distinct job cannot create an occurrence of an
existing FIFO record. -/
theorem mem_waiting_enqueueNonpreemptivePriorityJob_reverse_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hnew : newJob ≠ job)
    (hmem : job ∈ (enqueueNonpreemptivePriorityJob state newJob).waiting i) :
    job ∈ state.waiting i := by
  classical
  by_cases hi : i = newJob.priority
  · subst i
    rw [enqueueNonpreemptivePriorityJob_waiting_selected] at hmem
    rcases List.mem_append.mp hmem with hmem | hnewMem
    · exact hmem
    · have heq : job = newJob := by simpa using hnewMem
      exact (hnew heq.symm).elim
  · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state newJob i hi] at hmem
    exact hmem

/-- A distinct later admission cannot create an existing waiting record: it
either leaves the FIFO list unchanged or appends behind it after dispatch. -/
theorem mem_waiting_admitNonpreemptivePriorityJob_reverse_of_ne
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (newJob job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hnew : newJob ≠ job)
    (hmem : job ∈ (admitNonpreemptivePriorityJob state newJob).waiting i) :
    job ∈ state.waiting i := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  cases hactive : prepared.active with
  | none =>
      have hpreparedMem : job ∈ prepared.waiting i := by
        simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hmem
      exact mem_waiting_startNextNonpreemptivePriorityJob_reverse
        state job i (by simpa [prepared] using hpreparedMem)
  | some active =>
      have hadmit : admitNonpreemptivePriorityJob state newJob =
          enqueueNonpreemptivePriorityJob prepared newJob := by
        simp [admitNonpreemptivePriorityJob, prepared, hactive]
      have hpreparedMem : job ∈ prepared.waiting i := by
        rw [hadmit] at hmem
        exact mem_waiting_enqueueNonpreemptivePriorityJob_reverse_of_ne
          prepared newJob job i hnew hmem
      exact mem_waiting_startNextNonpreemptivePriorityJob_reverse
        state job i (by simpa [prepared] using hpreparedMem)

/-- If an idle queue has no strictly more urgent waiting job and the tag is
at the head of its class FIFO, the next dispatch starts the tag at its full
declared service work. -/
theorem startNextNonpreemptivePriorityJob_active_tag_of_no_strictlyMoreUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (tail : List (NonpreemptivePriorityJob n JobId))
    (hactive : state.active = none)
    (hhead : state.waiting tag.priority = tag :: tail)
    (hstrict : ∀ j, j < tag.priority → state.waiting j = []) :
    (startNextNonpreemptivePriorityJob state).active = some (tag, tag.serviceWork) := by
  classical
  have hwaiting : hasPriorityWaitingJob state := by
    refine ⟨tag.priority, ?_⟩
    rw [hhead]
    simp
  let selected := nextPriorityWaitingClass state hwaiting
  have hselectedLe : selected ≤ tag.priority := by
    exact nextPriorityWaitingClass_le_of_waiting state hwaiting tag.priority (by
      rw [hhead]
      simp)
  have htagLe : tag.priority ≤ selected := by
    by_contra hnot
    have hlt : selected < tag.priority := lt_of_not_ge hnot
    have hempty : state.waiting selected = [] := hstrict selected hlt
    have hpositive : 0 < (state.waiting selected).length := by
      simpa [selected, nextPriorityWaitingClass] using
        nextNonpreemptivePriority_positive (fun j => (state.waiting j).length) hwaiting
    simp [hempty] at hpositive
  have hselected : selected = tag.priority := le_antisymm hselectedLe htagLe
  simp [startNextNonpreemptivePriorityJob, hactive, hwaiting, selected, hselected, hhead]

/-- Immediately after a fresh tagged admission, the tagged pre-service ledger
is exactly the active residual and inclusive urgent waiting work present just
before the admission.  Work conservation rules out a malformed idle state
with an unstarted FIFO backlog. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_admit_self_of_fresh
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hfresh : ¬ nonpreemptivePriorityWorkStateContainsJob state tag)
    (hwork : nonpreemptivePriorityWorkConserving state) :
    nonpreemptivePriorityTaggedPreServiceWork
        (admitNonpreemptivePriorityJob state tag) tag =
      activeNonpreemptivePriorityResidualWork state +
        priorityWaitingResidualWorkAtLeastAsUrgent state tag.priority := by
  classical
  cases hactive : state.active with
  | none =>
      have hnoWaiting : ¬ hasPriorityWaitingJob state := hwork hactive
      have hwaiting : ∀ j, state.waiting j = [] := by
        intro j
        by_contra hnot
        apply hnoWaiting
        refine ⟨j, ?_⟩
        exact List.length_pos_of_ne_nil hnot
      have hadmit : (admitNonpreemptivePriorityJob state tag).active =
          some (tag, tag.serviceWork) := by
        simp [admitNonpreemptivePriorityJob, startNextNonpreemptivePriorityJob,
          hactive, hnoWaiting]
      unfold nonpreemptivePriorityTaggedPreServiceWork
      simp [hadmit, activeNonpreemptivePriorityResidualWork, hactive,
        priorityWaitingResidualWorkAtLeastAsUrgent, priorityWaitingResidualWork,
        hwaiting]
  | some active =>
      have hactiveNeTag : active.1 ≠ tag := by
        intro htag
        apply hfresh
        left
        refine ⟨active.2, ?_⟩
        rw [hactive]
        congr 1
        exact Prod.ext htag rfl
      have hnotWaiting : tag ∉ state.waiting tag.priority := by
        intro htag
        apply hfresh
        exact Or.inr (Or.inl ⟨tag.priority, htag⟩)
      have hbusy : state.active ≠ none := by simp [hactive]
      rw [admitNonpreemptivePriorityJob_eq_enqueue_of_active state tag hbusy]
      have htagNotActive : ¬ ∃ residual,
          (enqueueNonpreemptivePriorityJob state tag).active = some (tag, residual) := by
        intro htag
        rcases htag with ⟨residual, htag⟩
        have hpair : active = (tag, residual) := by
          exact Option.some.inj (by simpa [enqueueNonpreemptivePriorityJob, hactive] using htag)
        exact hactiveNeTag (congrArg Prod.fst hpair)
      have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent
          (enqueueNonpreemptivePriorityJob state tag) tag.priority =
          priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority := by
        unfold priorityWaitingResidualWorkStrictlyMoreUrgent
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ tag.priority := ne_of_lt (Finset.mem_filter.mp hj).2
        exact priorityWaitingResidualWork_enqueue_of_ne state tag j hji
      have hprefix : priorityWaitingResidualWorkBeforeTag
          ((enqueueNonpreemptivePriorityJob state tag).waiting tag.priority) tag =
          priorityWaitingResidualWork state tag.priority := by
        rw [enqueueNonpreemptivePriorityJob_waiting_selected]
        exact priorityWaitingResidualWorkBeforeTag_append_self_of_not_mem
          (state.waiting tag.priority) tag hnotWaiting
      have hactiveEnqueue : (enqueueNonpreemptivePriorityJob state tag).active = some active := by
        simpa [enqueueNonpreemptivePriorityJob, hactive] using hactive
      unfold nonpreemptivePriorityTaggedPreServiceWork
      rw [if_neg htagNotActive, hstrict, hprefix]
      rw [priorityWaitingResidualWorkAtLeastAsUrgent_eq_strictlyMoreUrgent_add_self]
      unfold activeNonpreemptivePriorityResidualWork
      rw [hactiveEnqueue]
      simp only [hactive]
      ring

/-- A strictly more urgent tail arrival adds exactly its declared work to the
tagged pre-service ledger, provided the tag has not yet started service. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_enqueue_of_strictlyMoreUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag newJob : NonpreemptivePriorityJob n JobId)
    (hnotActive : ¬ ∃ residual, state.active = some (tag, residual))
    (hpriority : newJob.priority < tag.priority) :
    nonpreemptivePriorityTaggedPreServiceWork
        (enqueueNonpreemptivePriorityJob state newJob) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag + newJob.serviceWork := by
  classical
  have hnotActiveEnqueue : ¬ ∃ residual,
      (enqueueNonpreemptivePriorityJob state newJob).active = some (tag, residual) := by
    rintro ⟨residual, hactive⟩
    apply hnotActive
    refine ⟨residual, ?_⟩
    simpa [enqueueNonpreemptivePriorityJob] using hactive
  have hactive : activeNonpreemptivePriorityResidualWork
      (enqueueNonpreemptivePriorityJob state newJob) =
      activeNonpreemptivePriorityResidualWork state := by
    rfl
  have hwaiting : (enqueueNonpreemptivePriorityJob state newJob).waiting tag.priority =
      state.waiting tag.priority := by
    exact enqueueNonpreemptivePriorityJob_waiting_of_ne state newJob tag.priority
      (Ne.symm (ne_of_lt hpriority))
  have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent
      (enqueueNonpreemptivePriorityJob state newJob) tag.priority =
      priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority + newJob.serviceWork := by
    let s : Finset (Fin n) := Finset.univ.filter (fun j => j < tag.priority)
    have hmem : newJob.priority ∈ s := by
      simp [s, hpriority]
    have hsum := Finset.sum_erase_add s
      (fun j => priorityWaitingResidualWork
        (enqueueNonpreemptivePriorityJob state newJob) j) hmem
    have hsumState := Finset.sum_erase_add s
      (fun j => priorityWaitingResidualWork state j) hmem
    unfold priorityWaitingResidualWorkStrictlyMoreUrgent
    change (∑ j ∈ s, priorityWaitingResidualWork
      (enqueueNonpreemptivePriorityJob state newJob) j) = _
    calc
      (∑ j ∈ s, priorityWaitingResidualWork
          (enqueueNonpreemptivePriorityJob state newJob) j) =
          (∑ j ∈ s.erase newJob.priority, priorityWaitingResidualWork
            (enqueueNonpreemptivePriorityJob state newJob) j) +
            priorityWaitingResidualWork
              (enqueueNonpreemptivePriorityJob state newJob) newJob.priority := by
            rw [Finset.sum_erase_add _ _ hmem]
      _ = (∑ j ∈ s.erase newJob.priority, priorityWaitingResidualWork state j) +
            (priorityWaitingResidualWork state newJob.priority + newJob.serviceWork) := by
            congr 1
            · apply Finset.sum_congr rfl
              intro j hj
              exact priorityWaitingResidualWork_enqueue_of_ne state newJob j
                (Finset.mem_erase.mp hj).1
            · exact priorityWaitingResidualWork_enqueue_selected state newJob
      _ = (∑ j ∈ s, priorityWaitingResidualWork state j) + newJob.serviceWork := by
            rw [← hsumState]
            ring
  unfold nonpreemptivePriorityTaggedPreServiceWork
  rw [if_neg hnotActiveEnqueue, if_neg hnotActive, hactive, hstrict, hwaiting]
  ring

/-- A later arrival that is not strictly more urgent than a waiting tag does
not change that tag's pre-service ledger.  The same-class case is exactly the
FIFO fact that tail admission stays behind the existing tag. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_enqueue_of_not_strictlyMoreUrgent
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag newJob : NonpreemptivePriorityJob n JobId)
    (hnotActive : ¬ ∃ residual, state.active = some (tag, residual))
    (htagWaiting : tag ∈ state.waiting tag.priority)
    (hpriority : ¬ newJob.priority < tag.priority) :
    nonpreemptivePriorityTaggedPreServiceWork
        (enqueueNonpreemptivePriorityJob state newJob) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag := by
  classical
  have hnotActiveEnqueue : ¬ ∃ residual,
      (enqueueNonpreemptivePriorityJob state newJob).active = some (tag, residual) := by
    rintro ⟨residual, hactive⟩
    apply hnotActive
    refine ⟨residual, ?_⟩
    simpa [enqueueNonpreemptivePriorityJob] using hactive
  have hactive : activeNonpreemptivePriorityResidualWork
      (enqueueNonpreemptivePriorityJob state newJob) =
      activeNonpreemptivePriorityResidualWork state := by
    rfl
  have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent
      (enqueueNonpreemptivePriorityJob state newJob) tag.priority =
      priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority := by
    unfold priorityWaitingResidualWorkStrictlyMoreUrgent
    apply Finset.sum_congr rfl
    intro j hj
    apply priorityWaitingResidualWork_enqueue_of_ne state newJob j
    intro hji
    apply hpriority
    rw [← hji]
    exact (Finset.mem_filter.mp hj).2
  have hprefix : priorityWaitingResidualWorkBeforeTag
      ((enqueueNonpreemptivePriorityJob state newJob).waiting tag.priority) tag =
      priorityWaitingResidualWorkBeforeTag (state.waiting tag.priority) tag := by
    by_cases hsame : newJob.priority = tag.priority
    · calc
        priorityWaitingResidualWorkBeforeTag
            ((enqueueNonpreemptivePriorityJob state newJob).waiting tag.priority) tag =
            priorityWaitingResidualWorkBeforeTag
              ((enqueueNonpreemptivePriorityJob state newJob).waiting newJob.priority) tag := by
                rw [hsame]
        _ = priorityWaitingResidualWorkBeforeTag
              (state.waiting newJob.priority ++ [newJob]) tag := by
                rw [enqueueNonpreemptivePriorityJob_waiting_selected]
        _ = priorityWaitingResidualWorkBeforeTag
              (state.waiting tag.priority) tag := by
                rw [hsame]
                exact priorityWaitingResidualWorkBeforeTag_append_of_mem
                  (state.waiting tag.priority) tag newJob htagWaiting
    · rw [enqueueNonpreemptivePriorityJob_waiting_of_ne state newJob tag.priority
        (Ne.symm hsame)]
  unfold nonpreemptivePriorityTaggedPreServiceWork
  rw [if_neg hnotActiveEnqueue, if_neg hnotActive, hactive, hstrict, hprefix]

/-- Completing a non-tagged active job subtracts exactly its residual work
from the tagged pre-service ledger.  The proof separates a higher-priority
dispatch, an earlier same-class FIFO dispatch, and dispatch of the tag. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_complete_of_active_ne_tag
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (tag activeJob : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hactive : state.active = some (activeJob, residual))
    (hactiveNe : activeJob ≠ tag)
    (htagWaiting : tag ∈ state.waiting tag.priority)
    (hclass : hasClassConsistentWaiting state) :
    nonpreemptivePriorityTaggedPreServiceWork
        (completeNonpreemptivePriorityWorkJob state) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag - residual := by
  classical
  let post : NonpreemptivePriorityWorkState n JobId :=
    { state with
      active := none
      completed := (activeJob, state.currentTime) :: state.completed }
  have hcomplete : completeNonpreemptivePriorityWorkJob state =
      startNextNonpreemptivePriorityJob post := by
    simp [completeNonpreemptivePriorityWorkJob, post, hactive]
  have hafterActive : post.active = none := rfl
  have hafterWaiting : post.waiting = state.waiting := rfl
  have hwaiting : hasPriorityWaitingJob post := by
    refine ⟨tag.priority, ?_⟩
    rw [hafterWaiting]
    exact List.length_pos_of_mem htagWaiting
  let selected := nextPriorityWaitingClass post hwaiting
  have hselectedLe : selected ≤ tag.priority := by
    exact nextPriorityWaitingClass_le_of_waiting post hwaiting tag.priority (by
      rw [hafterWaiting]
      exact List.length_pos_of_mem htagWaiting)
  have hnotActive : ¬ ∃ r, state.active = some (tag, r) := by
    rintro ⟨r, htag⟩
    have hpairs : (activeJob, residual) = (tag, r) :=
      Option.some.inj (hactive.symm.trans htag)
    exact hactiveNe (congrArg Prod.fst hpairs)
  rcases hselectedLe.lt_or_eq with hselectedLt | hselectedEq
  · have hselectedNe : selected ≠ tag.priority := ne_of_lt hselectedLt
    cases hlist : state.waiting selected with
    | nil =>
        have hpositive : 0 < (post.waiting selected).length := by
          simpa [selected, nextPriorityWaitingClass] using
            nextNonpreemptivePriority_positive (fun j => (post.waiting j).length) hwaiting
        simp [hafterWaiting, hlist] at hpositive
    | cons head tail =>
        let next : NonpreemptivePriorityWorkState n JobId :=
          { post with
            active := some (head, head.serviceWork)
            waiting := Function.update post.waiting selected tail }
        have hstart : startNextNonpreemptivePriorityJob post = next := by
          simp [startNextNonpreemptivePriorityJob, post, hwaiting, selected, hlist, next]
        have hheadMem : head ∈ state.waiting selected := by simp [hlist]
        have hheadPriority : head.priority = selected := hclass selected head hheadMem
        have hheadNe : head ≠ tag := by
          intro hhead
          have hpriority : tag.priority = selected := by
            simpa [hhead] using hheadPriority
          exact hselectedNe hpriority.symm
        have hnotActiveNext : ¬ ∃ r, next.active = some (tag, r) := by
          rintro ⟨r, htag⟩
          have hpairs : (head, head.serviceWork) = (tag, r) := by
            simpa [next] using htag
          exact hheadNe (congrArg Prod.fst hpairs)
        have hprefix : priorityWaitingResidualWorkBeforeTag
            (next.waiting tag.priority) tag =
            priorityWaitingResidualWorkBeforeTag (state.waiting tag.priority) tag := by
          have hwait : next.waiting tag.priority = state.waiting tag.priority := by
            simp [next, post, Function.update_of_ne (Ne.symm hselectedNe)]
          rw [hwait]
        have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent next tag.priority =
            priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority - head.serviceWork := by
          let s : Finset (Fin n) := Finset.univ.filter (fun j => j < tag.priority)
          have hmem : selected ∈ s := by simp [s, hselectedLt]
          have hsum := Finset.sum_erase_add s
            (fun j => priorityWaitingResidualWork state j) hmem
          unfold priorityWaitingResidualWorkStrictlyMoreUrgent
          change (∑ j ∈ s, priorityWaitingResidualWork next j) = _
          calc
            (∑ j ∈ s, priorityWaitingResidualWork next j) =
                (∑ j ∈ s.erase selected, priorityWaitingResidualWork next j) +
                  priorityWaitingResidualWork next selected := by
                    rw [Finset.sum_erase_add _ _ hmem]
            _ = (∑ j ∈ s.erase selected, priorityWaitingResidualWork state j) +
                  (priorityWaitingResidualWork state selected - head.serviceWork) := by
                    congr 1
                    · apply Finset.sum_congr rfl
                      intro j hj
                      unfold priorityWaitingResidualWork
                      simp [next, post,
                        Function.update_of_ne (Finset.mem_erase.mp hj).1]
                    · unfold priorityWaitingResidualWork
                      simp [next, post, hlist]
            _ = (∑ j ∈ s, priorityWaitingResidualWork state j) - head.serviceWork := by
                    rw [← hsum]
                    ring
        rw [hcomplete, hstart]
        unfold nonpreemptivePriorityTaggedPreServiceWork
        rw [if_neg hnotActiveNext, if_neg hnotActive, hstrict, hprefix]
        simp only [activeNonpreemptivePriorityResidualWork, next, hactive]
        ring
  · cases hlist : state.waiting tag.priority with
    | nil => simp [hlist] at htagWaiting
    | cons head tail =>
        have hlistSelected : state.waiting selected = head :: tail := by
          simpa [hselectedEq] using hlist
        let next : NonpreemptivePriorityWorkState n JobId :=
          { post with
            active := some (head, head.serviceWork)
            waiting := Function.update post.waiting selected tail }
        have hpostList :
            post.waiting (nextPriorityWaitingClass post hwaiting) = head :: tail := by
          change post.waiting selected = head :: tail
          exact hlistSelected
        have hstart : startNextNonpreemptivePriorityJob post = next := by
          unfold startNextNonpreemptivePriorityJob
          simp only [hafterActive]
          rw [dif_pos hwaiting, hpostList]
        subst selected
        by_cases hhead : head = tag
        · subst head
          have hstrictZero : priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority = 0 := by
            unfold priorityWaitingResidualWorkStrictlyMoreUrgent
            apply Finset.sum_eq_zero
            intro j hj
            have hjlt : j < tag.priority := (Finset.mem_filter.mp hj).2
            have hwaitNil : state.waiting j = [] := by
              by_contra hnot
              have hpositive : 0 < (post.waiting j).length := by
                rw [hafterWaiting]
                exact List.length_pos_of_ne_nil hnot
              have hle := nextPriorityWaitingClass_le_of_waiting post hwaiting j hpositive
              rw [hselectedEq] at hle
              exact (not_le_of_gt hjlt) hle
            simp [priorityWaitingResidualWork, hwaitNil]
          have hprefixZero : priorityWaitingResidualWorkBeforeTag
              (state.waiting tag.priority) tag = 0 := by
            rw [hlist]
            exact priorityWaitingResidualWorkBeforeTag_cons_self tag tail
          have hnextActive : next.active = some (tag, tag.serviceWork) := by
            simp [next]
          rw [hcomplete, hstart]
          rw [nonpreemptivePriorityTaggedPreServiceWork_eq_zero_of_active
            next tag tag.serviceWork hnextActive]
          unfold nonpreemptivePriorityTaggedPreServiceWork
          rw [if_neg hnotActive, hstrictZero, hprefixZero]
          simp only [activeNonpreemptivePriorityResidualWork, hactive]
          ring
        · have htagTail : tag ∈ tail := by
            have : tag = head ∨ tag ∈ tail := by simpa [hlist] using htagWaiting
            exact this.resolve_left (Ne.symm hhead)
          have hnotActiveNext : ¬ ∃ r, next.active = some (tag, r) := by
            rintro ⟨r, htag⟩
            have hpairs : (head, head.serviceWork) = (tag, r) := by
              simpa [next] using htag
            exact hhead (congrArg Prod.fst hpairs)
          have hstrict : priorityWaitingResidualWorkStrictlyMoreUrgent next tag.priority =
              priorityWaitingResidualWorkStrictlyMoreUrgent state tag.priority := by
            unfold priorityWaitingResidualWorkStrictlyMoreUrgent
            apply Finset.sum_congr rfl
            intro j hj
            unfold priorityWaitingResidualWork
            have hjne : j ≠ tag.priority := ne_of_lt (Finset.mem_filter.mp hj).2
            have hselector : nextPriorityWaitingClass post hwaiting = tag.priority :=
              hselectedEq
            have hjneSelected : j ≠ nextPriorityWaitingClass post hwaiting := by
              rw [hselector]
              exact hjne
            have hnextWaiting : next.waiting j = state.waiting j := by
              unfold next
              dsimp only
              rw [Function.update_of_ne hjneSelected]
            rw [hnextWaiting]
          have hprefix : priorityWaitingResidualWorkBeforeTag
              (next.waiting tag.priority) tag =
              priorityWaitingResidualWorkBeforeTag (state.waiting tag.priority) tag -
                head.serviceWork := by
            have hselector : nextPriorityWaitingClass post hwaiting = tag.priority :=
              hselectedEq
            have hnextWaiting : next.waiting tag.priority = tail := by
              unfold next
              dsimp only
              rw [hselector, Function.update_self]
            have htailPrefix : priorityWaitingResidualWorkBeforeTag tail tag =
                priorityWaitingResidualWorkBeforeTag (state.waiting tag.priority) tag -
                  head.serviceWork := by
              rw [hlist, priorityWaitingResidualWorkBeforeTag_cons_of_ne head tag tail hhead]
              ring
            rw [hnextWaiting]
            exact htailPrefix
          rw [hcomplete, hstart]
          unfold nonpreemptivePriorityTaggedPreServiceWork
          rw [if_neg hnotActiveNext, if_neg hnotActive, hstrict, hprefix]
          simp only [activeNonpreemptivePriorityResidualWork, next, hactive]
          ring

/-- Until a unique tagged job starts service, an arrival-free finite evolution
uses exactly the tagged pre-service ledger at unit rate.  The hypotheses rule
out both malformed idle FIFO states and duplicated tags; the endpoint
membership is the literal assertion that the tag has not yet started. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_advance_eq_sub_of_waiting
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hclass : hasClassConsistentWaiting state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hwaiting : tag ∈
      (advanceNonpreemptivePriorityWorkState fuel target state).waiting tag.priority) :
    nonpreemptivePriorityTaggedPreServiceWork
        (advanceNonpreemptivePriorityWorkState fuel target state) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag -
        (target - state.currentTime) := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨hactive, hwaitingNil⟩
      have hno : tag ∉
          (advanceNonpreemptivePriorityWorkState 0 target state).waiting tag.priority := by
        unfold advanceNonpreemptivePriorityWorkState
        split <;> simp [hactive, hwaitingNil]
      exact (hno hwaiting).elim
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have heq : target = state.currentTime := le_antisymm htarget hcurrent
        subst target
        simp [advanceNonpreemptivePriorityWorkState]
      · cases hactive : state.active with
        | none =>
            have hwaitingState : tag ∈ state.waiting tag.priority :=
              mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
                (fuel + 1) target state tag tag.priority hwaiting
            exact (hwork hactive ⟨tag.priority,
              List.length_pos_of_mem hwaitingState⟩).elim
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hstepCurrent :
                  (completeNonpreemptivePriorityWorkJob completedAt).currentTime ≤ target := by
                rw [completeNonpreemptivePriorityWorkJob_currentTime]
                dsimp [completedAt]
                linarith
              have hstepFuel :
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
              have hclassAt : hasClassConsistentWaiting completedAt := by
                simpa [completedAt] using hclass
              have hclassStep : hasClassConsistentWaiting
                  (completeNonpreemptivePriorityWorkJob completedAt) :=
                hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
                  completedAt hclassAt
              have hworkAt : nonpreemptivePriorityWorkConserving completedAt := by
                simpa [completedAt] using hwork
              have hworkStep : nonpreemptivePriorityWorkConserving
                  (completeNonpreemptivePriorityWorkJob completedAt) :=
                nonpreemptivePriorityWorkConserving_complete completedAt hworkAt
              have hmultAt :
                  nonpreemptivePriorityWorkStateJobMultiplicity completedAt tag ≤ 1 := by
                simpa [completedAt] using hmultiplicity
              have hmultStep : nonpreemptivePriorityWorkStateJobMultiplicity
                  (completeNonpreemptivePriorityWorkJob completedAt) tag ≤ 1 := by
                rw [nonpreemptivePriorityWorkStateJobMultiplicity_complete]
                exact hmultAt
              have hwaitingStep : tag ∈
                  (advanceNonpreemptivePriorityWorkState fuel target
                    (completeNonpreemptivePriorityWorkJob completedAt)).waiting tag.priority := by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete, completedAt] using hwaiting
              have hwaitingCompleted : tag ∈
                  (completeNonpreemptivePriorityWorkJob completedAt).waiting tag.priority :=
                mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
                  fuel target (completeNonpreemptivePriorityWorkJob completedAt)
                  tag tag.priority hwaitingStep
              have hwaitingAt : tag ∈ completedAt.waiting tag.priority :=
                mem_waiting_completeNonpreemptivePriorityWorkJob_reverse
                  completedAt tag tag.priority hwaitingCompleted
              have hactiveAt : completedAt.active = some active := by
                simp [completedAt, hactive]
              have hactiveNe : active.1 ≠ tag := by
                intro heq
                apply (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
                  completedAt tag tag.priority hwaitingAt hmultAt).1
                refine ⟨active.2, ?_⟩
                rw [hactiveAt]
                congr 1
                exact Prod.ext heq rfl
              have hledgerComplete :
                  nonpreemptivePriorityTaggedPreServiceWork
                      (completeNonpreemptivePriorityWorkJob completedAt) tag =
                    nonpreemptivePriorityTaggedPreServiceWork completedAt tag - active.2 := by
                exact nonpreemptivePriorityTaggedPreServiceWork_complete_of_active_ne_tag
                  completedAt tag active.1 active.2 hactiveAt hactiveNe hwaitingAt hclassAt
              have hind := ih (completeNonpreemptivePriorityWorkJob completedAt)
                hstepCurrent hclassStep hworkStep hmultStep hstepFuel hwaitingStep
              have htimeLedger :
                  nonpreemptivePriorityTaggedPreServiceWork completedAt tag =
                    nonpreemptivePriorityTaggedPreServiceWork state tag := by
                rfl
              calc
                nonpreemptivePriorityTaggedPreServiceWork
                    (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) tag =
                    nonpreemptivePriorityTaggedPreServiceWork
                      (advanceNonpreemptivePriorityWorkState fuel target
                        (completeNonpreemptivePriorityWorkJob completedAt)) tag := by
                          simp [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                            hcomplete, completedAt]
                _ = nonpreemptivePriorityTaggedPreServiceWork
                      (completeNonpreemptivePriorityWorkJob completedAt) tag -
                    (target - (completeNonpreemptivePriorityWorkJob completedAt).currentTime) := hind
                _ = (nonpreemptivePriorityTaggedPreServiceWork completedAt tag - active.2) -
                    (target - (completeNonpreemptivePriorityWorkJob completedAt).currentTime) := by
                      rw [hledgerComplete]
                _ = nonpreemptivePriorityTaggedPreServiceWork state tag -
                    (target - state.currentTime) := by
                      rw [htimeLedger, completeNonpreemptivePriorityWorkJob_currentTime]
                      dsimp [completedAt]
                      ring
            · have hwaitingState : tag ∈ state.waiting tag.priority :=
                mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
                  (fuel + 1) target state tag tag.priority hwaiting
              have hactiveNe : active.1 ≠ tag := by
                intro heq
                apply (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
                  state tag tag.priority hwaitingState hmultiplicity).1
                refine ⟨active.2, ?_⟩
                rw [hactive]
                congr 1
                exact Prod.ext heq rfl
              exact nonpreemptivePriorityTaggedPreServiceWork_advance_partial_of_active_ne_tag
                fuel target state tag active.1 active.2 htarget hactive hcomplete hactiveNe

/-- One chronological arrival step preserves the tagged work accounting: time
uses service capacity at unit rate, and only a strictly more urgent arrival
adds new work before the still-waiting tag. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_advanceThenAdmit_of_waiting
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag newJob : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ newJob.arrivalTime)
    (hclass : hasClassConsistentWaiting state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hnew : newJob ≠ tag)
    (hwaiting : tag ∈
      (advanceThenAdmitNonpreemptivePriorityJob fuel state newJob).waiting tag.priority) :
    nonpreemptivePriorityTaggedPreServiceWork
        (advanceThenAdmitNonpreemptivePriorityJob fuel state newJob) tag =
      nonpreemptivePriorityTaggedPreServiceWork state tag -
        (newJob.arrivalTime - state.currentTime) +
          if newJob.priority < tag.priority then newJob.serviceWork else 0 := by
  let advanced := advanceNonpreemptivePriorityWorkState fuel newJob.arrivalTime state
  have hwaitingAdvanced : tag ∈ advanced.waiting tag.priority := by
    apply mem_waiting_admitNonpreemptivePriorityJob_reverse_of_ne
      advanced newJob tag tag.priority hnew
    simpa [advanceThenAdmitNonpreemptivePriorityJob, advanced] using hwaiting
  have hadvance := nonpreemptivePriorityTaggedPreServiceWork_advance_eq_sub_of_waiting
    fuel newJob.arrivalTime state tag hcurrent hclass hwork hmultiplicity hfuel
      hwaitingAdvanced
  have hworkAdvanced : nonpreemptivePriorityWorkConserving advanced := by
    simpa [advanced] using
      nonpreemptivePriorityWorkConserving_advance fuel newJob.arrivalTime state hwork
  have hbusy : advanced.active ≠ none := by
    intro hnone
    exact hworkAdvanced hnone ⟨tag.priority,
      List.length_pos_of_mem hwaitingAdvanced⟩
  have hadmit : admitNonpreemptivePriorityJob advanced newJob =
      enqueueNonpreemptivePriorityJob advanced newJob := by
    exact admitNonpreemptivePriorityJob_eq_enqueue_of_active advanced newJob hbusy
  have hmultAdvanced :
      nonpreemptivePriorityWorkStateJobMultiplicity advanced tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity advanced tag =
        nonpreemptivePriorityWorkStateJobMultiplicity state tag by
      exact nonpreemptivePriorityWorkStateJobMultiplicity_advance
        fuel newJob.arrivalTime state tag]
    exact hmultiplicity
  have hnotActive : ¬ ∃ residual, advanced.active = some (tag, residual) :=
    (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
      advanced tag tag.priority hwaitingAdvanced hmultAdvanced).1
  change nonpreemptivePriorityTaggedPreServiceWork
      (admitNonpreemptivePriorityJob advanced newJob) tag = _
  by_cases hpriority : newJob.priority < tag.priority
  · rw [if_pos hpriority, hadmit,
      nonpreemptivePriorityTaggedPreServiceWork_enqueue_of_strictlyMoreUrgent
        advanced tag newJob hnotActive hpriority,
      hadvance]
  · rw [if_neg hpriority, hadmit,
      nonpreemptivePriorityTaggedPreServiceWork_enqueue_of_not_strictlyMoreUrgent
        advanced tag newJob hnotActive hwaitingAdvanced hpriority,
      hadvance]
    ring

/-- If a positive-work tag is already active and a sufficiently fuelled
arrival-free evolution still has that tag active with its *full* declared
residual, then no physical time has elapsed.  A nonpreemptive service
schedule either decreases an active residual or records the tag's completion;
the latter is incompatible with the unique live tag at the endpoint. -/
theorem target_eq_currentTime_of_advance_active_tag_full
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId) (residual : ℝ)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hactive : state.active = some (tag, residual))
    (hfinal :
      (advanceNonpreemptivePriorityWorkState fuel target state).active =
        some (tag, tag.serviceWork)) :
    target = state.currentTime := by
  cases fuel with
  | zero =>
      simp [totalNonpreemptivePriorityWorkJobs, hactive] at hfuel
  | succ fuel =>
      let completionTime := state.currentTime + residual
      have hresidualPos : 0 < residual := hpositive.1 (tag, residual) hactive
      have hschedule : nonpreemptivePriorityTaggedServiceSchedule tag completionTime state := by
        exact nonpreemptivePriorityTaggedServiceSchedule_of_active state tag residual
          hactive hresidualPos
      have hscheduled := nonpreemptivePriorityTaggedServiceSchedule_advance_succ
        fuel target completionTime state tag hschedule
      have hfinalMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity
              (advanceNonpreemptivePriorityWorkState (fuel + 1) target state) tag ≤ 1 := by
        rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance]
        exact hmultiplicity
      have hfinalTime :
          (advanceNonpreemptivePriorityWorkState (fuel + 1) target state).currentTime = target :=
        advanceNonpreemptivePriorityWorkState_currentTime_eq_target
          (fuel + 1) target state hcurrent hfuel
      rcases hscheduled with hcompleted | ⟨_, hscheduledActive⟩
      · have htooMany := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_completed
            (advanceNonpreemptivePriorityWorkState (fuel + 1) target state)
            tag tag.serviceWork completionTime hfinal hcompleted
        linarith
      · have hresidualEq : completionTime - target = tag.serviceWork := by
          rw [hfinalTime] at hscheduledActive
          have hpairs : (tag, completionTime - target) = (tag, tag.serviceWork) := by
            exact Option.some.inj (hscheduledActive.symm.trans hfinal)
          exact congrArg Prod.snd hpairs
        have hresidualLe : residual ≤ tag.serviceWork := hbound residual hactive
        dsimp [completionTime] at hresidualEq
        linarith

/-- The physical endpoint of a finite arrival list is strictly before a bound
when the initial time and every listed arrival epoch are strictly before that
bound. -/
theorem nonpreemptivePriorityArrivalTraceEndTime_lt
    {n : ℕ} {JobId : Type*}
    (time bound : ℝ) (jobs : List (NonpreemptivePriorityJob n JobId))
    (htime : time < bound)
    (hjobs : ∀ job ∈ jobs, job.arrivalTime < bound) :
    nonpreemptivePriorityArrivalTraceEndTime time jobs < bound := by
  induction jobs generalizing time with
  | nil => simpa [nonpreemptivePriorityArrivalTraceEndTime] using htime
  | cons job jobs ih =>
      simpa [nonpreemptivePriorityArrivalTraceEndTime] using
        ih job.arrivalTime (hjobs job (by simp))
          (fun other hother => hjobs other (by simp [hother]))

/-- A chronological finite trace likewise finishes strictly before such a
bound. -/
theorem runNonpreemptivePriorityArrivalTrace_currentTime_lt
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) (bound : ℝ)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hinitial : initial.currentTime < bound)
    (hjobs : ∀ job ∈ jobs, job.arrivalTime < bound) :
    (runNonpreemptivePriorityArrivalTrace initial jobs).currentTime < bound := by
  rw [runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime
    initial jobs hstart hsorted]
  exact nonpreemptivePriorityArrivalTraceEndTime_lt
    initial.currentTime bound jobs hinitial hjobs

/-- If a sufficiently fuelled future advance starts the tag at a strictly
later time with its full residual, the unique tag must have been waiting in
its own FIFO class immediately before that advance. -/
theorem mem_waiting_of_advance_active_tag_full_of_lt
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hlt : state.currentTime < target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hclass : hasClassConsistentWaiting state)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hfinal :
      (advanceNonpreemptivePriorityWorkState fuel target state).active =
        some (tag, tag.serviceWork)) :
    tag ∈ state.waiting tag.priority := by
  have hcontains : nonpreemptivePriorityWorkStateContainsJob state tag := by
    apply nonpreemptivePriorityWorkStateContainsJob_advance_reverse fuel target state tag
    exact Or.inl ⟨tag.serviceWork, hfinal⟩
  rcases hcontains with hactive | hwaiting | hcompleted
  · rcases hactive with ⟨residual, hactive⟩
    have htime := target_eq_currentTime_of_advance_active_tag_full
      fuel target state tag residual hcurrent hpositive hbound hmultiplicity hfuel
        hactive hfinal
    linarith
  · rcases hwaiting with ⟨priority, hwaiting⟩
    have hpriority : tag.priority = priority := hclass priority tag hwaiting
    rwa [hpriority]
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    have hcompletedFinal : (tag, completedAt) ∈
        (advanceNonpreemptivePriorityWorkState fuel target state).completed :=
      mem_completed_advanceNonpreemptivePriorityWorkState
        fuel target state tag completedAt hcompleted
    have htooMany := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_completed
      (advanceNonpreemptivePriorityWorkState fuel target state)
      tag tag.serviceWork completedAt hfinal hcompletedFinal
    have hfinalMultiplicity :
        nonpreemptivePriorityWorkStateJobMultiplicity
            (advanceNonpreemptivePriorityWorkState fuel target state) tag ≤ 1 := by
      rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance]
      exact hmultiplicity
    linarith

/-- If a unique positive-work tag is waiting initially and the finite
arrival-free evolution first reaches that tag in active service with its full
residual at the target time, the initial tagged pre-service ledger is exactly
the elapsed service time.  This is the deterministic service-start endpoint
form of the tagged ledger. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_eq_elapsed_of_advance_active_tag_full
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ) (state : NonpreemptivePriorityWorkState n JobId)
    (tag : NonpreemptivePriorityJob n JobId)
    (hcurrent : state.currentTime ≤ target)
    (hpositive : positiveNonpreemptivePriorityResidualWork state)
    (hclass : hasClassConsistentWaiting state)
    (hwork : nonpreemptivePriorityWorkConserving state)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag state)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state tag ≤ 1)
    (hfuel : totalNonpreemptivePriorityWorkJobs state ≤ fuel)
    (hwaiting : tag ∈ state.waiting tag.priority)
    (hfinal :
      (advanceNonpreemptivePriorityWorkState fuel target state).active =
        some (tag, tag.serviceWork)) :
    nonpreemptivePriorityTaggedPreServiceWork state tag =
      target - state.currentTime := by
  induction fuel generalizing state with
  | zero =>
      have hcount : totalNonpreemptivePriorityWorkJobs state = 0 :=
        Nat.eq_zero_of_le_zero hfuel
      rcases active_eq_none_and_waiting_eq_nil_of_totalNonpreemptivePriorityWorkJobs_eq_zero
        state hcount with ⟨_, hwaitingNil⟩
      have hfalse : False := by
        have : tag ∈ ([] : List (NonpreemptivePriorityJob n JobId)) := by
          simpa [hwaitingNil] using hwaiting
        simpa using this
      exact hfalse.elim
  | succ fuel ih =>
      classical
      by_cases htarget : target ≤ state.currentTime
      · have htime : target = state.currentTime := le_antisymm htarget hcurrent
        have hactiveTag : state.active = some (tag, tag.serviceWork) := by
          simpa [advanceNonpreemptivePriorityWorkState, htarget] using hfinal
        exact ((not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
          state tag tag.priority hwaiting hmultiplicity).1
            ⟨tag.serviceWork, hactiveTag⟩).elim
      · cases hactive : state.active with
        | none =>
            exact (hwork hactive ⟨tag.priority,
              List.length_pos_of_mem hwaiting⟩).elim
        | some active =>
            have hactiveNe : active.1 ≠ tag := by
              intro heq
              apply (not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
                state tag tag.priority hwaiting hmultiplicity).1
              refine ⟨active.2, ?_⟩
              rw [hactive]
              congr 1
              exact Prod.ext heq rfl
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let completedAt : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              let next : NonpreemptivePriorityWorkState n JobId :=
                completeNonpreemptivePriorityWorkJob completedAt
              have hnextCurrent : next.currentTime ≤ target := by
                rw [show next.currentTime = completedAt.currentTime by
                  simpa [next] using completeNonpreemptivePriorityWorkJob_currentTime completedAt]
                dsimp [completedAt]
                linarith
              have hnextFuel : totalNonpreemptivePriorityWorkJobs next ≤ fuel := by
                have hcompletionCount : totalNonpreemptivePriorityWorkJobs next + 1 =
                    totalNonpreemptivePriorityWorkJobs completedAt := by
                  apply totalNonpreemptivePriorityWorkJobs_complete_of_active completedAt active
                  simp [completedAt, hactive, next]
                have htimeCount : totalNonpreemptivePriorityWorkJobs completedAt =
                    totalNonpreemptivePriorityWorkJobs state := by rfl
                omega
              have hpositiveAt : positiveNonpreemptivePriorityResidualWork completedAt := by
                simpa [completedAt] using hpositive
              have hpositiveNext : positiveNonpreemptivePriorityResidualWork next := by
                simpa [next] using
                  positiveNonpreemptivePriorityResidualWork_complete completedAt hpositiveAt
              have hclassAt : hasClassConsistentWaiting completedAt := by
                simpa [completedAt] using hclass
              have hclassNext : hasClassConsistentWaiting next := by
                simpa [next] using
                  hasClassConsistentWaiting_completeNonpreemptivePriorityWorkJob
                    completedAt hclassAt
              have hworkAt : nonpreemptivePriorityWorkConserving completedAt := by
                simpa [completedAt] using hwork
              have hworkNext : nonpreemptivePriorityWorkConserving next := by
                simpa [next] using nonpreemptivePriorityWorkConserving_complete completedAt hworkAt
              have hboundAt : nonpreemptivePriorityTaggedResidualLeService tag completedAt := by
                simpa [completedAt] using hbound
              have hboundNext : nonpreemptivePriorityTaggedResidualLeService tag next := by
                simpa [next] using
                  nonpreemptivePriorityTaggedResidualLeService_complete completedAt tag hboundAt
              have hmultAt :
                  nonpreemptivePriorityWorkStateJobMultiplicity completedAt tag ≤ 1 := by
                simpa [completedAt] using hmultiplicity
              have hmultNext : nonpreemptivePriorityWorkStateJobMultiplicity next tag ≤ 1 := by
                rw [show nonpreemptivePriorityWorkStateJobMultiplicity next tag =
                    nonpreemptivePriorityWorkStateJobMultiplicity completedAt tag by
                  simpa [next] using
                    nonpreemptivePriorityWorkStateJobMultiplicity_complete completedAt tag]
                exact hmultAt
              have hfinalNext :
                  (advanceNonpreemptivePriorityWorkState fuel target next).active =
                    some (tag, tag.serviceWork) := by
                simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                  hcomplete, completedAt, next] using hfinal
              have hcontainsNext : nonpreemptivePriorityWorkStateContainsJob next tag := by
                apply nonpreemptivePriorityWorkStateContainsJob_advance_reverse
                  fuel target next tag
                exact Or.inl ⟨tag.serviceWork, hfinalNext⟩
              have hwaitingAt : tag ∈ completedAt.waiting tag.priority := by
                simpa [completedAt] using hwaiting
              have hledgerComplete :
                  nonpreemptivePriorityTaggedPreServiceWork next tag =
                    nonpreemptivePriorityTaggedPreServiceWork state tag - active.2 := by
                exact nonpreemptivePriorityTaggedPreServiceWork_complete_of_active_ne_tag
                  completedAt tag active.1 active.2
                  (by simp [completedAt, hactive]) hactiveNe hwaitingAt hclassAt
              rcases hcontainsNext with hactiveNext | hwaitingNext | hcompletedNext
              · rcases hactiveNext with ⟨residual, hactiveNext⟩
                have htime := target_eq_currentTime_of_advance_active_tag_full
                  fuel target next tag residual hnextCurrent hpositiveNext hboundNext
                  hmultNext hnextFuel hactiveNext hfinalNext
                have hzero : nonpreemptivePriorityTaggedPreServiceWork next tag = 0 :=
                  nonpreemptivePriorityTaggedPreServiceWork_eq_zero_of_active
                    next tag residual hactiveNext
                have hnextTime : next.currentTime = state.currentTime + active.2 := by
                  simpa [next, completedAt] using
                    completeNonpreemptivePriorityWorkJob_currentTime completedAt
                linarith
              · rcases hwaitingNext with ⟨priority, hwaitingNext⟩
                have hpriority : tag.priority = priority :=
                  hclassNext priority tag hwaitingNext
                have hwaitingTag : tag ∈ next.waiting tag.priority := by
                  rwa [hpriority]
                have hind := ih next hnextCurrent hpositiveNext hclassNext hworkNext
                  hboundNext hmultNext hnextFuel hwaitingTag hfinalNext
                have hnextTime : next.currentTime = state.currentTime + active.2 := by
                  simpa [next, completedAt] using
                    completeNonpreemptivePriorityWorkJob_currentTime completedAt
                linarith
              · rcases hcompletedNext with ⟨completedAtTag, hcompletedNext⟩
                have hcompletedFinal : (tag, completedAtTag) ∈
                    (advanceNonpreemptivePriorityWorkState fuel target next).completed :=
                  mem_completed_advanceNonpreemptivePriorityWorkState
                    fuel target next tag completedAtTag hcompletedNext
                have htooMany := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_completed
                  (advanceNonpreemptivePriorityWorkState fuel target next)
                  tag tag.serviceWork completedAtTag hfinalNext hcompletedFinal
                linarith [show nonpreemptivePriorityWorkStateJobMultiplicity
                  (advanceNonpreemptivePriorityWorkState fuel target next) tag ≤ 1 by
                    rw [nonpreemptivePriorityWorkStateJobMultiplicity_advance]
                    exact hmultNext]
            · have hpairs : (active.1,
                  active.2 - (target - state.currentTime)) = (tag, tag.serviceWork) := by
                exact Option.some.inj (by
                  simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete]
                    using hfinal)
              exact (hactiveNe (congrArg Prod.fst hpairs)).elim

/-- The accumulated work of trace arrivals that have strictly higher priority
than the tag.  This deterministic list functional is the finite-trace
counterpart of the later higher-priority arrival term in a tagged workload
balance. -/
noncomputable def nonpreemptivePriorityTaggedStrictArrivalWork
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId) :
    List (NonpreemptivePriorityJob n JobId) → ℝ
  | [] => 0
  | job :: jobs =>
      (if job.priority < tag.priority then job.serviceWork else 0) +
        nonpreemptivePriorityTaggedStrictArrivalWork tag jobs

/-- The recursive strict-arrival ledger is the sum of its pointwise
higher-priority work contributions. -/
theorem nonpreemptivePriorityTaggedStrictArrivalWork_eq_sum_map
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    nonpreemptivePriorityTaggedStrictArrivalWork tag jobs =
      (jobs.map fun job => if job.priority < tag.priority then job.serviceWork else 0).sum := by
  induction jobs with
  | nil => rfl
  | cons job jobs ih =>
      simp [nonpreemptivePriorityTaggedStrictArrivalWork, ih]

/-- Appending arrivals that are not strictly more urgent than a tag leaves
its strict-arrival work ledger unchanged. -/
theorem nonpreemptivePriorityTaggedStrictArrivalWork_append_of_forall_not_lt
    {n : ℕ} {JobId : Type*}
    (tag : NonpreemptivePriorityJob n JobId)
    (front tail : List (NonpreemptivePriorityJob n JobId))
    (htail : ∀ job ∈ tail, ¬ job.priority < tag.priority) :
    nonpreemptivePriorityTaggedStrictArrivalWork tag (front ++ tail) =
      nonpreemptivePriorityTaggedStrictArrivalWork tag front := by
  have htailZero : nonpreemptivePriorityTaggedStrictArrivalWork tag tail = 0 := by
    induction tail with
    | nil => rfl
    | cons job tail ih =>
        rw [nonpreemptivePriorityTaggedStrictArrivalWork]
        rw [if_neg (htail job (by simp))]
        rw [ih (fun other hother => htail other (by simp [hother]))]
        ring
  induction front with
  | nil => simpa using htailZero
  | cons job front ih =>
      simp only [List.cons_append, nonpreemptivePriorityTaggedStrictArrivalWork]
      rw [ih]

/-- If every presented job differs from the tag, a tag that is waiting after a
finite arrival trace was already waiting before that trace. -/
theorem mem_waiting_runNonpreemptivePriorityArrivalTrace_reverse_of_forall_ne
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hnew : ∀ job ∈ jobs, job ≠ tag)
    (hwaiting : tag ∈
      (runNonpreemptivePriorityArrivalTrace initial jobs).waiting i) :
    tag ∈ initial.waiting i := by
  induction jobs generalizing initial with
  | nil =>
      simpa [runNonpreemptivePriorityArrivalTrace] using hwaiting
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hwaitingAdmitted : tag ∈ admitted.waiting i := by
        simpa [runNonpreemptivePriorityArrivalTrace, advanced, admitted,
          advanceThenAdmitNonpreemptivePriorityJob] using
          ih admitted (fun other hother => hnew other (by simp [hother])) hwaiting
      have hwaitingAdvanced : tag ∈ advanced.waiting i := by
        apply mem_waiting_admitNonpreemptivePriorityJob_reverse_of_ne
          advanced job tag i (hnew job (by simp))
        simpa [admitted] using hwaitingAdmitted
      exact mem_waiting_advanceNonpreemptivePriorityWorkState_reverse
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial tag i
        (by simpa [advanced] using hwaitingAdvanced)

/-- Along a chronologically supplied finite trace, the tagged pre-service
ledger equals its initial value minus elapsed service capacity plus exactly
the work of the trace arrivals strictly more urgent than the tag, provided the
tag is still waiting at the terminal state. -/
theorem nonpreemptivePriorityTaggedPreServiceWork_run_eq_sub_add_of_waiting
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (tag : NonpreemptivePriorityJob n JobId)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hclass : hasClassConsistentWaiting initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial tag ≤ 1)
    (hnew : ∀ job ∈ jobs, job ≠ tag)
    (hwaiting : tag ∈
      (runNonpreemptivePriorityArrivalTrace initial jobs).waiting tag.priority) :
    nonpreemptivePriorityTaggedPreServiceWork
        (runNonpreemptivePriorityArrivalTrace initial jobs) tag =
      nonpreemptivePriorityTaggedPreServiceWork initial tag -
        (nonpreemptivePriorityArrivalTraceEndTime initial.currentTime jobs -
          initial.currentTime) +
        nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := by
  induction jobs generalizing initial with
  | nil =>
      simp [runNonpreemptivePriorityArrivalTrace,
        nonpreemptivePriorityArrivalTraceEndTime,
        nonpreemptivePriorityTaggedStrictArrivalWork]
  | cons job jobs ih =>
      rcases List.pairwise_cons.mp hsorted with ⟨hhead, htail⟩
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced job
      have hrun : runNonpreemptivePriorityArrivalTrace initial (job :: jobs) =
          runNonpreemptivePriorityArrivalTrace admitted jobs := by
        simp [runNonpreemptivePriorityArrivalTrace, advanced, admitted,
          advanceThenAdmitNonpreemptivePriorityJob]
      have hwaitingTail : tag ∈
          (runNonpreemptivePriorityArrivalTrace admitted jobs).waiting tag.priority := by
        simpa [hrun] using hwaiting
      have hwaitingAdmitted : tag ∈ admitted.waiting tag.priority := by
        exact mem_waiting_runNonpreemptivePriorityArrivalTrace_reverse_of_forall_ne
          admitted jobs tag tag.priority
          (fun other hother => hnew other (by simp [hother])) hwaitingTail
      have hstep := nonpreemptivePriorityTaggedPreServiceWork_advanceThenAdmit_of_waiting
        (totalNonpreemptivePriorityWorkJobs initial) initial tag job
        (hstart job (by simp)) hclass hwork hmultiplicity le_rfl
        (hnew job (by simp)) (by
          simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using
            hwaitingAdmitted)
      have hadmittedTime : admitted.currentTime = job.arrivalTime := by
        simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using
          advanceThenAdmitNonpreemptivePriorityJob_currentTime_eq_arrivalTime
            (totalNonpreemptivePriorityWorkJobs initial) initial job
            (hstart job (by simp)) le_rfl
      have hadvancedClass : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hclass
      have hadmittedClass : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob advanced job hadvancedClass
      have hadvancedWork : nonpreemptivePriorityWorkConserving advanced := by
        simpa [advanced] using nonpreemptivePriorityWorkConserving_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial hwork
      have hadmittedWork : nonpreemptivePriorityWorkConserving admitted := by
        simpa [admitted] using nonpreemptivePriorityWorkConserving_admit advanced job
      have hadvancedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity advanced tag ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity advanced tag =
            nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
          simpa [advanced] using nonpreemptivePriorityWorkStateJobMultiplicity_advance
            (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial tag]
        exact hmultiplicity
      have hadmittedMultiplicity :
          nonpreemptivePriorityWorkStateJobMultiplicity admitted tag ≤ 1 := by
        rw [show nonpreemptivePriorityWorkStateJobMultiplicity admitted tag =
            nonpreemptivePriorityWorkStateJobMultiplicity advanced tag by
          simpa [admitted] using nonpreemptivePriorityWorkStateJobMultiplicity_admit_of_ne
            advanced job tag (hnew job (by simp))]
        exact hadvancedMultiplicity
      have hadmittedStart : ∀ other ∈ jobs, admitted.currentTime ≤ other.arrivalTime := by
        intro other hother
        rw [hadmittedTime]
        exact hhead other hother
      have hrec := ih admitted hadmittedStart htail hadmittedClass hadmittedWork
        hadmittedMultiplicity (fun other hother => hnew other (by simp [hother]))
          hwaitingTail
      calc
        nonpreemptivePriorityTaggedPreServiceWork
            (runNonpreemptivePriorityArrivalTrace initial (job :: jobs)) tag =
            nonpreemptivePriorityTaggedPreServiceWork
              (runNonpreemptivePriorityArrivalTrace admitted jobs) tag := by rw [hrun]
        _ = nonpreemptivePriorityTaggedPreServiceWork admitted tag -
              (nonpreemptivePriorityArrivalTraceEndTime admitted.currentTime jobs -
                admitted.currentTime) +
              nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := hrec
        _ = (nonpreemptivePriorityTaggedPreServiceWork initial tag -
              (job.arrivalTime - initial.currentTime) +
                if job.priority < tag.priority then job.serviceWork else 0) -
              (nonpreemptivePriorityArrivalTraceEndTime job.arrivalTime jobs -
                job.arrivalTime) +
              nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := by
                rw [hadmittedTime]
                simpa [admitted, advanced, advanceThenAdmitNonpreemptivePriorityJob] using hstep
        _ = nonpreemptivePriorityTaggedPreServiceWork initial tag -
              (nonpreemptivePriorityArrivalTraceEndTime initial.currentTime (job :: jobs) -
                initial.currentTime) +
              nonpreemptivePriorityTaggedStrictArrivalWork tag (job :: jobs) := by
                simp only [nonpreemptivePriorityArrivalTraceEndTime,
                  nonpreemptivePriorityTaggedStrictArrivalWork]
                ring

/-- A finite chronological trace reaches the tagged customer's service start
at exactly its initial pre-service work plus the work of the trace arrivals
that strictly overtake the tag.  The terminal hypothesis says that the final
arrival-free advance has just dispatched the tag with its full residual. -/
theorem nonpreemptivePriorityServiceStart_elapsed_eq_taggedPreServiceWork_add_strictArrivalWork
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (target : ℝ) (tag : NonpreemptivePriorityJob n JobId)
    (hstart : ∀ job ∈ jobs, initial.currentTime ≤ job.arrivalTime)
    (hsorted : jobs.Pairwise (fun job other => job.arrivalTime ≤ other.arrivalTime))
    (hpositive : positiveNonpreemptivePriorityResidualWork initial)
    (hpositiveJobs : ∀ job ∈ jobs, 0 < job.serviceWork)
    (hclass : hasClassConsistentWaiting initial)
    (hwork : nonpreemptivePriorityWorkConserving initial)
    (hbound : nonpreemptivePriorityTaggedResidualLeService tag initial)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity initial tag ≤ 1)
    (hnew : ∀ job ∈ jobs, job ≠ tag)
    (hwaiting : tag ∈
      (runNonpreemptivePriorityArrivalTrace initial jobs).waiting tag.priority)
    (htarget :
      (runNonpreemptivePriorityArrivalTrace initial jobs).currentTime ≤ target)
    (hterminal :
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs
          (runNonpreemptivePriorityArrivalTrace initial jobs)) target
        (runNonpreemptivePriorityArrivalTrace initial jobs)).active =
          some (tag, tag.serviceWork)) :
    target - initial.currentTime =
      nonpreemptivePriorityTaggedPreServiceWork initial tag +
        nonpreemptivePriorityTaggedStrictArrivalWork tag jobs := by
  let afterArrivals := runNonpreemptivePriorityArrivalTrace initial jobs
  have hpositiveAfter : positiveNonpreemptivePriorityResidualWork afterArrivals := by
    simpa [afterArrivals] using
      positiveNonpreemptivePriorityResidualWork_run initial jobs hpositive hpositiveJobs
  have hclassAfter : hasClassConsistentWaiting afterArrivals := by
    simpa [afterArrivals] using
      hasClassConsistentWaiting_runNonpreemptivePriorityArrivalTrace initial jobs hclass
  have hworkAfter : nonpreemptivePriorityWorkConserving afterArrivals := by
    simpa [afterArrivals] using nonpreemptivePriorityWorkConserving_run initial jobs hwork
  have hboundAfter : nonpreemptivePriorityTaggedResidualLeService tag afterArrivals := by
    simpa [afterArrivals] using
      nonpreemptivePriorityTaggedResidualLeService_run_of_forall_ne
        initial jobs tag hbound hnew
  have hmultAfter : nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag ≤ 1 := by
    rw [show nonpreemptivePriorityWorkStateJobMultiplicity afterArrivals tag =
        nonpreemptivePriorityWorkStateJobMultiplicity initial tag by
      simpa [afterArrivals] using
        nonpreemptivePriorityWorkStateJobMultiplicity_run_of_forall_ne
          initial jobs tag hnew]
    exact hmultiplicity
  have hwaitingAfter : tag ∈ afterArrivals.waiting tag.priority := by
    simpa [afterArrivals] using hwaiting
  have htargetAfter : afterArrivals.currentTime ≤ target := by
    simpa [afterArrivals] using htarget
  have hterminalAfter :
      (advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs afterArrivals) target afterArrivals).active =
          some (tag, tag.serviceWork) := by
    simpa [afterArrivals] using hterminal
  have hendpoint := nonpreemptivePriorityTaggedPreServiceWork_eq_elapsed_of_advance_active_tag_full
    (totalNonpreemptivePriorityWorkJobs afterArrivals) target afterArrivals tag
    htargetAfter hpositiveAfter hclassAfter hworkAfter hboundAfter hmultAfter le_rfl
      hwaitingAfter hterminalAfter
  have htrace := nonpreemptivePriorityTaggedPreServiceWork_run_eq_sub_add_of_waiting
    initial jobs tag hstart hsorted hclass hwork hmultiplicity hnew hwaiting
  have hendTime : afterArrivals.currentTime =
      nonpreemptivePriorityArrivalTraceEndTime initial.currentTime jobs := by
    simpa [afterArrivals] using
      runNonpreemptivePriorityArrivalTrace_currentTime_eq_endTime initial jobs hstart hsorted
  rw [hendTime] at hendpoint
  linarith

end

end AppliedModelingLib.Queueing
