import AppliedModelingLib.Queueing.NonpreemptivePriorityCompletionLedger

/-!
# FIFO order for finite nonpreemptive-priority traces

This module isolates the deterministic within-class ordering invariant of the
finite nonpreemptive-priority queue.  A later stationary tagged-arrival proof
can use it to distinguish work already ahead of a tagged job from later
same-class arrivals, which are appended behind it and therefore cannot delay
its service start.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- `earlier` precedes `later` in their common class's FIFO list. -/
def nonpreemptivePriorityFifoPrecedes
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) : Prop :=
  earlier.priority = later.priority ∧
    ∃ front middle suffix,
      state.waiting later.priority = front ++ earlier :: middle ++ later :: suffix

/-- A job already waiting in a class is before a newly appended job of that
class. -/
theorem nonpreemptivePriorityFifoPrecedes_of_mem_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hpriority : earlier.priority = later.priority)
    (hwaiting : earlier ∈ state.waiting later.priority) :
    nonpreemptivePriorityFifoPrecedes
      (enqueueNonpreemptivePriorityJob state later) earlier later := by
  classical
  rcases List.mem_iff_append.mp hwaiting with ⟨front, suffix, hsplit⟩
  refine ⟨hpriority, front, suffix, [], ?_⟩
  rw [enqueueNonpreemptivePriorityJob_waiting_selected, hsplit]

/-- Appending a new arrival at a class tail preserves every existing FIFO
precedence relation. -/
theorem nonpreemptivePriorityFifoPrecedes_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later newJob : NonpreemptivePriorityJob n JobId)
    (hprecedes : nonpreemptivePriorityFifoPrecedes state earlier later) :
    nonpreemptivePriorityFifoPrecedes
      (enqueueNonpreemptivePriorityJob state newJob) earlier later := by
  classical
  rcases hprecedes with ⟨hpriority, front, middle, suffix, hwaiting⟩
  by_cases hnew : newJob.priority = later.priority
  · refine ⟨hpriority, front, middle, suffix ++ [newJob], ?_⟩
    simp [enqueueNonpreemptivePriorityJob, hnew, hwaiting, List.append_assoc]
  · refine ⟨hpriority, front, middle, suffix, ?_⟩
    simp only [enqueueNonpreemptivePriorityJob]
    rw [Function.update_of_ne (Ne.symm hnew)]
    exact hwaiting

/-- If the server is already busy, attempting to start a next job leaves all
same-class FIFO precedence relations unchanged. -/
theorem nonpreemptivePriorityFifoPrecedes_startNext_of_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hactive : state.active ≠ none)
    (hprecedes : nonpreemptivePriorityFifoPrecedes state earlier later) :
    nonpreemptivePriorityFifoPrecedes
      (startNextNonpreemptivePriorityJob state) earlier later := by
  classical
  cases hstate : state.active with
  | none => exact (hactive hstate).elim
  | some active =>
      simpa [startNextNonpreemptivePriorityJob, hstate] using hprecedes

/-- Starting work from an idle server either preserves an existing same-class
FIFO precedence relation or starts its earlier customer.  In particular, a
later customer cannot become active before a customer that precedes it in the
same FIFO list. -/
theorem nonpreemptivePriorityFifoPrecedes_startNext_or_earlier_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hactive : state.active = none)
    (hprecedes : nonpreemptivePriorityFifoPrecedes state earlier later) :
    nonpreemptivePriorityFifoPrecedes
        (startNextNonpreemptivePriorityJob state) earlier later ∨
      ∃ residual,
        (startNextNonpreemptivePriorityJob state).active = some (earlier, residual) := by
  classical
  rcases hprecedes with ⟨hpriority, front, middle, suffix, hwaiting⟩
  have hhasWaiting : hasPriorityWaitingJob state := by
    refine ⟨later.priority, ?_⟩
    rw [hwaiting]
    simp
  let selected := nextPriorityWaitingClass state hhasWaiting
  by_cases hselected : selected = later.priority
  · have hselectedWaiting : state.waiting selected =
        front ++ earlier :: middle ++ later :: suffix := by
      simpa [hselected] using hwaiting
    cases hfront : front with
    | nil =>
        right
        refine ⟨earlier.serviceWork, ?_⟩
        simp [startNextNonpreemptivePriorityJob, hactive, hhasWaiting,
          selected, hselectedWaiting, hfront]
    | cons head front =>
        left
        refine ⟨hpriority, front, middle, suffix, ?_⟩
        have hwaiting' : state.waiting later.priority =
            head :: front ++ earlier :: middle ++ later :: suffix := by
          rw [hwaiting, hfront]
        simp [startNextNonpreemptivePriorityJob, hactive, hhasWaiting,
          selected, hselected, hwaiting', List.append_assoc]
  · left
    refine ⟨hpriority, front, middle, suffix, ?_⟩
    have hselectedNonempty : state.waiting selected ≠ [] := by
      have hpositive : 0 < (state.waiting selected).length := by
        simpa [selected, nextPriorityWaitingClass] using
          (nextNonpreemptivePriority_positive
            (fun j => (state.waiting j).length) hhasWaiting)
      exact List.ne_nil_of_length_pos hpositive
    cases hhead : state.waiting selected with
    | nil => exact (hselectedNonempty hhead).elim
    | cons head tail =>
        simp only [startNextNonpreemptivePriorityJob, hactive, dif_pos hhasWaiting,
          selected, hhead, Function.update_of_ne (Ne.symm hselected)]
        exact hwaiting

/-- The persistent disposition of a job that was initially ahead of another
job in the same FIFO list: it is still ahead, currently active, or has a
completion record. -/
def nonpreemptivePriorityFifoPrecedesDisposition
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) : Prop :=
  nonpreemptivePriorityFifoPrecedes state earlier later ∨
    (∃ residual, state.active = some (earlier, residual)) ∨
      ∃ completedAt, (earlier, completedAt) ∈ state.completed

/-- Admitting a job cannot let it pass a same-class customer that was already
waiting.  The predecessor either remains in the FIFO list or is dispatched
immediately before the new job is appended. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_admit_of_mem
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hpriority : earlier.priority = later.priority)
    (hwaiting : earlier ∈ state.waiting later.priority) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (admitNonpreemptivePriorityJob state later) earlier later := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  cases hstate : state.active with
  | some active =>
      have hprepared : prepared = state := by
        simp [prepared, startNextNonpreemptivePriorityJob, hstate]
      have hpreparedActive : prepared.active = some active := by
        rw [hprepared, hstate]
      have hprecedes : nonpreemptivePriorityFifoPrecedes
          (enqueueNonpreemptivePriorityJob prepared later) earlier later := by
        rw [hprepared]
        exact nonpreemptivePriorityFifoPrecedes_of_mem_enqueue
          state earlier later hpriority hwaiting
      exact Or.inl (by
        simpa [admitNonpreemptivePriorityJob, prepared, hpreparedActive] using hprecedes)
  | none =>
      have hhasWaiting : hasPriorityWaitingJob state := by
        exact ⟨later.priority, List.length_pos_of_mem hwaiting⟩
      let selected := nextPriorityWaitingClass state hhasWaiting
      cases hselectedWaiting : state.waiting selected with
      | nil =>
          have hpositive : 0 < (state.waiting selected).length := by
            simpa [selected, nextPriorityWaitingClass] using
              (nextNonpreemptivePriority_positive
                (fun j => (state.waiting j).length) hhasWaiting)
          exact (List.ne_nil_of_length_pos hpositive hselectedWaiting).elim
      | cons head tail =>
          have hpreparedActive : prepared.active = some (head, head.serviceWork) := by
            simp [prepared, startNextNonpreemptivePriorityJob, hstate,
              hhasWaiting, selected, hselectedWaiting]
          by_cases hselected : selected = later.priority
          · have hmember : earlier = head ∨ earlier ∈ tail := by
              rw [← hselected, hselectedWaiting] at hwaiting
              exact List.mem_cons.mp hwaiting
            rcases hmember with hearlier | htail
            · subst head
              exact Or.inr (Or.inl ⟨earlier.serviceWork, by
                simpa [admitNonpreemptivePriorityJob, prepared, hpreparedActive]⟩)
            · have hpreparedWaiting : earlier ∈ prepared.waiting later.priority := by
                rw [show later.priority = selected by exact hselected.symm]
                simp [prepared, startNextNonpreemptivePriorityJob, hstate,
                  hhasWaiting, selected, hselectedWaiting]
                exact htail
              have hprecedes := nonpreemptivePriorityFifoPrecedes_of_mem_enqueue
                prepared earlier later hpriority hpreparedWaiting
              exact Or.inl (by
                simpa [admitNonpreemptivePriorityJob, prepared, hpreparedActive] using hprecedes)
          · have hpreparedWaiting : earlier ∈ prepared.waiting later.priority := by
              simp [prepared, startNextNonpreemptivePriorityJob, hstate,
                hhasWaiting, selected, hselectedWaiting,
                Function.update_of_ne (Ne.symm hselected), hwaiting]
            have hprecedes := nonpreemptivePriorityFifoPrecedes_of_mem_enqueue
              prepared earlier later hpriority hpreparedWaiting
            exact Or.inl (by
              simpa [admitNonpreemptivePriorityJob, prepared, hpreparedActive] using hprecedes)

/-- Tail arrivals preserve the disposition of every existing FIFO
predecessor. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_enqueue
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later newJob : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (enqueueNonpreemptivePriorityJob state newJob) earlier later := by
  rcases hdisposition with hprecedes | hactive | hcompleted
  · exact Or.inl (nonpreemptivePriorityFifoPrecedes_enqueue state earlier later newJob hprecedes)
  · rcases hactive with ⟨residual, hactive⟩
    exact Or.inr (Or.inl ⟨residual, by
      simpa [enqueueNonpreemptivePriorityJob] using hactive⟩)
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    exact Or.inr (Or.inr ⟨completedAt, by
      simpa [enqueueNonpreemptivePriorityJob] using hcompleted⟩)

/-- Dispatching a next job preserves the predecessor disposition: an earlier
FIFO job either remains ahead, is the job begun by dispatch, or was already
completed. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_startNext
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (startNextNonpreemptivePriorityJob state) earlier later := by
  classical
  rcases hdisposition with hprecedes | hactive | hcompleted
  · cases hstate : state.active with
    | none =>
        rcases nonpreemptivePriorityFifoPrecedes_startNext_or_earlier_active
          state earlier later hstate hprecedes with hprecedes | hactive
        · exact Or.inl hprecedes
        · exact Or.inr (Or.inl hactive)
    | some active =>
        exact Or.inl
          (nonpreemptivePriorityFifoPrecedes_startNext_of_active state earlier later
            (by simp [hstate]) hprecedes)
  · rcases hactive with ⟨residual, hactive⟩
    exact Or.inr (Or.inl ⟨residual, by
      simpa [startNextNonpreemptivePriorityJob, hactive] using hactive⟩)
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    exact Or.inr (Or.inr ⟨completedAt,
      mem_completed_startNextNonpreemptivePriorityJob state earlier completedAt hcompleted⟩)

/-- A service completion preserves the predecessor disposition.  If the
earlier job was active, that completion explicitly enters it in the ledger. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_complete
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (completeNonpreemptivePriorityWorkJob state) earlier later := by
  classical
  rcases hdisposition with hprecedes | hactive | hcompleted
  · cases hstate : state.active with
    | none =>
        exact Or.inl (by simpa [completeNonpreemptivePriorityWorkJob, hstate] using hprecedes)
    | some active =>
        let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
          { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
        have hafter : nonpreemptivePriorityFifoPrecedes afterCompletion earlier later := by
          simpa [afterCompletion] using hprecedes
        have hnext := nonpreemptivePriorityFifoPrecedesDisposition_startNext
          afterCompletion earlier later (Or.inl hafter)
        simpa [completeNonpreemptivePriorityWorkJob, hstate, afterCompletion] using hnext
  · rcases hactive with ⟨residual, hactive⟩
    cases hstate : state.active with
    | none => simp [hstate] at hactive
    | some active =>
        have hearlier : active.1 = earlier := by
          exact congrArg Prod.fst (Option.some.inj (hstate.symm.trans hactive))
        let afterCompletion : NonpreemptivePriorityWorkState n JobId :=
          { state with active := none, completed := (active.1, state.currentTime) :: state.completed }
        have hrecorded : (earlier, state.currentTime) ∈ afterCompletion.completed := by
          simp [afterCompletion, hearlier]
        have hnext := nonpreemptivePriorityFifoPrecedesDisposition_startNext
          afterCompletion earlier later (Or.inr (Or.inr ⟨state.currentTime, hrecorded⟩))
        simpa [completeNonpreemptivePriorityWorkJob, hstate, afterCompletion] using hnext
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    exact Or.inr (Or.inr ⟨completedAt,
      mem_completed_completeNonpreemptivePriorityWorkJob state earlier completedAt hcompleted⟩)

/-- Admission preserves the disposition of an existing FIFO predecessor.  A
new job may enter service or a class tail, but it cannot erase an earlier
job's waiting, active, or completed status. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_admit
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later newJob : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (admitNonpreemptivePriorityJob state newJob) earlier later := by
  classical
  let prepared := startNextNonpreemptivePriorityJob state
  have hprepared : nonpreemptivePriorityFifoPrecedesDisposition prepared earlier later := by
    simpa [prepared] using
      nonpreemptivePriorityFifoPrecedesDisposition_startNext state earlier later hdisposition
  cases hactive : prepared.active with
  | none =>
      rcases hprepared with hprecedes | hactive' | hcompleted
      · exact Or.inl (by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hprecedes)
      · rcases hactive' with ⟨residual, hactive'⟩
        simp [hactive] at hactive'
      · rcases hcompleted with ⟨completedAt, hcompleted⟩
        exact Or.inr (Or.inr ⟨completedAt, by
          simpa [admitNonpreemptivePriorityJob, prepared, hactive] using hcompleted⟩)
  | some active =>
      simpa [admitNonpreemptivePriorityJob, prepared, hactive] using
        nonpreemptivePriorityFifoPrecedesDisposition_enqueue
          prepared earlier later newJob hprepared

/-- A same-class customer already represented by a class-consistent queue is
still before a newly admitted customer of that class: it is either waiting in
that class, currently active, or already has a completion record.  This is the
arrival-time bridge used for later customers in a literal FIFO trace. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_admit_of_contains
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting state)
    (hpriority : earlier.priority = later.priority)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob state earlier) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (admitNonpreemptivePriorityJob state later) earlier later := by
  rcases hcontains with hactive | hwaiting | hcompleted
  · exact nonpreemptivePriorityFifoPrecedesDisposition_admit state earlier later later
      (Or.inr (Or.inl hactive))
  · rcases hwaiting with ⟨waitingClass, hwaiting⟩
    have hwaitingClass : waitingClass = later.priority :=
      (hclass waitingClass earlier hwaiting).symm.trans hpriority
    rw [hwaitingClass] at hwaiting
    exact nonpreemptivePriorityFifoPrecedesDisposition_admit_of_mem
      state earlier later hpriority hwaiting
  · exact nonpreemptivePriorityFifoPrecedesDisposition_admit state earlier later later
      (Or.inr (Or.inr hcompleted))

/-- Changing only the physical clock preserves a FIFO predecessor's
disposition. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_timeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId) (time : ℝ)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      { state with currentTime := time } earlier later := by
  rcases hdisposition with hprecedes | hactive | hcompleted
  · exact Or.inl (by simpa using hprecedes)
  · rcases hactive with ⟨residual, hactive⟩
    exact Or.inr (Or.inl ⟨residual, by simpa using hactive⟩)
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    exact Or.inr (Or.inr ⟨completedAt, by simpa using hcompleted⟩)

/-- Updating the residual work of the currently active job preserves a FIFO
predecessor disposition. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_activeUpdate
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (active : NonpreemptivePriorityJob n JobId × ℝ)
    (hactive : state.active = some active)
    (time residual : ℝ)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      { state with currentTime := time, active := some (active.1, residual) } earlier later := by
  rcases hdisposition with hprecedes | hpredecessorActive | hcompleted
  · exact Or.inl (by simpa using hprecedes)
  · rcases hpredecessorActive with ⟨oldResidual, hpredecessorActive⟩
    have hearlier : active.1 = earlier := by
      exact congrArg Prod.fst (Option.some.inj (hactive.symm.trans hpredecessorActive))
    exact Or.inr (Or.inl ⟨residual, by simp [hearlier]⟩)
  · rcases hcompleted with ⟨completedAt, hcompleted⟩
    exact Or.inr (Or.inr ⟨completedAt, by simpa using hcompleted⟩)

/-- Finite service advancement preserves a FIFO predecessor's disposition. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_advance
    {n : ℕ} {JobId : Type*}
    (fuel : ℕ) (target : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId)
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition state earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (advanceNonpreemptivePriorityWorkState fuel target state) earlier later := by
  induction fuel generalizing state with
  | zero =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hdisposition
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityFifoPrecedesDisposition_timeUpdate
                state earlier later target hdisposition
        | some active =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using hdisposition
  | succ fuel ih =>
      by_cases htarget : target ≤ state.currentTime
      · simpa [advanceNonpreemptivePriorityWorkState, htarget] using hdisposition
      · cases hactive : state.active with
        | none =>
            simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive] using
              nonpreemptivePriorityFifoPrecedesDisposition_timeUpdate
                state earlier later target hdisposition
        | some active =>
            by_cases hcomplete : active.2 ≤ target - state.currentTime
            · let atCompletion : NonpreemptivePriorityWorkState n JobId :=
                { state with currentTime := state.currentTime + active.2 }
              have hatCompletion : nonpreemptivePriorityFifoPrecedesDisposition
                  atCompletion earlier later := by
                simpa [atCompletion] using
                  nonpreemptivePriorityFifoPrecedesDisposition_timeUpdate
                    state earlier later (state.currentTime + active.2) hdisposition
              have hcompleted := nonpreemptivePriorityFifoPrecedesDisposition_complete
                atCompletion earlier later hatCompletion
              simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive,
                hcomplete, atCompletion] using
                ih (completeNonpreemptivePriorityWorkJob atCompletion) hcompleted
            · simpa [advanceNonpreemptivePriorityWorkState, htarget, hactive, hcomplete] using
                nonpreemptivePriorityFifoPrecedesDisposition_activeUpdate
                  state earlier later active hactive target
                  (active.2 - (target - state.currentTime)) hdisposition

/-- A finite chronological arrival trace preserves a FIFO predecessor's
disposition through every intermediate service advancement and admission. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_run
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hdisposition : nonpreemptivePriorityFifoPrecedesDisposition initial earlier later) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (runNonpreemptivePriorityArrivalTrace initial jobs) earlier later := by
  induction jobs generalizing initial with
  | nil => simpa [runNonpreemptivePriorityArrivalTrace] using hdisposition
  | cons job jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial
      have hadvanced : nonpreemptivePriorityFifoPrecedesDisposition
          advanced earlier later := by
        simpa [advanced] using nonpreemptivePriorityFifoPrecedesDisposition_advance
          (totalNonpreemptivePriorityWorkJobs initial) job.arrivalTime initial earlier later hdisposition
      have hadmitted : nonpreemptivePriorityFifoPrecedesDisposition
          (admitNonpreemptivePriorityJob advanced job) earlier later :=
        nonpreemptivePriorityFifoPrecedesDisposition_admit
          advanced earlier later job hadvanced
      simpa [runNonpreemptivePriorityArrivalTrace,
        advanceThenAdmitNonpreemptivePriorityJob, advanced] using
        ih (admitNonpreemptivePriorityJob advanced job) hadmitted

/-- In a class-consistent finite trace, every later same-class input record
is behind a distinct customer that was already present at the trace start.
The earlier customer may already have completed when the later record arrives;
the conclusion intentionally retains that completion alternative. -/
theorem nonpreemptivePriorityFifoPrecedesDisposition_run_of_mem
    {n : ℕ} {JobId : Type*}
    (initial : NonpreemptivePriorityWorkState n JobId)
    (jobs : List (NonpreemptivePriorityJob n JobId))
    (earlier later : NonpreemptivePriorityJob n JobId)
    (hclass : hasClassConsistentWaiting initial)
    (hcontains : nonpreemptivePriorityWorkStateContainsJob initial earlier)
    (hjobs : ∀ job ∈ jobs, job ≠ earlier)
    (hlater : later ∈ jobs)
    (hpriority : earlier.priority = later.priority) :
    nonpreemptivePriorityFifoPrecedesDisposition
      (runNonpreemptivePriorityArrivalTrace initial jobs) earlier later := by
  induction jobs generalizing initial with
  | nil => simp at hlater
  | cons newJob jobs ih =>
      let advanced := advanceNonpreemptivePriorityWorkState
        (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial
      let admitted := admitNonpreemptivePriorityJob advanced newJob
      have hadvancedClass : hasClassConsistentWaiting advanced := by
        simpa [advanced] using
          hasClassConsistentWaiting_advanceNonpreemptivePriorityWorkState
            (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial hclass
      have hadvancedContains : nonpreemptivePriorityWorkStateContainsJob advanced earlier := by
        simpa [advanced] using nonpreemptivePriorityWorkStateContainsJob_advance
          (totalNonpreemptivePriorityWorkJobs initial) newJob.arrivalTime initial earlier hcontains
      have hadmittedClass : hasClassConsistentWaiting admitted := by
        simpa [admitted] using
          hasClassConsistentWaiting_admitNonpreemptivePriorityJob
            advanced newJob hadvancedClass
      have hadmittedContains : nonpreemptivePriorityWorkStateContainsJob admitted earlier := by
        simpa [admitted] using nonpreemptivePriorityWorkStateContainsJob_admit
          advanced newJob earlier hadvancedContains
      rcases List.mem_cons.mp hlater with hhead | htail
      · subst newJob
        have hadmitted :=
          nonpreemptivePriorityFifoPrecedesDisposition_admit_of_contains
            advanced earlier later hadvancedClass hpriority hadvancedContains
        have hrun := nonpreemptivePriorityFifoPrecedesDisposition_run
          admitted jobs earlier later hadmitted
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun
      · have hjobsTail : ∀ job ∈ jobs, job ≠ earlier := by
          intro job hjob
          exact hjobs job (List.mem_cons_of_mem _ hjob)
        have hrun := ih admitted hadmittedClass hadmittedContains hjobsTail htail
        simpa [runNonpreemptivePriorityArrivalTrace,
          advanceThenAdmitNonpreemptivePriorityJob, advanced, admitted] using hrun

end

end AppliedModelingLib.Queueing
