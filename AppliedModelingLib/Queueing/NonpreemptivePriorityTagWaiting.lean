import AppliedModelingLib.Queueing.NonpreemptivePriorityFixedTraceSkeleton
import AppliedModelingLib.Queueing.NonpreemptivePriorityTraceProvenance
import AppliedModelingLib.Queueing.NonpreemptivePriorityIdentifierTransport
import AppliedModelingLib.Queueing.NonpreemptivePriorityTimeTranslation

/-!
# Tagged waiting observations in finite nonpreemptive-priority traces

This module gives a label-based observable for whether a job remains in a
FIFO queue.  In a fixed-coordinate replay its value is branch-static, while
evaluation agrees exactly with the corresponding literal finite state.  It is
therefore suitable for prefix-measurable tagged-service-start observations.
-/

namespace AppliedModelingLib.Queueing

noncomputable section

/-- A job label occurs in one of the class FIFO lists of a finite priority
state.  This is the literal condition that the labelled job has not yet begun
service and has not completed. -/
def nonpreemptivePriorityWaitingIdentifier
    {n : ℕ} {JobId : Type*}
    (identifier : JobId) (state : NonpreemptivePriorityWorkState n JobId) : Prop :=
  ∃ i job, job ∈ state.waiting i ∧ job.identifier = identifier

/-- Live-equivalent finite priority states agree on whether each labelled job
is still waiting.  Completion-ledger history is intentionally irrelevant to
this present-queue observation. -/
theorem nonpreemptivePriorityWaitingIdentifier_iff_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    (identifier : JobId) {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    nonpreemptivePriorityWaitingIdentifier identifier first ↔
      nonpreemptivePriorityWaitingIdentifier identifier second := by
  unfold nonpreemptivePriorityWaitingIdentifier
  rw [show first.waiting = second.waiting from hequivalent.2.2]

/-- Re-expressing a finite trace at a different time origin preserves whether
a given job identifier is waiting. -/
theorem nonpreemptivePriorityWaitingIdentifier_translate_iff
    {n : ℕ} {JobId : Type*}
    (identifier : JobId) (offset : ℝ)
    (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWaitingIdentifier identifier
        (translateNonpreemptivePriorityWorkState offset state) ↔
      nonpreemptivePriorityWaitingIdentifier identifier state := by
  constructor
  · rintro ⟨i, job, hjob, hidentifier⟩
    change job ∈ (state.waiting i).map (translateNonpreemptivePriorityJob offset) at hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, horiginalEq⟩
    subst job
    exact ⟨i, original, horiginal, by simpa using hidentifier⟩
  · rintro ⟨i, job, hjob, hidentifier⟩
    refine ⟨i, translateNonpreemptivePriorityJob offset job, ?_, ?_⟩
    · change translateNonpreemptivePriorityJob offset job ∈
        (state.waiting i).map (translateNonpreemptivePriorityJob offset)
      exact List.mem_map.mpr ⟨job, hjob, rfl⟩
    · simpa using hidentifier

/-- Relabelling a finite trace by an injective identifier map preserves FIFO
membership of each particular job. -/
theorem nonpreemptivePriorityWaitingIdentifier_mapIdentifier_iff
    {n : ℕ} {JobId JobId' : Type*}
    (f : JobId → JobId') (hinjective : Function.Injective f)
    (identifier : JobId) (state : NonpreemptivePriorityWorkState n JobId) :
    nonpreemptivePriorityWaitingIdentifier (f identifier)
        (nonpreemptivePriorityWorkStateMapIdentifier f state) ↔
      nonpreemptivePriorityWaitingIdentifier identifier state := by
  constructor
  · rintro ⟨i, job, hjob, hidentifier⟩
    change job ∈ (state.waiting i).map (nonpreemptivePriorityJobMapIdentifier f) at hjob
    rcases List.mem_map.mp hjob with ⟨original, horiginal, horiginalEq⟩
    subst job
    refine ⟨i, original, horiginal, ?_⟩
    apply hinjective
    simpa [nonpreemptivePriorityJobMapIdentifier] using hidentifier
  · rintro ⟨i, job, hjob, hidentifier⟩
    refine ⟨i, nonpreemptivePriorityJobMapIdentifier f job, ?_, ?_⟩
    · change nonpreemptivePriorityJobMapIdentifier f job ∈
        (state.waiting i).map (nonpreemptivePriorityJobMapIdentifier f)
      exact List.mem_map.mpr ⟨job, hjob, rfl⟩
    · simpa [nonpreemptivePriorityJobMapIdentifier] using congrArg f hidentifier

/-- A FIFO occurrence and an active occurrence of the same literal record
are two distinct entries in the trace-provenance ledger. -/
theorem one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_mem_waiting_and_active
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n) (residual : ℝ)
    (hwaiting : job ∈ state.waiting i)
    (hactive : state.active = some (job, residual)) :
    1 < nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  have hactiveExists : ∃ residual, state.active = some (job, residual) :=
    ⟨residual, hactive⟩
  have hwaitingCount : 1 ≤ (state.waiting i).count job :=
    List.count_pos_iff.mpr hwaiting
  have hsum : (state.waiting i).count job ≤ ∑ k, (state.waiting k).count job := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun k => (state.waiting k).count job)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [nonpreemptivePriorityWorkStateJobMultiplicity, if_pos hactiveExists]
  omega

/-- A FIFO occurrence and a completion-ledger occurrence of the same literal
record are two distinct entries in the trace-provenance ledger. -/
theorem one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_mem_waiting_and_completed
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n) (completedAt : ℝ)
    (hwaiting : job ∈ state.waiting i)
    (hcompleted : (job, completedAt) ∈ state.completed) :
    1 < nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  have hwaitingCount : 1 ≤ (state.waiting i).count job :=
    List.count_pos_iff.mpr hwaiting
  have hsum : (state.waiting i).count job ≤ ∑ k, (state.waiting k).count job := by
    exact Finset.single_le_sum
      (s := Finset.univ) (f := fun k => (state.waiting k).count job)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hcompletedMem : job ∈ state.completed.map Prod.fst := by
    exact List.mem_map.mpr ⟨(job, completedAt), hcompleted, rfl⟩
  have hcompletedCount : 1 ≤ (state.completed.map Prod.fst).count job :=
    List.count_pos_iff.mpr hcompletedMem
  unfold nonpreemptivePriorityWorkStateJobMultiplicity
  split <;> omega

/-- An active occurrence and a completion-ledger occurrence of the same
literal record are two distinct entries in the trace-provenance ledger. -/
theorem one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_active_and_completed
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (residual completedAt : ℝ)
    (hactive : state.active = some (job, residual))
    (hcompleted : (job, completedAt) ∈ state.completed) :
    1 < nonpreemptivePriorityWorkStateJobMultiplicity state job := by
  classical
  have hactiveExists : ∃ residual, state.active = some (job, residual) :=
    ⟨residual, hactive⟩
  have hcompletedMem : job ∈ state.completed.map Prod.fst := by
    exact List.mem_map.mpr ⟨(job, completedAt), hcompleted, rfl⟩
  have hcompletedCount : 1 ≤ (state.completed.map Prod.fst).count job :=
    List.count_pos_iff.mpr hcompletedMem
  rw [nonpreemptivePriorityWorkStateJobMultiplicity, if_pos hactiveExists]
  omega

/-- In a single-occurrence trace, a literal job has at most one recorded
completion epoch. -/
theorem completedAt_eq_of_mem_completed_of_jobMultiplicity_le_one
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (left right : ℝ)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state job ≤ 1)
    (hleft : (job, left) ∈ state.completed)
    (hright : (job, right) ∈ state.completed) :
    left = right := by
  classical
  have hcompleted : (state.completed.map Prod.fst).count job ≤ 1 := by
    exact (nonpreemptivePriorityCompletedJobMultiplicity_le state job).trans hmultiplicity
  have hunique : ∀ (entries : List (NonpreemptivePriorityJob n JobId × ℝ))
      (first second : ℝ),
      (job, first) ∈ entries → (job, second) ∈ entries →
      (entries.map Prod.fst).count job ≤ 1 → first = second := by
    intro entries
    induction entries with
    | nil =>
        intro first second hfirst
        simp at hfirst
    | cons head tail ih =>
        rcases head with ⟨headJob, headTime⟩
        intro first second hfirst hsecond hcount
        by_cases hhead : headJob = job
        · subst headJob
          have htailZero : (tail.map Prod.fst).count job = 0 := by
            simp only [List.map_cons, List.count_cons, beq_self_eq_true, ite_true] at hcount
            omega
          have hfirstEq : first = headTime := by
            rcases List.mem_cons.mp hfirst with hfirst | hfirst
            · exact congrArg Prod.snd hfirst
            · have hpositive : 0 < (tail.map Prod.fst).count job := by
                apply List.count_pos_iff.mpr
                exact List.mem_map.mpr ⟨(job, first), hfirst, rfl⟩
              omega
          have hsecondEq : second = headTime := by
            rcases List.mem_cons.mp hsecond with hsecond | hsecond
            · exact congrArg Prod.snd hsecond
            · have hpositive : 0 < (tail.map Prod.fst).count job := by
                apply List.count_pos_iff.mpr
                exact List.mem_map.mpr ⟨(job, second), hsecond, rfl⟩
              omega
          linarith
        · have hcountTail : (tail.map Prod.fst).count job ≤ 1 := by
            simpa [List.count, hhead] using hcount
          have hfirstTail : (job, first) ∈ tail := by
            rcases List.mem_cons.mp hfirst with hfirst | hfirst
            · exact (hhead (congrArg Prod.fst hfirst).symm).elim
            · exact hfirst
          have hsecondTail : (job, second) ∈ tail := by
            rcases List.mem_cons.mp hsecond with hsecond | hsecond
            · exact (hhead (congrArg Prod.fst hsecond).symm).elim
            · exact hsecond
          exact ih first second hfirstTail hsecondTail hcountTail
  exact hunique state.completed left right hleft hright hcompleted

/-- In a single-occurrence trace, a tagged FIFO record is neither active nor
already completed. -/
theorem not_exists_active_or_completed_of_mem_waiting_of_jobMultiplicity_le_one
    {n : ℕ} {JobId : Type*}
    (state : NonpreemptivePriorityWorkState n JobId)
    (job : NonpreemptivePriorityJob n JobId) (i : Fin n)
    (hwaiting : job ∈ state.waiting i)
    (hmultiplicity : nonpreemptivePriorityWorkStateJobMultiplicity state job ≤ 1) :
    (¬ ∃ residual, state.active = some (job, residual)) ∧
      (¬ ∃ completedAt, (job, completedAt) ∈ state.completed) := by
  constructor
  · rintro ⟨residual, hactive⟩
    have htwo := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_mem_waiting_and_active
      state job i residual hwaiting hactive
    omega
  · rintro ⟨completedAt, hcompleted⟩
    have htwo := one_lt_nonpreemptivePriorityWorkStateJobMultiplicity_of_mem_waiting_and_completed
      state job i completedAt hwaiting hcompleted
    omega

/-- Numeric indicator of the labelled job still being in a finite FIFO list. -/
noncomputable def nonpreemptivePriorityWaitingIdentifierIndicator
    {n : ℕ} {JobId : Type*}
    (identifier : JobId) (state : NonpreemptivePriorityWorkState n JobId) : ℝ := by
  classical
  exact if nonpreemptivePriorityWaitingIdentifier identifier state then 1 else 0

/-- The numeric labelled-waiting observation is invariant under live queue
equivalence. -/
theorem nonpreemptivePriorityWaitingIdentifierIndicator_eq_of_liveEquivalent
    {n : ℕ} {JobId : Type*}
    (identifier : JobId) {first second : NonpreemptivePriorityWorkState n JobId}
    (hequivalent : liveEquivalentNonpreemptivePriorityWorkState first second) :
    nonpreemptivePriorityWaitingIdentifierIndicator identifier first =
      nonpreemptivePriorityWaitingIdentifierIndicator identifier second := by
  unfold nonpreemptivePriorityWaitingIdentifierIndicator
  rw [nonpreemptivePriorityWaitingIdentifier_iff_of_liveEquivalent identifier hequivalent]

/-- The static fixed-coordinate analogue of FIFO membership by label. -/
def fixedNonpreemptivePriorityWaitingIdentifier
    {Ω : Type*} {n : ℕ} {JobId : Type*}
    (identifier : JobId)
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) : Prop :=
  ∃ i job, job ∈ state.waiting i ∧ job.identifier = identifier

/-- A fixed-coordinate FIFO-membership indicator.  Its value is constant on
the sample space because a fixed replay skeleton fixes all discrete labels and
list shapes. -/
noncomputable def fixedNonpreemptivePriorityWaitingIdentifierIndicator
    {Ω : Type*} {n : ℕ} {JobId : Type*}
    (identifier : JobId)
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) : Ω → ℝ := by
  classical
  exact if fixedNonpreemptivePriorityWaitingIdentifier identifier state then
    fun _ => 1 else fun _ => 0

/-- Evaluating a fixed-coordinate state preserves labelled FIFO membership. -/
theorem fixedNonpreemptivePriorityWaitingIdentifier_iff_eval
    {Ω : Type*} {n : ℕ} {JobId : Type*}
    (identifier : JobId)
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) (omega : Ω) :
    fixedNonpreemptivePriorityWaitingIdentifier identifier state ↔
      nonpreemptivePriorityWaitingIdentifier identifier (state.eval omega) := by
  constructor
  · rintro ⟨i, job, hjob, hidentifier⟩
    refine ⟨i, job.eval omega, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨job, hjob, rfl⟩
    · simpa [NonpreemptivePriorityFixedJobCoordinate.eval] using hidentifier
  · rintro ⟨i, job, hjob, hidentifier⟩
    rcases List.mem_map.mp hjob with ⟨fixedJob, hfixedJob, heq⟩
    subst job
    refine ⟨i, fixedJob, hfixedJob, ?_⟩
    simpa [NonpreemptivePriorityFixedJobCoordinate.eval] using hidentifier

/-- The static indicator evaluates to the literal FIFO-membership indicator. -/
theorem fixedNonpreemptivePriorityWaitingIdentifierIndicator_eval
    {Ω : Type*} {n : ℕ} {JobId : Type*}
    (identifier : JobId)
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) (omega : Ω) :
    fixedNonpreemptivePriorityWaitingIdentifierIndicator identifier state omega =
      nonpreemptivePriorityWaitingIdentifierIndicator identifier (state.eval omega) := by
  classical
  by_cases hfixed : fixedNonpreemptivePriorityWaitingIdentifier identifier state
  · have heval : nonpreemptivePriorityWaitingIdentifier identifier (state.eval omega) :=
      (fixedNonpreemptivePriorityWaitingIdentifier_iff_eval identifier state omega).mp hfixed
    simp [fixedNonpreemptivePriorityWaitingIdentifierIndicator,
      nonpreemptivePriorityWaitingIdentifierIndicator, hfixed, heval]
  · have heval : ¬ nonpreemptivePriorityWaitingIdentifier identifier (state.eval omega) := by
      intro h
      exact hfixed ((fixedNonpreemptivePriorityWaitingIdentifier_iff_eval
        identifier state omega).mpr h)
    simp [fixedNonpreemptivePriorityWaitingIdentifierIndicator,
      nonpreemptivePriorityWaitingIdentifierIndicator, hfixed, heval]

/-- Every fixed-coordinate FIFO-membership indicator is Borel. -/
theorem measurable_fixedNonpreemptivePriorityWaitingIdentifierIndicator
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {JobId : Type*}
    (identifier : JobId)
    (state : NonpreemptivePriorityFixedStateCoordinate Ω n JobId) :
    Measurable (fixedNonpreemptivePriorityWaitingIdentifierIndicator identifier state) := by
  classical
  unfold fixedNonpreemptivePriorityWaitingIdentifierIndicator
  split <;> exact measurable_const

end

end AppliedModelingLib.Queueing
