import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSCompletionTrace
import Mathlib.Tactic

/-!
# Key accounting for finite FCFS completion traces

The finite FCFS executor retains source identifiers.  This module records an
exact conservation law for the number of records satisfying any Boolean key:
at every finite trace boundary, each keyed source job is either still in the
residual ledger or has occurred once in the completion trace.  Endpoint-job
key counts are included explicitly, so the result does not assume identifier
uniqueness or a particular source model.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- Count keyed source jobs supplied at the endpoints of a finite segment
trace for one class. -/
def finiteGPSFCFSSegmentStepsEndpointKeyCount
    (key : JobId → Bool) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℕ :=
  (steps.map fun step =>
    (step.endpointJobs.jobs i).countP fun job => key job.identifier).sum

/-- Endpoint key counts add across a literal segment-list boundary. -/
theorem finiteGPSFCFSSegmentStepsEndpointKeyCount_append
    (key : JobId → Bool) (i : Class)
    (left right : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    finiteGPSFCFSSegmentStepsEndpointKeyCount key i (left ++ right) =
      finiteGPSFCFSSegmentStepsEndpointKeyCount key i left +
        finiteGPSFCFSSegmentStepsEndpointKeyCount key i right := by
  simp [finiteGPSFCFSSegmentStepsEndpointKeyCount]

/-- Summing a Boolean indicator over a finite list is its predicate count. -/
theorem List.sum_map_indicator_eq_countP
    {α : Type*} (key : α → Bool) :
    ∀ entries : List α,
      (entries.map fun entry => if key entry then 1 else 0).sum =
        entries.countP key := by
  intro entries
  induction entries with
  | nil => simp
  | cons entry entries ih =>
      simp [List.countP_cons, ih, Nat.add_comm]

/-- A duplicate-free list with a present keyed entry and no other keyed value
has exactly one keyed occurrence. -/
theorem List.countP_eq_one_of_nodup_of_mem_of_keyed_eq
    {α : Type*} (key : α → Bool) :
    ∀ (entries : List α) (selected : α),
      entries.Nodup → selected ∈ entries → key selected = true →
      (∀ entry ∈ entries, key entry = true → entry = selected) →
      entries.countP key = 1 := by
  intro entries
  induction entries with
  | nil =>
      intro selected hnodup hmem
      simp at hmem
  | cons head tail ih =>
      intro selected hnodup hselected hselected_key hunique
      by_cases hhead : key head = true
      · have hhead' : key head := by simpa using hhead
        have hhead_eq : head = selected := hunique head (by simp) hhead
        have htail_no_key : ∀ entry ∈ tail, ¬ key entry := by
          intro entry hentry hentry_key
          have hentry_eq : entry = selected := hunique entry (by simp [hentry])
            (by simpa using hentry_key)
          have : entry = head := hentry_eq.trans hhead_eq.symm
          exact (List.nodup_cons.mp hnodup).1 (this ▸ hentry)
        rw [List.countP_cons_of_pos hhead']
        have htail_zero : tail.countP key = 0 :=
          List.countP_eq_zero.mpr htail_no_key
        omega
      · have hhead' : ¬ key head := by simpa using hhead
        have hselected_tail : selected ∈ tail := by
          rcases List.mem_cons.mp hselected with hselected | hselected
          · subst selected
            exact False.elim (hhead' (by simpa using hselected_key))
          · exact hselected
        rw [List.countP_cons_of_neg hhead']
        apply ih selected (List.nodup_cons.mp hnodup).2 hselected_tail hselected_key
        intro entry hentry hentry_key
        exact hunique entry (by simp [hentry]) hentry_key

/-- In one FCFS consumption pass, every keyed input job is represented either
by a completion record or by a residual job, with no loss or duplication. -/
theorem finiteGPSFCFSCompletedJobsFrom_keyCount_add_consume_keyCount
    (key : JobId → Bool)
    (segmentStart classRate serviceBefore availableService : ℝ)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    (finiteGPSFCFSCompletedJobsFrom segmentStart classRate serviceBefore
      availableService jobs).countP (fun completion => key completion.identifier) +
      (finiteGPSFCFSConsume availableService jobs).countP
        (fun job => key job.identifier) =
      jobs.countP (fun job => key job.identifier) := by
  induction jobs generalizing serviceBefore availableService with
  | nil =>
      simp [finiteGPSFCFSCompletedJobsFrom, finiteGPSFCFSConsume]
  | cons job jobs ih =>
      by_cases hpartial : availableService < job.residualWork
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_nil_of_partial_head
            segmentStart classRate serviceBefore availableService job jobs hpartial,
            finiteGPSFCFSConsume_eq_partial_head
              availableService job jobs hpartial]
        simp [List.countP_cons]
      · rw [finiteGPSFCFSCompletedJobsFrom_eq_cons_of_complete_head
            segmentStart classRate serviceBefore availableService job jobs hpartial,
            finiteGPSFCFSConsume_eq_after_complete_head
              availableService job jobs hpartial]
        have htail := ih
          (serviceBefore := serviceBefore + job.residualWork)
          (availableService := availableService - job.residualWork)
        simpa [finiteGPSFCFSCompletionOf, List.countP_cons,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- The same key-accounting identity for the completion list emitted by one
concrete GPS segment. -/
theorem finiteGPSFCFSCompletedJobsInSegment_keyCount_add_consume_keyCount
    (key : JobId → Bool) (segment : FiniteGPSExecutionSegment Class) (i : Class)
    (jobs : List (FiniteGPSFCFSJob JobId)) :
    (finiteGPSFCFSCompletedJobsInSegment segment i jobs).countP
        (fun completion => key completion.identifier) +
      (finiteGPSFCFSConsume (segment.serviceIncrement i) jobs).countP
        (fun job => key job.identifier) =
      jobs.countP (fun job => key job.identifier) := by
  simpa [finiteGPSFCFSCompletedJobsInSegment, finiteGPSFCFSCompletedJobs] using
    (finiteGPSFCFSCompletedJobsFrom_keyCount_add_consume_keyCount
      key segment.startTime (segment.classRate i) 0 (segment.serviceIncrement i) jobs)

/-- Exact key accounting over a complete finite FCFS segment fold.  The left
side records keyed completion records and keyed final residual jobs; the right
side records the keyed initial jobs and every keyed literal endpoint job. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_keyCount_add_residualKeyCount
    (key : JobId → Bool)
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class) :
    ∀ steps : List (FiniteGPSFCFSSegmentJobStep Class JobId),
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps).countP
          (fun completion => key completion.identifier) +
        ((finiteGPSFCFSRunSegmentSteps initial steps).residualJobs i).countP
          (fun job => key job.identifier) =
        (initial.residualJobs i).countP (fun job => key job.identifier) +
          finiteGPSFCFSSegmentStepsEndpointKeyCount key i steps := by
  intro steps
  induction steps generalizing initial with
  | nil =>
      simp [finiteGPSFCFSRunSegmentStepsClassCompletions,
        finiteGPSFCFSRunSegmentSteps, finiteGPSFCFSSegmentStepsEndpointKeyCount]
  | cons step steps ih =>
      have hsegment := finiteGPSFCFSCompletedJobsInSegment_keyCount_add_consume_keyCount
        key step.segment i (initial.residualJobs i)
      have htail := ih
        (initial := finiteGPSFCFSApplySegment initial step.segment step.endpointJobs)
      have happly :
          ((finiteGPSFCFSApplySegment initial step.segment step.endpointJobs).residualJobs i).countP
              (fun job => key job.identifier) =
            (finiteGPSFCFSConsume (step.segment.serviceIncrement i)
              (initial.residualJobs i)).countP (fun job => key job.identifier) +
              (step.endpointJobs.jobs i).countP (fun job => key job.identifier) := by
        simp [finiteGPSFCFSApplySegment]
      simp only [finiteGPSFCFSRunSegmentStepsClassCompletions,
        finiteGPSFCFSRunSegmentSteps, finiteGPSFCFSSegmentStepsEndpointKeyCount,
        List.map_cons, List.sum_cons, List.countP_append] at htail ⊢
      omega

/-- A list with at most one entry satisfying a Boolean key cannot contain two
different keyed entries. -/
theorem List.eq_of_mem_of_mem_of_countP_le_one
    {α : Type*} (key : α → Bool) :
    ∀ (entries : List α) (left right : α),
      left ∈ entries → key left = true →
      right ∈ entries → key right = true →
      entries.countP key ≤ 1 → left = right := by
  intro entries
  induction entries with
  | nil =>
      intro left right hleft
      simp at hleft
  | cons head tail ih =>
      intro left right hleft hleft_key hright hright_key hcount
      by_cases hhead : key head = true
      · have hhead' : key head := by simpa using hhead
        have htail_zero : tail.countP key = 0 := by
          rw [List.countP_cons_of_pos hhead'] at hcount
          omega
        have hleft_eq : left = head := by
          rcases List.mem_cons.mp hleft with hleft | hleft
          · exact hleft
          · exfalso
            have hpositive : 0 < tail.countP key :=
              List.countP_pos_iff.mpr ⟨left, hleft, by simpa using hleft_key⟩
            omega
        have hright_eq : right = head := by
          rcases List.mem_cons.mp hright with hright | hright
          · exact hright
          · exfalso
            have hpositive : 0 < tail.countP key :=
              List.countP_pos_iff.mpr ⟨right, hright, by simpa using hright_key⟩
            omega
        exact hleft_eq.trans hright_eq.symm
      · have hhead' : ¬ key head := by simpa using hhead
        have hleft_tail : left ∈ tail := by
          rcases List.mem_cons.mp hleft with hleft | hleft
          · subst left
            exact False.elim (hhead' (by simpa using hleft_key))
          · exact hleft
        have hright_tail : right ∈ tail := by
          rcases List.mem_cons.mp hright with hright | hright
          · subst right
            exact False.elim (hhead' (by simpa using hright_key))
          · exact hright
        apply ih left right hleft_tail hleft_key hright_tail hright_key
        simpa [List.countP_cons_of_neg hhead'] using hcount

/-- If there are no keyed initial jobs and at most one keyed literal endpoint
job, then a finite FCFS completion trace has at most one keyed completion
record. -/
theorem finiteGPSFCFSRunSegmentStepsClassCompletion_eq_of_mem_key_of_endpointKeyCount_le_one
    (key : JobId → Bool)
    (initial : FiniteGPSFCFSJobLedger Class JobId) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hinitial : (initial.residualJobs i).countP (fun job => key job.identifier) = 0)
    (hendpoint : finiteGPSFCFSSegmentStepsEndpointKeyCount key i steps ≤ 1)
    (left right : FiniteGPSFCFSCompletion JobId)
    (hleft : left ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps)
    (hleft_key : key left.identifier = true)
    (hright : right ∈ finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps)
    (hright_key : key right.identifier = true) :
    left = right := by
  have haccount := finiteGPSFCFSRunSegmentStepsClassCompletion_keyCount_add_residualKeyCount
    key initial i steps
  have hcompletion_count :
      (finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps).countP
          (fun completion => key completion.identifier) ≤ 1 := by
    rw [hinitial] at haccount
    omega
  exact List.eq_of_mem_of_mem_of_countP_le_one
    (fun completion : FiniteGPSFCFSCompletion JobId => key completion.identifier)
    (finiteGPSFCFSRunSegmentStepsClassCompletions initial i steps)
    left right hleft hleft_key hright hright_key hcompletion_count

end

end AppliedModelingLib.Probability.Queueing
