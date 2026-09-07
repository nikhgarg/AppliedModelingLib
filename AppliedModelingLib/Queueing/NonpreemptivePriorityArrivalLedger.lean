import AppliedModelingLib.Queueing.NonpreemptivePriorityFiniteTrace

/-!
# Finite arrival ledgers for nonpreemptive-priority queues

This module turns a finite family of class-labelled arrival indices into the
chronological job list consumed by the deterministic priority trace.  It has no
probabilistic assumptions: a stationary point-process construction supplies a
finite index set in each bounded window and instantiates these definitions.
-/

namespace AppliedModelingLib
namespace Queueing

noncomputable section

/-- Two disjoint finite ledgers can be enumerated as the concatenation of
their separate enumerations, up to permutation. -/
theorem Finset.toList_union_perm_append_of_disjoint
    {α : Type*} [DecidableEq α]
    (first second : Finset α) (hdisjoint : Disjoint first second) :
    (first ∪ second).toList.Perm (first.toList ++ second.toList) := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (first ∪ second).nodup_toList
  · apply first.nodup_toList.append second.nodup_toList
    rw [List.disjoint_iff_ne]
    intro x hfirst y hsecond hxy
    subst y
    exact (Finset.disjoint_left.mp hdisjoint
      (Finset.mem_toList.mp hfirst) (Finset.mem_toList.mp hsecond)).elim
  · simp

/-- A class label together with an index in that class's two-sided arrival
stream. -/
abbrev NonpreemptivePriorityArrivalIndex (n : ℕ) := Sigma fun _ : Fin n => ℤ

/-- The finite collection of all labelled indices selected by one finite
arrival window. -/
def nonpreemptivePriorityArrivalWindowIndices
    {n : ℕ} (indices : Fin n → Finset ℤ) :
    Finset (NonpreemptivePriorityArrivalIndex n) :=
  Finset.sigma Finset.univ indices

/-- Forming the labelled finite ledger commutes with classwise union. -/
theorem nonpreemptivePriorityArrivalWindowIndices_union
    {n : ℕ} (first second : Fin n → Finset ℤ) :
    nonpreemptivePriorityArrivalWindowIndices (fun i => first i ∪ second i) =
      nonpreemptivePriorityArrivalWindowIndices first ∪
        nonpreemptivePriorityArrivalWindowIndices second := by
  ext ⟨i, k⟩
  simp [nonpreemptivePriorityArrivalWindowIndices]

/-- The unsorted jobs attached to a finite family of class-index sets.  The
identifier retains both its class and its location in the original stream. -/
def nonpreemptivePriorityArrivalWindowJobs
    {n : ℕ} (indices : Fin n → Finset ℤ)
    (arrivalTime serviceWork : Fin n → ℤ → ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  (nonpreemptivePriorityArrivalWindowIndices indices).toList.map fun q =>
    { identifier := q
      priority := q.1
      arrivalTime := arrivalTime q.1 q.2
      serviceWork := serviceWork q.1 q.2 }

/-- The raw finite ledger contains exactly one job for every selected
class-index pair, with the supplied epoch and work mark. -/
theorem mem_nonpreemptivePriorityArrivalWindowJobs_iff
    {n : ℕ} (indices : Fin n → Finset ℤ)
    (arrivalTime serviceWork : Fin n → ℤ → ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ nonpreemptivePriorityArrivalWindowJobs indices arrivalTime serviceWork ↔
      ∃ (i : Fin n) (k : ℤ), k ∈ indices i ∧
        job =
          { identifier := Sigma.mk i k
            priority := i
            arrivalTime := arrivalTime i k
            serviceWork := serviceWork i k } := by
  simp [nonpreemptivePriorityArrivalWindowJobs,
    nonpreemptivePriorityArrivalWindowIndices, eq_comm]

/-- Sort a finite job ledger by physical arrival epoch.  Equal epochs retain a
deterministic implementation order. -/
def chronologicalNonpreemptivePriorityJobs
    {n : ℕ} {JobId : Type*}
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    List (NonpreemptivePriorityJob n JobId) :=
  jobs.mergeSort fun job other => job.arrivalTime ≤ other.arrivalTime

/-- A chronological finite arrival ledger is the sort of the corresponding
class-index window. -/
def chronologicalNonpreemptivePriorityArrivalWindowJobs
    {n : ℕ} (indices : Fin n → Finset ℤ)
    (arrivalTime serviceWork : Fin n → ℤ → ℝ) :
    List (NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :=
  chronologicalNonpreemptivePriorityJobs
    (nonpreemptivePriorityArrivalWindowJobs indices arrivalTime serviceWork)

/-- Sorting a finite ledger does not alter which labelled jobs it contains. -/
theorem mem_chronologicalNonpreemptivePriorityArrivalWindowJobs_iff
    {n : ℕ} (indices : Fin n → Finset ℤ)
    (arrivalTime serviceWork : Fin n → ℤ → ℝ)
    (job : NonpreemptivePriorityJob n (NonpreemptivePriorityArrivalIndex n)) :
    job ∈ chronologicalNonpreemptivePriorityArrivalWindowJobs indices arrivalTime serviceWork ↔
      ∃ (i : Fin n) (k : ℤ), k ∈ indices i ∧
        job =
          { identifier := Sigma.mk i k
            priority := i
            arrivalTime := arrivalTime i k
            serviceWork := serviceWork i k } := by
  unfold chronologicalNonpreemptivePriorityArrivalWindowJobs
    chronologicalNonpreemptivePriorityJobs
  rw [List.Perm.mem_iff (List.mergeSort_perm _ _)]
  exact mem_nonpreemptivePriorityArrivalWindowJobs_iff indices arrivalTime serviceWork job

/-- The chronological ledger is nondecreasing in physical arrival time. -/
theorem pairwise_arrivalTime_le_chronologicalNonpreemptivePriorityJobs
    {n : ℕ} {JobId : Type*}
    (jobs : List (NonpreemptivePriorityJob n JobId)) :
    (chronologicalNonpreemptivePriorityJobs jobs).Pairwise
      (fun job other => job.arrivalTime ≤ other.arrivalTime) := by
  simpa [chronologicalNonpreemptivePriorityJobs, decide_eq_true_eq] using
    (List.pairwise_mergeSort
    (le := fun job other : NonpreemptivePriorityJob n JobId =>
      job.arrivalTime ≤ other.arrivalTime)
    (fun _ _ _ hfirst hsecond => by
      simp only [decide_eq_true_eq] at hfirst hsecond ⊢
      exact le_trans hfirst hsecond)
    (fun first second => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total first.arrivalTime second.arrivalTime)
    jobs)

/-- The chronological window ledger has the same concrete jobs as the raw
finite index ledger, up to order. -/
theorem perm_chronologicalNonpreemptivePriorityArrivalWindowJobs
    {n : ℕ} (indices : Fin n → Finset ℤ)
    (arrivalTime serviceWork : Fin n → ℤ → ℝ) :
    List.Perm
      (chronologicalNonpreemptivePriorityArrivalWindowJobs indices arrivalTime serviceWork)
      (nonpreemptivePriorityArrivalWindowJobs indices arrivalTime serviceWork) := by
  exact List.mergeSort_perm _ _

end

end Queueing
end AppliedModelingLib
