import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedTargetSourceOrder
import Mathlib.Tactic

/-!
# Chronological literal target predecessors in the tagged source trace

This module isolates a source-only fact used by the closed pre-tag GPS
projection: filtering the literal finite endpoint trace by the presence of a
target predecessor returns exactly those predecessors in physical chronological
order.  Selection is by source identifier, never by a numerical work mark;
simultaneous passive jobs remain attached to their original source batch.

No queueing, service, or GPS comparison statement is made here.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The target predecessor at chronological position `j`: position zero is
the oldest predecessor, while the final position is the immediate predecessor.
This local source-order spelling is definitionally the arithmetic used by the
closed projection certificate, while avoiding an import cycle with it. -/
def taggedAdmittedChronologicalRemotePredecessorIndex
    (remoteStart : Nat) (j : Fin remoteStart) : Nat :=
  remoteStart - (j.1 + 1)

/-- The physical endpoint time of a chronological target predecessor. -/
def taggedAdmittedChronologicalRemotePredecessorTime
    (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (j : Fin remoteStart) : ℝ :=
  candidatePalmArrival z.1.1
    (Int.negSucc (taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j))

/-- The literal source endpoint batches for the target predecessors in a
finite past window, oldest first.  Endpoint batches retain all simultaneous
source data, including passive jobs. -/
def taggedAdmittedChronologicalRemotePredecessorEndpointTrace
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    List (TaggedAdmittedFiniteGPSTimedEndpointJobs Category) :=
  List.ofFn fun j : Fin remoteStart =>
    { eventTime := taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j
      endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z
        (taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j) }

/-- The executable source-label predicate selecting a target predecessor from
a timed endpoint batch.  In particular, a zero work mark is still selected.
The finite `range` makes the filter decidable without assuming a decision
procedure for an unbounded existential. -/
noncomputable def taggedAdmittedIsRemotePredecessorEndpointBatch
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (batch : TaggedAdmittedFiniteGPSTimedEndpointJobs Category) : Bool := by
  classical
  exact (List.range remoteStart).any fun n =>
    decide (taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
      batch.endpointJobs.jobs target)

/-- Semantic form of the finite source-label filter. -/
theorem taggedAdmittedIsRemotePredecessorEndpointBatch_eq_true_iff
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat)
    (batch : TaggedAdmittedFiniteGPSTimedEndpointJobs Category) :
    taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart batch = true ↔
      ∃ n : Nat, n < remoteStart ∧
        taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
          batch.endpointJobs.jobs target := by
  classical
  simp [taggedAdmittedIsRemotePredecessorEndpointBatch]

/-- The chronological predecessor index is always in the selected finite
past window. -/
theorem taggedAdmittedChronologicalRemotePredecessorIndex_lt
    (remoteStart : Nat) (j : Fin remoteStart) :
    taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j < remoteStart := by
  simp only [taggedAdmittedChronologicalRemotePredecessorIndex]
  omega

/-- Every finite remote predecessor has one chronological position. -/
theorem exists_taggedAdmittedChronologicalRemotePredecessorIndex_eq
    {remoteStart n : Nat} (hn : n < remoteStart) :
    ∃ j : Fin remoteStart,
      taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j = n := by
  refine ⟨⟨remoteStart - (n + 1), by omega⟩, ?_⟩
  simp only [taggedAdmittedChronologicalRemotePredecessorIndex]
  omega

/-- Literal target predecessor epochs are strictly increasing in chronological
position. -/
theorem strictMono_taggedAdmittedChronologicalRemotePredecessorTime
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat) :
    StrictMono (taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart) := by
  intro j k hjk
  apply suspensionGoodGapPath_strictMono z.1.1 htarget_good.1
  simp only [taggedAdmittedChronologicalRemotePredecessorIndex] at *
  have hjk' : j.1 < k.1 := hjk
  omega

/-- The time-only form of the literal predecessor predicate.  It is used to
factor a filter through the source trace's map from epochs to endpoint
batches. -/
noncomputable def taggedAdmittedIsRemotePredecessorTime
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (eventTime : ℝ) : Bool := by
  classical
  exact (List.range remoteStart).any fun n =>
    decide (taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
      (taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime).jobs target)

/-- Semantic form of the time-level filter used to factor the endpoint-trace
filter through its epoch map. -/
theorem taggedAdmittedIsRemotePredecessorTime_eq_true_iff
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (eventTime : ℝ) :
    taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart eventTime = true ↔
      ∃ n : Nat, n < remoteStart ∧
        taggedAdmittedFCFSJob target z (target, Int.negSucc n) ∈
          (taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime).jobs target := by
  classical
  simp [taggedAdmittedIsRemotePredecessorTime]

/-- A selected source epoch is exactly one literal target predecessor epoch.
The source-trace membership in the premise ensures the forward direction does
not silently introduce arbitrary non-source times. -/
theorem mem_taggedAdmittedBatchTimeTrace_filter_remotePredecessor_iff
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (eventTime : ℝ) :
    eventTime ∈ (taggedAdmittedBatchTimeTrace resetTime 0 target z).filter
      (taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart) ↔
      ∃ n : Nat, n < remoteStart ∧
        eventTime = candidatePalmArrival z.1.1 (Int.negSucc n) := by
  classical
  constructor
  · intro hmem
    rcases List.mem_filter.mp hmem with ⟨_, hselected⟩
    rcases (taggedAdmittedIsRemotePredecessorTime_eq_true_iff
      resetTime target z remoteStart eventTime).mp hselected with ⟨n, hn, hjob⟩
    have htime := (mem_taggedAdmittedFCFSJob_jobsAt_iff
      resetTime 0 target z eventTime target (Int.negSucc n)).mp hjob |>.2
    refine ⟨n, hn, ?_⟩
    simpa [taggedAdmittedSourceArrival] using htime.symm
  · rintro ⟨n, hn, heventTime⟩
    have hindex : Int.negSucc n ∈
        taggedAdmittedArrivalIndicesBetween resetTime 0 target z target := by
      rw [taggedAdmittedTargetArrivalIndicesBetween_eq_range_image_of_pastWindowCoverage
        resetTime target z htarget_good remoteStart hcoverage]
      exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩
    have hledger : (target, Int.negSucc n) ∈
        taggedAdmittedSourceJobLedger resetTime 0 target z :=
      taggedAdmittedSourceJob_mem_ledger resetTime 0 target z target
        (Int.negSucc n) hindex
    have hbatchTimes : candidatePalmArrival z.1.1 (Int.negSucc n) ∈
        taggedAdmittedBatchTimes resetTime 0 target z := by
      apply (mem_taggedAdmittedBatchTimes_iff resetTime 0 target z _).mpr
      refine ⟨(target, Int.negSucc n), hledger, ?_⟩
      simp [taggedAdmittedSourceArrival]
    have htrace : candidatePalmArrival z.1.1 (Int.negSucc n) ∈
        taggedAdmittedBatchTimeTrace resetTime 0 target z :=
      (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mpr hbatchTimes
    subst eventTime
    apply List.mem_filter.mpr
    refine ⟨htrace, (taggedAdmittedIsRemotePredecessorTime_eq_true_iff
      resetTime target z remoteStart _).mpr ⟨n, hn, ?_⟩⟩
    apply (mem_taggedAdmittedFCFSJob_jobsAt_iff
      resetTime 0 target z _ target (Int.negSucc n)).mpr
    refine ⟨hindex, ?_⟩
    simp [taggedAdmittedSourceArrival]

/-- The filtered source epoch list contains exactly the chronological finite
remote predecessor window. -/
theorem taggedAdmittedBatchTimeTrace_filter_remotePredecessor_eq_chronological
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart) :
    (taggedAdmittedBatchTimeTrace resetTime 0 target z).filter
      (taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart) =
      List.ofFn (taggedAdmittedChronologicalRemotePredecessorTime
        target z remoteStart) := by
  classical
  let selectedTimes := (taggedAdmittedBatchTimeTrace resetTime 0 target z).filter
    (taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart)
  have hselected_pairwise_le : selectedTimes.Pairwise (fun left right : ℝ => left ≤ right) := by
    dsimp [selectedTimes]
    exact (Finset.pairwise_sort (taggedAdmittedBatchTimes resetTime 0 target z)
      (fun left right : ℝ => left ≤ right)).filter _
  have hselected_nodup : selectedTimes.Nodup := by
    dsimp [selectedTimes]
    exact (Finset.sort_nodup (taggedAdmittedBatchTimes resetTime 0 target z)
      (fun left right : ℝ => left ≤ right)).filter _
  have hselected_sorted_le : selectedTimes.SortedLE := hselected_pairwise_le.sortedLE
  have hselected_sorted_lt : selectedTimes.SortedLT :=
    hselected_sorted_le.sortedLT_of_nodup hselected_nodup
  have hchronological_sorted_lt :
      (List.ofFn (taggedAdmittedChronologicalRemotePredecessorTime
        target z remoteStart)).SortedLT :=
    (strictMono_taggedAdmittedChronologicalRemotePredecessorTime
      target z htarget_good remoteStart).sortedLT_ofFn
  apply hselected_sorted_lt.eq_of_mem_iff hchronological_sorted_lt
  intro eventTime
  change eventTime ∈ (taggedAdmittedBatchTimeTrace resetTime 0 target z).filter
      (taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart) ↔ _
  rw [mem_taggedAdmittedBatchTimeTrace_filter_remotePredecessor_iff
    resetTime target z htarget_good remoteStart hcoverage]
  constructor
  · rintro ⟨n, hn, heventTime⟩
    rcases exists_taggedAdmittedChronologicalRemotePredecessorIndex_eq hn with ⟨j, hj⟩
    refine List.mem_ofFn.mpr ⟨j, ?_⟩
    simpa [taggedAdmittedChronologicalRemotePredecessorTime, hj] using heventTime.symm
  · intro hmem
    rcases List.mem_ofFn.mp hmem with ⟨j, hj⟩
    refine ⟨taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j,
      taggedAdmittedChronologicalRemotePredecessorIndex_lt remoteStart j, ?_⟩
    simpa [taggedAdmittedChronologicalRemotePredecessorTime] using hj.symm

/-- On a literal source endpoint built from one time, the batch predicate is
exactly the corresponding time predicate. -/
@[simp]
theorem taggedAdmittedIsRemotePredecessorEndpointBatch_mk_eq_time
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (eventTime : ℝ) :
    taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart
      { eventTime := eventTime
        endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime } =
      taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart eventTime := by
  classical
  rfl

/-- The canonical endpoint trace is the map of the canonical chronological
epoch trace through the literal source endpoint constructor. -/
theorem taggedAdmittedChronologicalRemotePredecessorEndpointTrace_eq_map_time
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    taggedAdmittedChronologicalRemotePredecessorEndpointTrace
      resetTime target z remoteStart =
      (List.ofFn (taggedAdmittedChronologicalRemotePredecessorTime
        target z remoteStart)).map fun eventTime =>
        { eventTime := eventTime
          endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime } := by
  unfold taggedAdmittedChronologicalRemotePredecessorEndpointTrace
  simpa only [Function.comp_apply] using
    (List.ofFn_comp'
      (taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart)
      (fun eventTime : ℝ =>
        ({ eventTime := eventTime
           endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime } :
          TaggedAdmittedFiniteGPSTimedEndpointJobs Category)))

/-- Filtering the chronological literal endpoint trace by target source label
returns exactly the remote target predecessors, in physical chronological
order.  This retains simultaneous passive source jobs and does not inspect
any work mark. -/
theorem taggedAdmittedFCFSSourceEndpointBatchTrace_filter_remotePredecessor_eq_chronological
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart) :
    (taggedAdmittedFCFSSourceEndpointBatchTrace resetTime 0 target z).filter
      (taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart) =
      taggedAdmittedChronologicalRemotePredecessorEndpointTrace
        resetTime target z remoteStart := by
  classical
  rw [taggedAdmittedFCFSSourceEndpointBatchTrace]
  rw [List.filter_map]
  have hpredicate :
      taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart ∘
        (fun eventTime : ℝ =>
          ({ eventTime := eventTime
             endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z eventTime } :
            TaggedAdmittedFiniteGPSTimedEndpointJobs Category)) =
      taggedAdmittedIsRemotePredecessorTime resetTime target z remoteStart := by
    funext eventTime
    exact taggedAdmittedIsRemotePredecessorEndpointBatch_mk_eq_time
      resetTime target z remoteStart eventTime
  rw [hpredicate]
  rw [taggedAdmittedBatchTimeTrace_filter_remotePredecessor_eq_chronological
    resetTime target z htarget_good remoteStart hcoverage]
  symm
  exact taggedAdmittedChronologicalRemotePredecessorEndpointTrace_eq_map_time
    resetTime target z remoteStart

/-- At a literal target predecessor epoch, strict target source order leaves
exactly that one target-class source job in the endpoint batch.  Simultaneous
passive jobs remain present in their own classes. -/
theorem taggedAdmittedFCFSJobsAt_target_predecessor_eq_singleton_sourceOrder
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart n : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (hn : n < remoteStart) :
    (taggedAdmittedFCFSJobsAt resetTime 0 target z
      (candidatePalmArrival z.1.1 (Int.negSucc n))).jobs target =
      [taggedAdmittedFCFSJob target z (target, Int.negSucc n)] := by
  have hindex : Int.negSucc n ∈
      taggedAdmittedArrivalIndicesBetween resetTime 0 target z target := by
    rw [taggedAdmittedTargetArrivalIndicesBetween_eq_range_image_of_pastWindowCoverage
      resetTime target z htarget_good remoteStart hcoverage]
    exact Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩
  have hindices : taggedAdmittedJobIndicesAt resetTime 0 target z
      (candidatePalmArrival z.1.1 (Int.negSucc n)) target = {Int.negSucc n} := by
    ext m
    rw [mem_taggedAdmittedJobIndicesAt_iff]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨_, htime⟩
      apply (suspensionGoodGapPath_strictMono z.1.1 htarget_good.1).injective
      simpa [taggedAdmittedSourceArrival] using htime
    · intro hm
      subst m
      refine ⟨hindex, ?_⟩
      simp [taggedAdmittedSourceArrival]
  change ((taggedAdmittedJobIndicesAt resetTime 0 target z
      (candidatePalmArrival z.1.1 (Int.negSucc n)) target).sort
      (fun left right : ℤ => left ≤ right)).map
      (fun m => taggedAdmittedFCFSJob target z (target, m)) = _
  rw [hindices]
  simp

/-- The `j`th canonical endpoint batch is the literal source batch at the
corresponding chronological target predecessor epoch. -/
theorem taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (j : Fin remoteStart) :
    (taggedAdmittedChronologicalRemotePredecessorEndpointTrace
      resetTime target z remoteStart)[j.1]'(by simpa [
        taggedAdmittedChronologicalRemotePredecessorEndpointTrace] using j.2) =
      ({ eventTime := taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j
         endpointJobs := taggedAdmittedFCFSJobsAt resetTime 0 target z
           (taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j) } :
        TaggedAdmittedFiniteGPSTimedEndpointJobs Category) := by
  simp [taggedAdmittedChronologicalRemotePredecessorEndpointTrace]

/-- The `j`th canonical endpoint retains its literal physical source epoch. -/
theorem taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem_eventTime
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) (j : Fin remoteStart) :
    ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
      resetTime target z remoteStart)[j.1]'(by simpa [
        taggedAdmittedChronologicalRemotePredecessorEndpointTrace] using j.2)).eventTime =
      taggedAdmittedChronologicalRemotePredecessorTime target z remoteStart j := by
  rw [taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem]

/-- The selected class list at each canonical retained endpoint is the
singleton literal predecessor job. -/
theorem taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem_targetJobs_eq_singleton
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (j : Fin remoteStart) :
    ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
      resetTime target z remoteStart)[j.1]'(by simpa [
        taggedAdmittedChronologicalRemotePredecessorEndpointTrace] using j.2)).endpointJobs.jobs target =
      [taggedAdmittedFCFSJob target z
        (target, Int.negSucc (taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j))] := by
  rw [taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem]
  exact taggedAdmittedFCFSJobsAt_target_predecessor_eq_singleton_sourceOrder
    resetTime target z htarget_good remoteStart
    (taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j)
    hcoverage (taggedAdmittedChronologicalRemotePredecessorIndex_lt remoteStart j)

/-- Every canonical retained endpoint satisfies the literal predecessor
filter. -/
theorem taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem_isRemotePredecessor
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart)
    (j : Fin remoteStart) :
    taggedAdmittedIsRemotePredecessorEndpointBatch target z remoteStart
      ((taggedAdmittedChronologicalRemotePredecessorEndpointTrace
        resetTime target z remoteStart)[j.1]'(by simpa [
          taggedAdmittedChronologicalRemotePredecessorEndpointTrace] using j.2)) = true := by
  apply (taggedAdmittedIsRemotePredecessorEndpointBatch_eq_true_iff
    target z remoteStart _).mpr
  refine ⟨taggedAdmittedChronologicalRemotePredecessorIndex remoteStart j,
    taggedAdmittedChronologicalRemotePredecessorIndex_lt remoteStart j, ?_⟩
  rw [taggedAdmittedChronologicalRemotePredecessorEndpointTrace_getElem_targetJobs_eq_singleton
    resetTime target z htarget_good remoteStart hcoverage j]
  simp

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
