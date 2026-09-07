import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SuffixCreditReset
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedClosedRunRestart
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGlobalPastCutoff
import Mathlib.Tactic

/-!
# Literal global-past reset for the tagged admitted GPS source

This module turns the literal physical-time global aggregate net-work cutoff
into an executable finite GPS reset.  The prefix is always `[start, r)` and
is closed at `r` only by the explicitly computational zero-work fence.  A
literal source batch at `r` remains in the source suffix; when `r = 0`, the
selected Palm request at zero is also outside the prefix.

The proof uses the sorted source trace only to establish an exact semantic
identity between each chronological trace suffix and its literal half-open
source ledger.  It does not move positive work to an endpoint or identify a
computational fence with a source arrival.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability
open AppliedModelingLib.Probability.Palm
open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory BigOperators

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- Summing the aggregate work of the literal chronological source batches
recovers the class-indexed half-open source ledger exactly. -/
theorem sum_taggedAdmittedBatchTimeTrace_aggregateBatchAt_eq_totalAggregateLedgerWork
    (start horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) :
    ((taggedAdmittedBatchTimeTrace start horizon target z).map
      (fun t => finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z t))).sum =
      taggedAdmittedSourceAggregateLedgerWork start horizon target z := by
  have hinterchange : ∀ times : List Real,
      (times.map fun t => finiteGPSAggregateWork
        (taggedAdmittedBatchAt start horizon target z t)).sum =
        ∑ k : Category, (times.map fun t =>
          taggedAdmittedBatchAt start horizon target z t k).sum := by
    intro times
    induction times with
    | nil => simp
    | cons t ts ih =>
        simp only [List.map_cons, List.sum_cons]
        calc
          finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z t) +
              (ts.map fun u => finiteGPSAggregateWork
                (taggedAdmittedBatchAt start horizon target z u)).sum =
              finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z t) +
                ∑ k : Category, (ts.map fun u =>
                  taggedAdmittedBatchAt start horizon target z u k).sum := by rw [ih]
          _ = (∑ k : Category, taggedAdmittedBatchAt start horizon target z t k) +
                ∑ k : Category, (ts.map fun u =>
                  taggedAdmittedBatchAt start horizon target z u k).sum := by
              rfl
          _ = ∑ k : Category, (taggedAdmittedBatchAt start horizon target z t k +
                (ts.map fun u => taggedAdmittedBatchAt start horizon target z u k).sum) := by
              rw [Finset.sum_add_distrib]
  calc
    ((taggedAdmittedBatchTimeTrace start horizon target z).map
        (fun t => finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z t))).sum =
        ∑ k : Category, ((taggedAdmittedBatchTimeTrace start horizon target z).map
          fun t => taggedAdmittedBatchAt start horizon target z t k).sum :=
      hinterchange _
    _ = taggedAdmittedSourceAggregateLedgerWork start horizon target z := by
      unfold taggedAdmittedSourceAggregateLedgerWork
      apply Finset.sum_congr rfl
      intro k _
      exact sum_taggedAdmittedBatchTimeTrace_batchAt_eq_totalLedgerWork
        start horizon target z k

/-- If a sorted literal source trace is split before an actual source batch,
then the suffix beginning at that batch is exactly the source trace generated
with that batch time as its lower-inclusive endpoint. -/
theorem taggedAdmittedBatchTimeTrace_suffix_eq_of_append
    (start horizon t : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (before tail : List Real)
    (htrace : taggedAdmittedBatchTimeTrace start horizon target z =
      before ++ t :: tail) :
    taggedAdmittedBatchTimeTrace t horizon target z = t :: tail := by
  let fullTimes := taggedAdmittedBatchTimes start horizon target z
  let suffixTimes := taggedAdmittedBatchTimes t horizon target z
  have hfull_pairwise : List.Pairwise (fun x y : Real => x ≤ y)
      (before ++ t :: tail) := by
    rw [← htrace]
    exact Finset.pairwise_sort fullTimes (fun x y : Real => x ≤ y)
  have htarget_pairwise : List.Pairwise (fun x y : Real => x ≤ y) (t :: tail) := by
    apply List.Pairwise.sublist (List.sublist_append_right before (t :: tail))
    exact hfull_pairwise
  have hfull_nodup : (before ++ t :: tail).Nodup := by
    rw [← htrace]
    exact Finset.sort_nodup fullTimes (fun x y : Real => x ≤ y)
  have htarget_nodup : (t :: tail).Nodup :=
    List.Nodup.sublist (List.sublist_append_right before (t :: tail)) hfull_nodup
  have hbefore_lt : ∀ u ∈ before, u < t := by
    intro u hu
    have hle : u ≤ t :=
      (List.pairwise_append.mp hfull_pairwise).2.2 u hu t (by simp)
    have hne : u ≠ t :=
      (List.nodup_append.mp hfull_nodup).2.2 u hu t (by simp)
    exact lt_of_le_of_ne hle hne
  have htail_ge : ∀ u ∈ t :: tail, t ≤ u := by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu_tail
    · exact le_rfl
    · exact (List.pairwise_cons.mp htarget_pairwise).1 u hu_tail
  have hstart_t : start ≤ t := by
    have ht_mem : t ∈ taggedAdmittedBatchTimeTrace start horizon target z := by
      rw [htrace]
      simp
    exact finiteGPSChronologicalFrom_start_le start
      (taggedAdmittedBatchTimeTrace start horizon target z)
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
      t ht_mem
  have hset : (taggedAdmittedBatchTimeTrace t horizon target z).toFinset =
      (t :: tail).toFinset := by
    ext u
    simp only [List.mem_toFinset]
    constructor
    · intro hu
      have hu_batch : u ∈ suffixTimes := by
        simpa [suffixTimes] using (Finset.mem_sort (fun x y : Real => x ≤ y)).mp hu
      rcases (mem_taggedAdmittedBatchTimes_iff t horizon target z u).mp hu_batch with
        ⟨job, hjob, harrival⟩
      have hinterval := (mem_taggedAdmittedSourceJobLedger_interval_iff
        t horizon target z htarget_good job).mp hjob
      have hjob_full : job ∈ taggedAdmittedSourceJobLedger start horizon target z := by
        apply (mem_taggedAdmittedSourceJobLedger_interval_iff
          start horizon target z htarget_good job).mpr
        exact ⟨hstart_t.trans hinterval.1, hinterval.2⟩
      have hu_full : u ∈ taggedAdmittedBatchTimeTrace start horizon target z := by
        apply (Finset.mem_sort (fun x y : Real => x ≤ y)).mpr
        apply (mem_taggedAdmittedBatchTimes_iff start horizon target z u).mpr
        exact ⟨job, hjob_full, harrival⟩
      rw [htrace] at hu_full
      rcases List.mem_append.mp hu_full with hu_before | hu_suffix
      · have hu_lt := hbefore_lt u hu_before
        have hu_ge : t ≤ u := by simpa [← harrival] using hinterval.1
        exact False.elim (not_lt_of_ge hu_ge hu_lt)
      · exact hu_suffix
    · intro hu
      have hu_full : u ∈ taggedAdmittedBatchTimeTrace start horizon target z := by
        rw [htrace]
        exact List.mem_append.mpr (Or.inr hu)
      have hu_batch_full : u ∈ fullTimes := by
        simpa [fullTimes] using (Finset.mem_sort (fun x y : Real => x ≤ y)).mp hu_full
      rcases (mem_taggedAdmittedBatchTimes_iff start horizon target z u).mp hu_batch_full with
        ⟨job, hjob, harrival⟩
      have hinterval := (mem_taggedAdmittedSourceJobLedger_interval_iff
        start horizon target z htarget_good job).mp hjob
      have hu_ge : t ≤ u := htail_ge u hu
      have hjob_suffix : job ∈ taggedAdmittedSourceJobLedger t horizon target z := by
        apply (mem_taggedAdmittedSourceJobLedger_interval_iff
          t horizon target z htarget_good job).mpr
        exact ⟨by simpa [← harrival] using hu_ge, hinterval.2⟩
      apply (Finset.mem_sort (fun x y : Real => x ≤ y)).mpr
      apply (mem_taggedAdmittedBatchTimes_iff t horizon target z u).mpr
      exact ⟨job, hjob_suffix, harrival⟩
  have hperm : (taggedAdmittedBatchTimeTrace t horizon target z).Perm (t :: tail) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup suffixTimes (fun x y : Real => x ≤ y)
    · exact htarget_nodup
    · simpa [suffixTimes] using hset
  have hsuffix_pairwise : List.Pairwise (fun x y : Real => x ≤ y)
      (taggedAdmittedBatchTimeTrace t horizon target z) :=
    Finset.pairwise_sort suffixTimes (fun x y : Real => x ≤ y)
  exact hperm.eq_of_pairwise' hsuffix_pairwise htarget_pairwise

/-- At every literal source-trace suffix, the aggregate batch total is
exactly the lower-inclusive source ledger from the suffix's first batch. -/
theorem taggedAdmittedSourceAggregateLedgerWork_eq_head_add_tail_batchAggregate_of_append
    (start horizon t : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (before tail : List Real)
    (htrace : taggedAdmittedBatchTimeTrace start horizon target z =
      before ++ t :: tail) :
    taggedAdmittedSourceAggregateLedgerWork t horizon target z =
      finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z t) +
        (tail.map fun u =>
          finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z u)).sum := by
  have ht_full : t ∈ taggedAdmittedBatchTimeTrace start horizon target z := by
    rw [htrace]
    simp
  have hstart_t : start ≤ t := by
    exact finiteGPSChronologicalFrom_start_le start
      (taggedAdmittedBatchTimeTrace start horizon target z)
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
      t ht_full
  have hsuffix := taggedAdmittedBatchTimeTrace_suffix_eq_of_append
    start horizon t target z htarget_good before tail htrace
  have hsum := sum_taggedAdmittedBatchTimeTrace_aggregateBatchAt_eq_totalAggregateLedgerWork
    t horizon target z
  rw [hsuffix] at hsum
  have hchrono_suffix : FiniteGPSChronologicalFrom t tail := by
    have hchrono : FiniteGPSChronologicalFrom t (t :: tail) := by
      rw [← hsuffix]
      exact (taggedAdmittedExternalBatchTrace
        t horizon target z htarget_good).chronological
    exact hchrono.2
  have hmap :
      ((t :: tail).map fun u =>
        finiteGPSAggregateWork (taggedAdmittedBatchAt t horizon target z u)) =
      ((t :: tail).map fun u =>
        finiteGPSAggregateWork (taggedAdmittedBatchAt start horizon target z u)) := by
    apply List.map_congr_left
    intro u hu
    congr 1
    exact (taggedAdmittedBatchAt_eq_suffix_of_reset_le
      start t horizon target z htarget_good hstart_t u
      (by
        rcases List.mem_cons.mp hu with rfl | hu_tail
        · exact le_rfl
        · exact finiteGPSChronologicalFrom_start_le t tail hchrono_suffix u hu_tail)).symm
  rw [hmap] at hsum
  simpa using hsum.symm

/-- A global physical-time net-work maximum gives the semantic suffix-credit
condition consumed by the executable finite GPS reset criterion. -/
theorem taggedAdmittedBatchTrace_suffix_credit_of_pastGlobalMax
    (start resetTime : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_zero : resetTime ≤ 0)
    (hglobal : ∀ u : Real, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          capacity * (-resetTime))
    (before : List Real) (t : Real) (tail : List Real)
    (htrace : taggedAdmittedBatchTimeTrace start resetTime target z =
      before ++ t :: tail) :
    finiteGPSAggregateWork (taggedAdmittedBatchAt start resetTime target z t) +
      (tail.map fun u =>
        finiteGPSAggregateWork (taggedAdmittedBatchAt start resetTime target z u)).sum ≤
        capacity * (resetTime - t) := by
  have ht_mem : t ∈ taggedAdmittedBatchTimeTrace start resetTime target z := by
    rw [htrace]
    simp
  have ht_reset : t ≤ resetTime :=
    (taggedAdmittedExternalBatchTrace_time_lt_horizon
      start resetTime target z htarget_good t (by
        simpa [taggedAdmittedExternalBatchTrace] using ht_mem)).le
  have hnet := taggedAdmittedSourceNetWork_prefix_le_zero_of_pastGlobalMax
    resetTime t target z capacity htarget_good ht_reset hreset_zero hglobal
  rw [show taggedAdmittedSourceNetWork t resetTime target z capacity =
      taggedAdmittedSourceAggregateLedgerWork t resetTime target z -
        capacity * (resetTime - t) by rfl,
    taggedAdmittedSourceAggregateLedgerWork_eq_head_add_tail_batchAggregate_of_append
      start resetTime t target z htarget_good before tail htrace] at hnet
  linarith

/-- The literal selected global source cutoff gives an actual all-class empty
state after closing the half-open source prefix by its computational
zero-work fence.  A source batch at the cutoff remains outside that prefix. -/
theorem taggedAdmittedFiniteGPSRun_all_work_eq_zero_of_pastGlobalMax
    (start resetTime : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category → Real)
    (hstart_reset : start ≤ resetTime) (hreset_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hglobal : ∀ u : Real, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          capacity * (-resetTime)) :
    ∀ i,
      (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good capacity weight
        (fun _ => 0) hstart_reset).workload i = 0 := by
  have htrace_credit :
      ((taggedAdmittedBatchTimeTrace start resetTime target z).map
          (fun t => finiteGPSAggregateWork
            (taggedAdmittedBatchAt start resetTime target z t))).sum ≤
        capacity * (resetTime - start) := by
    have hnet := taggedAdmittedSourceNetWork_prefix_le_zero_of_pastGlobalMax
      resetTime start target z capacity htarget_good hstart_reset hreset_zero hglobal
    rw [show taggedAdmittedSourceNetWork start resetTime target z capacity =
        taggedAdmittedSourceAggregateLedgerWork start resetTime target z -
          capacity * (resetTime - start) by rfl,
      ← sum_taggedAdmittedBatchTimeTrace_aggregateBatchAt_eq_totalAggregateLedgerWork
        start resetTime target z] at hnet
    linarith
  have hclosed := finiteGPSCloseAtHorizon_all_work_eq_zero_of_suffix_credit
    capacity weight (fun _ => 0)
    (taggedAdmittedBatchAt start resetTime target z) start resetTime
    (taggedAdmittedBatchTimeTrace start resetTime target z)
    hcapacity hweight_pos htotal_weight_le_one (by intro k; norm_num)
    (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).chronological
    hstart_reset
    (by
      intro t ht
      exact taggedAdmittedExternalBatchTrace_time_lt_horizon
        start resetTime target z htarget_good t (by
          simpa [taggedAdmittedExternalBatchTrace] using ht))
    (by
      intro t _ k
      exact taggedAdmittedBatchAt_nonneg start resetTime target z hsource_work_nonneg t k)
    (by simpa [finiteGPSAggregateWork] using htrace_credit)
    (by
      intro before t tail htrace
      exact taggedAdmittedBatchTrace_suffix_credit_of_pastGlobalMax
        start resetTime target z capacity htarget_good hstart_reset hreset_zero hglobal
        before t tail htrace)
  simpa [taggedAdmittedFiniteGPSRun, taggedAdmittedFiniteGPSPreTerminalRun,
    finiteGPSRunExternalBatchTrace] using hclosed

/-- The full literal run through the Palm epoch factors at the selected
global cutoff through an actual closed zero state.  The source suffix begins
at the cutoff itself, so this equality never deletes a simultaneous source
batch. -/
theorem taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_pastGlobalMax
    (start resetTime : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : Real) (weight : Category → Real)
    (hstart_reset : start ≤ resetTime) (hreset_zero : resetTime ≤ 0)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ k, 0 < weight k)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hglobal : ∀ u : Real, u ≤ 0 →
      stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
          capacity * (-u) ≤
        stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
          capacity * (-resetTime)) :
    taggedAdmittedFiniteGPSRun start 0 target z htarget_good capacity weight (fun _ => 0)
        (hstart_reset.trans hreset_zero) =
      { workload :=
          (taggedAdmittedFiniteGPSRun resetTime 0 target z htarget_good capacity weight
            (fun _ => 0) hreset_zero).workload
        currentTime :=
          (taggedAdmittedFiniteGPSRun resetTime 0 target z htarget_good capacity weight
            (fun _ => 0) hreset_zero).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good capacity weight
            (fun _ => 0) hstart_reset).service i +
          (taggedAdmittedFiniteGPSRun resetTime 0 target z htarget_good capacity weight
            (fun _ => 0) hreset_zero).service i } := by
  apply taggedAdmittedFiniteGPSRun_eq_closed_prefix_then_closed_source_suffix_of_closed_prefix_workload_zero
    start resetTime 0 target z htarget_good capacity weight (fun _ => 0)
    hstart_reset hreset_zero hcapacity hweight_pos htotal_weight_le_one
    (by intro k; norm_num) hsource_work_nonneg
  exact taggedAdmittedFiniteGPSRun_all_work_eq_zero_of_pastGlobalMax
    start resetTime target z htarget_good capacity weight hstart_reset hreset_zero
    hcapacity hweight_pos htotal_weight_le_one hsource_work_nonneg hglobal

/-- Under the paper's aggregate slack parameters, almost every literal
target-Palm source input has a finite physical source boundary whose closed
prefix is empty in every GPS class.  The boundary is either an actual source
batch epoch or the terminal Palm boundary zero; it is not a scheduler-made
arrival. -/
theorem ae_exists_taggedAdmittedPastGlobalClosedPrefix
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ htarget_good : palmTaggedArrivalGoodCarrier z.1.1,
        ∃ hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z,
          ∃ start resetTime, ∃ hstart_reset : start ≤ resetTime,
            start ≤ 0 ∧
              resetTime ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
              resetTime ≤ 0 ∧
              ∀ i,
                (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                  G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0 := by
  filter_upwards [
    M.ae_exists_taggedAdmittedPastGlobalNetCutoff G target,
    M.ae_taggedAdmittedFiniteExecutionInputGood target] with z hcut hgood
  rcases hcut with ⟨start, resetTime, hstart_zero, hboundary,
    hstart_reset, hreset_zero, hglobal⟩
  refine ⟨hgood.1, hgood.2, start, resetTime, hstart_reset, hstart_zero, hboundary,
    hreset_zero, ?_⟩
  intro i
  exact taggedAdmittedFiniteGPSRun_all_work_eq_zero_of_pastGlobalMax
    start resetTime target z hgood.1 G.capacity G.weight hstart_reset hreset_zero
    (G.capacity_pos target) (G.weight_pos) G.total_weight_le_one hgood.2 hglobal i

/-- The global-reset construction with the physical net-work maximizer
retained.  Keeping this source-side certificate visible is essential for
canonical remote-past replays: it proves that every sufficiently remote
diagonal prefix, rather than merely one chosen prefix, reaches the same
empty state at `resetTime`. -/
theorem ae_exists_taggedAdmittedPastGlobalClosedPrefix_with_globalMax
    (M : SLA2026BoroughQueueingInput Category)
    (G : SLA2026BoroughGPSParameters M) (target : Category) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ htarget_good : palmTaggedArrivalGoodCarrier z.1.1,
        ∃ hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z,
          ∃ start resetTime, ∃ hstart_reset : start ≤ resetTime,
            start ≤ 0 ∧
              resetTime ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
              resetTime ≤ 0 ∧
              (∀ u : Real, u ≤ 0 →
                stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
                    G.capacity * (-u) ≤
                  stationaryAdmittedTargetPassivePastAggregateWork target z (-resetTime) -
                    G.capacity * (-resetTime)) ∧
              ∀ i,
                (taggedAdmittedFiniteGPSRun start resetTime target z htarget_good
                  G.capacity G.weight (fun _ => 0) hstart_reset).workload i = 0 := by
  filter_upwards [
    M.ae_exists_taggedAdmittedPastGlobalNetCutoff G target,
    M.ae_taggedAdmittedFiniteExecutionInputGood target] with z hcut hgood
  rcases hcut with ⟨start, resetTime, hstart_zero, hboundary,
    hstart_reset, hreset_zero, hglobal⟩
  refine ⟨hgood.1, hgood.2, start, resetTime, hstart_reset, hstart_zero,
    hboundary, hreset_zero, hglobal, ?_⟩
  intro i
  exact taggedAdmittedFiniteGPSRun_all_work_eq_zero_of_pastGlobalMax
    start resetTime target z hgood.1 G.capacity G.weight hstart_reset hreset_zero
    (G.capacity_pos target) (G.weight_pos) G.total_weight_le_one hgood.2 hglobal i

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
