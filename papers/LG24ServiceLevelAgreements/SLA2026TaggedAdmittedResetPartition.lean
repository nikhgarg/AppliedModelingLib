import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteExecution
import Mathlib.Tactic

/-!
# Reset-time partition of a tagged direct-admitted source trace

This module splits one finite literal target/passive source ledger at an
explicit reset time.  The source convention remains half-open throughout:
the prefix is `[start, resetTime)` and the suffix is
`[resetTime, horizon)`.  Consequently an actual arrival at the reset time is
in the suffix, never in the prefix; no stochastic assertion that such an
arrival is absent is used or needed.

Only finite source ledgers and their exact batch-time trace are partitioned.
The module does not add a GPS fence, prove a reset, construct stationarity,
or make a response-time or tail claim.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

omit [Fintype Category] in
/-- Each class's literal finite source-index ledger on `[start, horizon)` is
the disjoint union of the prefix `[start, resetTime)` and suffix
`[resetTime, horizon)` ledgers. -/
theorem taggedAdmittedArrivalIndicesBetween_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (k : Category) :
    taggedAdmittedArrivalIndicesBetween start horizon target z k =
      taggedAdmittedArrivalIndicesBetween start resetTime target z k ∪
        taggedAdmittedArrivalIndicesBetween resetTime horizon target z k := by
  ext n
  rw [mem_taggedAdmittedArrivalIndicesBetween_iff start horizon target z htarget_good,
    Finset.mem_union,
    mem_taggedAdmittedArrivalIndicesBetween_iff start resetTime target z htarget_good,
    mem_taggedAdmittedArrivalIndicesBetween_iff resetTime horizon target z htarget_good]
  constructor
  · rintro ⟨hstart, hhorizon⟩
    by_cases hbefore : taggedAdmittedSourceArrival target z (k, n) < resetTime
    · exact Or.inl ⟨hstart, hbefore⟩
    · exact Or.inr ⟨le_of_not_gt hbefore, hhorizon⟩
  · rintro (⟨hstart, hreset⟩ | ⟨hreset, hhorizon⟩)
    · exact ⟨hstart, hreset.trans_le hreset_horizon⟩
    · exact ⟨hstart_reset.trans hreset, hhorizon⟩

omit [Fintype Category] in
/-- The prefix and suffix class-index ledgers are disjoint.  This remains
true even when a literal source arrival is exactly at `resetTime`, because
the prefix has a strict right endpoint. -/
theorem taggedAdmittedArrivalIndicesBetween_reset_disjoint
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (k : Category) :
    Disjoint
      (taggedAdmittedArrivalIndicesBetween start resetTime target z k)
      (taggedAdmittedArrivalIndicesBetween resetTime horizon target z k) := by
  refine Finset.disjoint_left.mpr ?_
  intro n hprefix hsuffix
  have hprefix_interval :=
    (mem_taggedAdmittedArrivalIndicesBetween_iff start resetTime target z htarget_good k n).mp
      hprefix
  have hsuffix_interval :=
    (mem_taggedAdmittedArrivalIndicesBetween_iff resetTime horizon target z htarget_good k n).mp
      hsuffix
  linarith [hprefix_interval.2, hsuffix_interval.1]

omit [Fintype Category] in
/-- A literal source arrival at the reset time belongs to the suffix and not
the prefix whenever that time lies before the terminal horizon.  This is a
deterministic endpoint convention, not a no-arrival assumption. -/
theorem taggedAdmittedArrivalAtReset_mem_suffix_not_prefix
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hreset_horizon : resetTime < horizon)
    (k : Category) (n : ℤ)
    (harrival : taggedAdmittedSourceArrival target z (k, n) = resetTime) :
    n ∈ taggedAdmittedArrivalIndicesBetween resetTime horizon target z k ∧
      n ∉ taggedAdmittedArrivalIndicesBetween start resetTime target z k := by
  constructor
  · apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      resetTime horizon target z htarget_good k n).mpr
    simpa [harrival]
  · intro hprefix
    have hprefix_interval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        start resetTime target z htarget_good k n).mp hprefix
    linarith [hprefix_interval.2]

/-- The combined literal target/passive source-job ledger factors into its
disjoint prefix and suffix ledgers. -/
theorem taggedAdmittedSourceJobLedger_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    taggedAdmittedSourceJobLedger start horizon target z =
      taggedAdmittedSourceJobLedger start resetTime target z ∪
        taggedAdmittedSourceJobLedger resetTime horizon target z := by
  ext job
  rcases job with ⟨k, n⟩
  rw [mem_taggedAdmittedSourceJobLedger_iff,
    Finset.mem_union,
    mem_taggedAdmittedSourceJobLedger_iff,
    mem_taggedAdmittedSourceJobLedger_iff,
    taggedAdmittedArrivalIndicesBetween_reset_partition
      start resetTime horizon target z htarget_good hstart_reset hreset_horizon k]
  simp

/-- Prefix and suffix combined source-job ledgers are disjoint. -/
theorem taggedAdmittedSourceJobLedger_reset_disjoint
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) :
    Disjoint
      (taggedAdmittedSourceJobLedger start resetTime target z)
      (taggedAdmittedSourceJobLedger resetTime horizon target z) := by
  refine Finset.disjoint_left.mpr ?_
  intro job hprefix hsuffix
  rcases job with ⟨k, n⟩
  exact (Finset.disjoint_left.mp
    (taggedAdmittedArrivalIndicesBetween_reset_disjoint
      start resetTime horizon target z htarget_good k))
    ((mem_taggedAdmittedSourceJobLedger_iff start resetTime target z k n).mp hprefix)
    ((mem_taggedAdmittedSourceJobLedger_iff resetTime horizon target z k n).mp hsuffix)

/-- The exact physical batch-time set factors into disjoint prefix and suffix
sets.  Batches at `resetTime` are in the suffix set. -/
theorem taggedAdmittedBatchTimes_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    taggedAdmittedBatchTimes start horizon target z =
      taggedAdmittedBatchTimes start resetTime target z ∪
        taggedAdmittedBatchTimes resetTime horizon target z := by
  unfold taggedAdmittedBatchTimes
  rw [taggedAdmittedSourceJobLedger_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon,
    Finset.image_union]

/-- Prefix and suffix exact batch-time sets are disjoint without any
assumption excluding an arrival at the reset time. -/
theorem taggedAdmittedBatchTimes_reset_disjoint
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) :
    Disjoint
      (taggedAdmittedBatchTimes start resetTime target z)
      (taggedAdmittedBatchTimes resetTime horizon target z) := by
  refine Finset.disjoint_left.mpr ?_
  intro eventTime hprefix hsuffix
  rcases (mem_taggedAdmittedBatchTimes_iff start resetTime target z eventTime).mp hprefix with
    ⟨prefixJob, hprefixJob, hprefixTime⟩
  rcases (mem_taggedAdmittedBatchTimes_iff resetTime horizon target z eventTime).mp hsuffix with
    ⟨suffixJob, hsuffixJob, hsuffixTime⟩
  have hprefix_interval :=
    (mem_taggedAdmittedSourceJobLedger_interval_iff
      start resetTime target z htarget_good prefixJob).mp hprefixJob
  have hsuffix_interval :=
    (mem_taggedAdmittedSourceJobLedger_interval_iff
      resetTime horizon target z htarget_good suffixJob).mp hsuffixJob
  rw [hprefixTime] at hprefix_interval
  rw [hsuffixTime] at hsuffix_interval
  linarith [hprefix_interval.2, hsuffix_interval.1]

/-- Every prefix batch time is strictly before the reset time. -/
theorem taggedAdmittedBatchTimes_prefix_lt_reset
    (start resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (eventTime : ℝ)
    (heventTime : eventTime ∈ taggedAdmittedBatchTimes start resetTime target z) :
    eventTime < resetTime := by
  rcases (mem_taggedAdmittedBatchTimes_iff start resetTime target z eventTime).mp heventTime with
    ⟨job, hjob, htime⟩
  rw [← htime]
  exact (mem_taggedAdmittedSourceJobLedger_interval_iff
    start resetTime target z htarget_good job).mp hjob |>.2

/-- Every suffix batch time is at or after the reset time. -/
theorem taggedAdmittedBatchTimes_suffix_ge_reset
    (resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (eventTime : ℝ)
    (heventTime : eventTime ∈ taggedAdmittedBatchTimes resetTime horizon target z) :
    resetTime ≤ eventTime := by
  rcases (mem_taggedAdmittedBatchTimes_iff resetTime horizon target z eventTime).mp heventTime with
    ⟨job, hjob, htime⟩
  rw [← htime]
  exact (mem_taggedAdmittedSourceJobLedger_interval_iff
    resetTime horizon target z htarget_good job).mp hjob |>.1

omit [Fintype Category] in
/-- At a physical epoch strictly before the reset time, filtering the full
class ledger for that epoch gives exactly the prefix ledger's filter. -/
theorem taggedAdmittedArrivalIndicesBetween_filter_eq_prefix_of_lt_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hreset_horizon : resetTime ≤ horizon)
    (eventTime : ℝ) (heventTime : eventTime < resetTime) (k : Category) :
    (taggedAdmittedArrivalIndicesBetween start horizon target z k).filter
        (fun n => taggedAdmittedSourceArrival target z (k, n) = eventTime) =
      (taggedAdmittedArrivalIndicesBetween start resetTime target z k).filter
        (fun n => taggedAdmittedSourceArrival target z (k, n) = eventTime) := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hfull, harrival⟩
    refine ⟨?_, harrival⟩
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        start horizon target z htarget_good k n).mp hfull
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      start resetTime target z htarget_good k n).mpr
    refine ⟨?_, ?_⟩
    · simpa [harrival] using hinterval.1
    · simpa [harrival] using heventTime
  · rintro ⟨hprefix, harrival⟩
    refine ⟨?_, harrival⟩
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        start resetTime target z htarget_good k n).mp hprefix
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      start horizon target z htarget_good k n).mpr
    exact ⟨hinterval.1, hinterval.2.trans_le hreset_horizon⟩

omit [Fintype Category] in
/-- At a physical epoch at or after the reset time, filtering the full class
ledger gives exactly the suffix ledger's filter. -/
theorem taggedAdmittedArrivalIndicesBetween_filter_eq_suffix_of_reset_le
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime)
    (eventTime : ℝ) (heventTime : resetTime ≤ eventTime) (k : Category) :
    (taggedAdmittedArrivalIndicesBetween start horizon target z k).filter
        (fun n => taggedAdmittedSourceArrival target z (k, n) = eventTime) =
      (taggedAdmittedArrivalIndicesBetween resetTime horizon target z k).filter
        (fun n => taggedAdmittedSourceArrival target z (k, n) = eventTime) := by
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hfull, harrival⟩
    refine ⟨?_, harrival⟩
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        start horizon target z htarget_good k n).mp hfull
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      resetTime horizon target z htarget_good k n).mpr
    refine ⟨?_, ?_⟩
    · simpa [harrival] using heventTime
    · simpa [harrival] using hinterval.2
  · rintro ⟨hsuffix, harrival⟩
    refine ⟨?_, harrival⟩
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        resetTime horizon target z htarget_good k n).mp hsuffix
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      start horizon target z htarget_good k n).mpr
    exact ⟨hstart_reset.trans hinterval.1, hinterval.2⟩

omit [Fintype Category] in
/-- The aggregate batch vector at an epoch strictly before the reset is the
same whether computed from the full source ledger or the prefix ledger. -/
theorem taggedAdmittedBatchAt_eq_prefix_of_lt_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hreset_horizon : resetTime ≤ horizon)
    (eventTime : ℝ) (heventTime : eventTime < resetTime) :
    taggedAdmittedBatchAt start horizon target z eventTime =
      taggedAdmittedBatchAt start resetTime target z eventTime := by
  funext k
  unfold taggedAdmittedBatchAt
  rw [taggedAdmittedArrivalIndicesBetween_filter_eq_prefix_of_lt_reset
    start resetTime horizon target z htarget_good hreset_horizon eventTime heventTime k]

omit [Fintype Category] in
/-- The aggregate batch vector at an epoch at or after the reset is the same
whether computed from the full source ledger or the suffix ledger. -/
theorem taggedAdmittedBatchAt_eq_suffix_of_reset_le
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime)
    (eventTime : ℝ) (heventTime : resetTime ≤ eventTime) :
    taggedAdmittedBatchAt start horizon target z eventTime =
      taggedAdmittedBatchAt resetTime horizon target z eventTime := by
  funext k
  unfold taggedAdmittedBatchAt
  rw [taggedAdmittedArrivalIndicesBetween_filter_eq_suffix_of_reset_le
    start resetTime horizon target z htarget_good hstart_reset eventTime heventTime k]

/-- The chronological finite tagged source trace factors at an explicit reset
time into the prefix trace followed by the suffix trace.  The proof uses only
the literal half-open source ledgers, so no assumption excluding arrivals at
the reset time is needed. -/
theorem taggedAdmittedBatchTimeTrace_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    taggedAdmittedBatchTimeTrace start horizon target z =
      taggedAdmittedBatchTimeTrace start resetTime target z ++
        taggedAdmittedBatchTimeTrace resetTime horizon target z := by
  let fullTimes := taggedAdmittedBatchTimes start horizon target z
  let prefixTimes := taggedAdmittedBatchTimes start resetTime target z
  let suffixTimes := taggedAdmittedBatchTimes resetTime horizon target z
  have hset_partition : fullTimes = prefixTimes ∪ suffixTimes := by
    simpa [fullTimes, prefixTimes, suffixTimes] using
      (taggedAdmittedBatchTimes_reset_partition
        start resetTime horizon target z htarget_good hstart_reset hreset_horizon)
  have hset_disjoint : Disjoint prefixTimes suffixTimes := by
    simpa [prefixTimes, suffixTimes] using
      (taggedAdmittedBatchTimes_reset_disjoint
        start resetTime horizon target z htarget_good)
  have hconcat_pairwise :
      List.Pairwise (fun left right : ℝ => left ≤ right)
        ((prefixTimes.sort (fun left right : ℝ => left ≤ right)) ++
          (suffixTimes.sort (fun left right : ℝ => left ≤ right))) := by
    rw [List.pairwise_append]
    refine ⟨Finset.pairwise_sort prefixTimes (fun left right : ℝ => left ≤ right),
      Finset.pairwise_sort suffixTimes (fun left right : ℝ => left ≤ right), ?_⟩
    intro left hleft right hright
    have hleft_set : left ∈ prefixTimes :=
      (Finset.mem_sort (fun x y : ℝ => x ≤ y)).mp hleft
    have hright_set : right ∈ suffixTimes :=
      (Finset.mem_sort (fun x y : ℝ => x ≤ y)).mp hright
    have hleft_lt : left < resetTime := by
      simpa [prefixTimes] using
        (taggedAdmittedBatchTimes_prefix_lt_reset
          start resetTime target z htarget_good left hleft_set)
    have hright_ge : resetTime ≤ right := by
      simpa [suffixTimes] using
        (taggedAdmittedBatchTimes_suffix_ge_reset
          resetTime horizon target z htarget_good right hright_set)
    exact hleft_lt.le.trans hright_ge
  have htrace_disjoint :
      List.Disjoint
        (prefixTimes.sort (fun left right : ℝ => left ≤ right))
        (suffixTimes.sort (fun left right : ℝ => left ≤ right)) := by
    rw [List.disjoint_left]
    intro eventTime hprefix hsuffix
    apply (Finset.disjoint_left.mp hset_disjoint)
    · exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp hprefix
    · exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp hsuffix
  have hconcat_nodup :
      ((prefixTimes.sort (fun left right : ℝ => left ≤ right)) ++
        (suffixTimes.sort (fun left right : ℝ => left ≤ right))).Nodup :=
    List.Nodup.append
      (Finset.sort_nodup prefixTimes (fun left right : ℝ => left ≤ right))
      (Finset.sort_nodup suffixTimes (fun left right : ℝ => left ≤ right))
      htrace_disjoint
  have hconcat_toFinset :
      ((prefixTimes.sort (fun left right : ℝ => left ≤ right)) ++
        (suffixTimes.sort (fun left right : ℝ => left ≤ right))).toFinset =
        prefixTimes ∪ suffixTimes := by
    simp
  have hperm :
      List.Perm (fullTimes.sort (fun left right : ℝ => left ≤ right))
        ((prefixTimes.sort (fun left right : ℝ => left ≤ right)) ++
          (suffixTimes.sort (fun left right : ℝ => left ≤ right))) := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact Finset.sort_nodup fullTimes (fun left right : ℝ => left ≤ right)
    · exact hconcat_nodup
    · calc
        (fullTimes.sort (fun left right : ℝ => left ≤ right)).toFinset = fullTimes := by
          simp
        _ = prefixTimes ∪ suffixTimes := hset_partition
        _ = ((prefixTimes.sort (fun left right : ℝ => left ≤ right)) ++
            (suffixTimes.sort (fun left right : ℝ => left ≤ right))).toFinset :=
          hconcat_toFinset.symm
  have hfull_pairwise :
      List.Pairwise (fun left right : ℝ => left ≤ right)
        (fullTimes.sort (fun left right : ℝ => left ≤ right)) :=
    Finset.pairwise_sort fullTimes (fun left right : ℝ => left ≤ right)
  simpa [taggedAdmittedBatchTimeTrace, fullTimes, prefixTimes, suffixTimes] using
    hperm.eq_of_pairwise' hfull_pairwise hconcat_pairwise

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
