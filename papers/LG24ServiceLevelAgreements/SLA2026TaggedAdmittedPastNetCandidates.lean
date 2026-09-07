import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedBlockSourceRate
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteExecution
import Mathlib.Tactic

/-!
# Finite source-boundary candidates for the SLA tagged input

For one finite literal source window, this module reduces an arbitrary
continuous-time lower endpoint to the first actual source batch at or after
that endpoint, or to the terminal horizon when no such batch exists.  The
window convention is always `[start, horizon)`: a batch at the chosen
candidate is retained in the candidate's lower-inclusive ledger, and a
source arrival at the terminal horizon is outside the finite window.

This is a finite ledger/candidate reduction only.  It does not choose a
remote cutoff, prove a GPS reset, construct a stationary queue, or establish
a response or tail theorem.
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

/-- Total literal source work in a finite half-open target/passive ledger.
The definition remains class-indexed, which retains the exact target-Palm
and passive stationary enumerators used by the finite executor. -/
def taggedAdmittedSourceAggregateLedgerWork
    (start horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : Real :=
  Finset.univ.sum fun k : Category =>
    (taggedAdmittedArrivalIndicesBetween start horizon target z k).sum fun n =>
      taggedAdmittedSourceWork target z (k, n)

/-- Source net work after giving a finite physical-time window its full
aggregate capacity credit.  No scheduler state is involved in this scalar
source quantity. -/
def taggedAdmittedSourceNetWork
    (start horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real) : Real :=
  taggedAdmittedSourceAggregateLedgerWork start horizon target z -
    capacity * (horizon - start)

/-- The finite candidate list contains every real source batch in chronological
order and the terminal horizon.  The terminal point is a boundary candidate,
not a source batch or a computational GPS fence. -/
def taggedAdmittedPastBoundaryCandidates
    (start horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target) : List Real :=
  taggedAdmittedBatchTimeTrace start horizon target z ++ [horizon]

/-- At horizon zero, the aggregate finite executor ledger is exactly the
source-rate module's literal physical-time work ledger.  The target Palm tag
at zero is excluded on both sides, and all passive terms are retained through
their original stationary enumerators. -/
theorem stationaryAdmittedTargetPassivePastAggregateWork_eq_taggedLedger
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (t : Real) :
    stationaryAdmittedTargetPassivePastAggregateWork target z t =
      taggedAdmittedSourceAggregateLedgerWork (-t) 0 target z := by
  symm
  rw [taggedAdmittedSourceAggregateLedgerWork,
    Fintype.sum_eq_add_sum_subtype_ne
      (fun k : Category =>
        (taggedAdmittedArrivalIndicesBetween (-t) 0 target z k).sum fun n =>
          taggedAdmittedSourceWork target z (k, n)) target]
  congr 1
  · simp [taggedAdmittedArrivalIndicesBetween, taggedAdmittedSourceWork,
      stationaryAdmittedTargetPalmPastWindowLedgerWork,
      stationaryAdmittedTargetPalmPastWindowLedgerIndices]
  · apply Finset.sum_congr rfl
    intro k _
    simp [taggedAdmittedArrivalIndicesBetween, taggedAdmittedSourceWork,
      stationaryPoissonWorkPastAggregate, stationaryPoissonWorkRequirement, k.2]

/-- The literal past source net-work process is exactly the finite executor's
source net-work ledger at the corresponding physical lower endpoint. -/
theorem stationaryAdmittedTargetPassivePastAggregateNetWork_eq_taggedNetWork
    (start : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real) :
    stationaryAdmittedTargetPassivePastAggregateWork target z (-start) -
        capacity * (-start) =
      taggedAdmittedSourceNetWork start 0 target z capacity := by
  rw [stationaryAdmittedTargetPassivePastAggregateWork_eq_taggedLedger]
  simp [taggedAdmittedSourceNetWork]

/-- If no actual finite source batch lies from `u` (inclusive) to `r`
(exclusive), then each class's literal suffix ledger from `u` equals its
literal suffix ledger from `r`.  In particular, a batch exactly at `r` stays
in both ledgers, as required by the lower-inclusive endpoint convention. -/
theorem taggedAdmittedArrivalIndicesBetween_eq_of_no_batch_between
    (start u r horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_u : start ≤ u) (hu_r : u ≤ r) (hr_horizon : r ≤ horizon)
    (hno_batch : ∀ eventTime,
      eventTime ∈ taggedAdmittedBatchTimeTrace start horizon target z →
      u ≤ eventTime → eventTime < r → False)
    (k : Category) :
    taggedAdmittedArrivalIndicesBetween u horizon target z k =
      taggedAdmittedArrivalIndicesBetween r horizon target z k := by
  ext n
  constructor
  · intro hmem
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        u horizon target z htarget_good k n).mp hmem
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      r horizon target z htarget_good k n).mpr
    refine ⟨?_, hinterval.2⟩
    by_contra hnot
    have harrival_lt_r : taggedAdmittedSourceArrival target z (k, n) < r :=
      lt_of_not_ge hnot
    have hfull_mem : n ∈
        taggedAdmittedArrivalIndicesBetween start horizon target z k :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        start horizon target z htarget_good k n).mpr
        ⟨hstart_u.trans hinterval.1, hinterval.2⟩
    have hjob_mem : (k, n) ∈
        taggedAdmittedSourceJobLedger start horizon target z :=
      taggedAdmittedSourceJob_mem_ledger start horizon target z k n hfull_mem
    have hbatch_mem : taggedAdmittedSourceArrival target z (k, n) ∈
        taggedAdmittedBatchTimeTrace start horizon target z := by
      apply (Finset.mem_sort (fun s t : Real => s ≤ t)).mpr
      exact (mem_taggedAdmittedBatchTimes_iff
        start horizon target z (taggedAdmittedSourceArrival target z (k, n))).mpr
        ⟨(k, n), hjob_mem, rfl⟩
    exact hno_batch _ hbatch_mem hinterval.1 harrival_lt_r
  · intro hmem
    have hinterval :=
      (mem_taggedAdmittedArrivalIndicesBetween_iff
        r horizon target z htarget_good k n).mp hmem
    apply (mem_taggedAdmittedArrivalIndicesBetween_iff
      u horizon target z htarget_good k n).mpr
    exact ⟨hu_r.trans hinterval.1, hinterval.2⟩

/-- The no-batch condition gives an exact equality of the total literal
target/passive source work in the two suffix windows. -/
theorem taggedAdmittedSourceAggregateLedgerWork_eq_of_no_batch_between
    (start u r horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_u : start ≤ u) (hu_r : u ≤ r) (hr_horizon : r ≤ horizon)
    (hno_batch : ∀ eventTime,
      eventTime ∈ taggedAdmittedBatchTimeTrace start horizon target z →
      u ≤ eventTime → eventTime < r → False) :
    taggedAdmittedSourceAggregateLedgerWork u horizon target z =
      taggedAdmittedSourceAggregateLedgerWork r horizon target z := by
  unfold taggedAdmittedSourceAggregateLedgerWork
  apply Finset.sum_congr rfl
  intro k _
  rw [taggedAdmittedArrivalIndicesBetween_eq_of_no_batch_between
    start u r horizon target z htarget_good hstart_u hu_r hr_horizon hno_batch k]

/-- If aggregate capacity is nonnegative, moving the lower endpoint forward
through a source-free interval can only increase the source net-work value.
The candidate endpoint retains its own batch because the ledger is
lower-inclusive. -/
theorem taggedAdmittedSourceNetWork_le_of_no_batch_between
    (start u r horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hcapacity_nonneg : 0 ≤ capacity)
    (hstart_u : start ≤ u) (hu_r : u ≤ r) (hr_horizon : r ≤ horizon)
    (hno_batch : ∀ eventTime,
      eventTime ∈ taggedAdmittedBatchTimeTrace start horizon target z →
      u ≤ eventTime → eventTime < r → False) :
    taggedAdmittedSourceNetWork u horizon target z capacity ≤
      taggedAdmittedSourceNetWork r horizon target z capacity := by
  unfold taggedAdmittedSourceNetWork
  rw [taggedAdmittedSourceAggregateLedgerWork_eq_of_no_batch_between
    start u r horizon target z htarget_good hstart_u hu_r hr_horizon hno_batch]
  have hcredit : 0 ≤ capacity * (r - u) :=
    mul_nonneg hcapacity_nonneg (sub_nonneg.mpr hu_r)
  linarith

/-- Every finite continuous-time lower endpoint has a first real source-batch
boundary at or after it, unless there is no remaining source batch, in which
case the terminal horizon is selected.  No actual batch lies in the half-open
gap `[u,r)`. -/
theorem exists_taggedAdmittedBoundaryCandidate
    (start u horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_u : start ≤ u) (hu_horizon : u ≤ horizon) :
    ∃ r,
      (r ∈ taggedAdmittedBatchTimeTrace start horizon target z ∨ r = horizon) ∧
        u ≤ r ∧ r ≤ horizon ∧
        ∀ eventTime,
          eventTime ∈ taggedAdmittedBatchTimeTrace start horizon target z →
          u ≤ eventTime → eventTime < r → False := by
  let futureTimes : Finset Real :=
    (taggedAdmittedBatchTimes start horizon target z).filter fun eventTime =>
      u ≤ eventTime
  by_cases hfuture : futureTimes.Nonempty
  · let r := futureTimes.min' hfuture
    have hr_filter : r ∈ futureTimes := Finset.min'_mem futureTimes hfuture
    have hr_batch : r ∈ taggedAdmittedBatchTimes start horizon target z :=
      (Finset.mem_filter.mp hr_filter).1
    have hu_r : u ≤ r := (Finset.mem_filter.mp hr_filter).2
    have hr_trace : r ∈ taggedAdmittedBatchTimeTrace start horizon target z :=
      (Finset.mem_sort (fun s t : Real => s ≤ t)).mpr hr_batch
    refine ⟨r, Or.inl hr_trace, hu_r, ?_, ?_⟩
    · exact (taggedAdmittedExternalBatchTrace_time_lt_horizon
        start horizon target z htarget_good r (by
          simpa [taggedAdmittedExternalBatchTrace] using hr_trace)).le
    · intro eventTime heventTime hu_eventTime heventTime_lt_r
      have heventTime_batch : eventTime ∈
          taggedAdmittedBatchTimes start horizon target z :=
        (Finset.mem_sort (fun s t : Real => s ≤ t)).mp heventTime
      have heventTime_future : eventTime ∈ futureTimes :=
        Finset.mem_filter.mpr ⟨heventTime_batch, hu_eventTime⟩
      exact (not_lt_of_ge
        (Finset.min'_le futureTimes eventTime heventTime_future)) heventTime_lt_r
  · refine ⟨horizon, Or.inr rfl, hu_horizon, le_rfl, ?_⟩
    intro eventTime heventTime hu_eventTime _
    apply hfuture
    refine ⟨eventTime, Finset.mem_filter.mpr ?_⟩
    exact ⟨(Finset.mem_sort (fun s t : Real => s ≤ t)).mp heventTime,
      hu_eventTime⟩

/-- Finite source-boundary reduction for the scalar net-work path: every
continuous-time lower endpoint is dominated by a real batch boundary or the
terminal horizon.  The candidate list is the actual chronological source
trace with only its terminal boundary appended. -/
theorem exists_taggedAdmittedBoundaryCandidate_net_dominating
    (start u horizon : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hcapacity_nonneg : 0 ≤ capacity)
    (hstart_u : start ≤ u) (hu_horizon : u ≤ horizon) :
    ∃ r,
      r ∈ taggedAdmittedPastBoundaryCandidates start horizon target z ∧
        u ≤ r ∧ r ≤ horizon ∧
        taggedAdmittedSourceNetWork u horizon target z capacity ≤
          taggedAdmittedSourceNetWork r horizon target z capacity := by
  rcases exists_taggedAdmittedBoundaryCandidate
    start u horizon target z htarget_good hstart_u hu_horizon with
      ⟨r, hcandidate, hu_r, hr_horizon, hno_batch⟩
  refine ⟨r, ?_, hu_r, hr_horizon, ?_⟩
  · simpa [taggedAdmittedPastBoundaryCandidates] using hcandidate
  · exact taggedAdmittedSourceNetWork_le_of_no_batch_between
      start u r horizon target z capacity htarget_good hcapacity_nonneg
      hstart_u hu_r hr_horizon hno_batch

/-- At horizon zero, the finite source-boundary reduction applies directly to
the physical past process `A([-t,0)) - C t`: every lower endpoint `u` is
dominated by a literal source-batch lower endpoint or by zero itself.  A
batch selected at `r` is included in the `[-r,0)` ledger; zero is merely the
terminal boundary and the Palm tag at zero remains excluded. -/
theorem exists_taggedAdmittedPastBoundaryCandidate_net_dominating
    (start u : Real) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (capacity : Real)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hcapacity_nonneg : 0 ≤ capacity)
    (hstart_u : start ≤ u) (hu_zero : u ≤ 0) :
    ∃ r,
      r ∈ taggedAdmittedPastBoundaryCandidates start 0 target z ∧
        u ≤ r ∧ r ≤ 0 ∧
        stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
            capacity * (-u) ≤
          stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
            capacity * (-r) := by
  rcases exists_taggedAdmittedBoundaryCandidate_net_dominating
    start u 0 target z capacity htarget_good hcapacity_nonneg hstart_u hu_zero with
      ⟨r, hcandidate, hu_r, hr_zero, hnet⟩
  refine ⟨r, hcandidate, hu_r, hr_zero, ?_⟩
  calc
    stationaryAdmittedTargetPassivePastAggregateWork target z (-u) -
        capacity * (-u) =
        taggedAdmittedSourceNetWork u 0 target z capacity :=
      stationaryAdmittedTargetPassivePastAggregateNetWork_eq_taggedNetWork
        u target z capacity
    _ ≤ taggedAdmittedSourceNetWork r 0 target z capacity := hnet
    _ = stationaryAdmittedTargetPassivePastAggregateWork target z (-r) -
        capacity * (-r) :=
      (stationaryAdmittedTargetPassivePastAggregateNetWork_eq_taggedNetWork
        r target z capacity).symm

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
