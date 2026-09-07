import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFSFrontWorkOrder
import LG24ServiceLevelAgreements.SLA2026TargetMM1ComparatorResponse
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSFCFS
import Mathlib.Tactic

/-!
# Literal target-source order around the Palm tag

This module isolates the source-order facts needed by the finite GPS versus
target-only FCFS comparison.  A remote start is described by the target source
jobs that actually lie in the half-open interval `[r, 0)`: `r` may be a
passive-source boundary, so it is not forced to be a target arrival epoch.
The target tag itself is excluded from that past ledger and is appended only
at its real zero-time endpoint after the preceding segment's service.

No GPS/comparator domination is claimed here.  That dynamic inequality must
still be proved from the concrete GPS service-floor trace.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- A remote start `N` exactly covers the literal target arrivals in the
physical half-open window `[resetTime, 0)`.  It is intentionally stated by
source epochs rather than requiring `resetTime` itself to be a target batch:
the global GPS reset may occur at a passive-source boundary. -/
def TaggedAdmittedTargetPastWindowCoversRemoteStart
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) : Prop :=
  ∀ n : Nat,
    resetTime ≤ candidatePalmArrival z.1.1 (Int.negSucc n) ↔ n < remoteStart

/-- On a good Palm target path, there is a genuine future target source epoch
strictly after every finite physical time.  This is a source-time fact: it
does not introduce a computational fence or select a queue completion. -/
theorem exists_taggedAdmittedFutureTargetSourceArrival_gt
    (target : Category) (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1) (time : ℝ) :
    ∃ n : ℕ,
      time < taggedAdmittedSourceArrival target z
        (target, Int.ofNat (n + 1)) := by
  rcases exists_arrivalTime_gt_of_tendsto_atTop
      (suspensionFuturePath z.1.1)
      (suspensionGoodGapPath_future z.1.1 htarget_good.1) time with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [taggedAdmittedSourceArrival, candidatePalmArrival_ofNat,
    candidateFutureEpoch_succ_eq_arrivalTime_suspension] using hn

/-- Under the literal source-window coverage condition, the target jobs in
`[resetTime, 0)` are exactly the remote-past labels replayed by the finite
target comparator.  The left endpoint is included, so a target batch at the
reset time is retained; the tag at time zero is excluded by the right-open
interval. -/
theorem taggedAdmittedTargetArrivalIndicesBetween_eq_range_image_of_pastWindowCoverage
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (remoteStart : Nat)
    (hcoverage : TaggedAdmittedTargetPastWindowCoversRemoteStart
      resetTime target z remoteStart) :
    taggedAdmittedArrivalIndicesBetween resetTime 0 target z target =
      (Finset.range remoteStart).image Int.negSucc := by
  ext i
  rw [mem_taggedAdmittedArrivalIndicesBetween_iff
    resetTime 0 target z htarget_good target i]
  simp only [taggedAdmittedSourceArrival]
  change
    resetTime ≤ candidatePalmArrival z.1.1 i ∧
        candidatePalmArrival z.1.1 i < 0 ↔
      i ∈ (Finset.range remoteStart).image Int.negSucc
  let hstrict := suspensionGoodGapPath_strictMono z.1.1 htarget_good.1
  constructor
  · rintro ⟨hlower, hupper⟩
    have hi_neg : i < 0 := by
      by_contra hnot
      have hzero_le : (0 : Int) ≤ i := le_of_not_gt hnot
      have harrival : candidatePalmArrival z.1.1 0 ≤ candidatePalmArrival z.1.1 i :=
        hstrict.monotone hzero_le
      rw [htarget_good.2] at harrival
      linarith
    rcases Int.eq_negSucc_of_lt_zero hi_neg with ⟨n, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨n, ?_, rfl⟩
    exact Finset.mem_range.mpr ((hcoverage n).mp hlower)
  · rintro hmem
    rcases Finset.mem_image.mp hmem with ⟨n, hn, rfl⟩
    constructor
    · exact (hcoverage n).mpr (Finset.mem_range.mp hn)
    · have harrival := hstrict (Int.negSucc_lt_zero n)
      rw [htarget_good.2] at harrival
      exact harrival

/-- The selected target's physical zero-time endpoint batch contains exactly
one target-class job.  Other categories may have simultaneous source batches,
but they are not in this FCFS class queue; strict target source order rules
out an additional target job tied with the Palm tag. -/
theorem taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon) :
    (taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target =
      [taggedAdmittedFCFSJob target z (target, 0)] := by
  have hstrict := suspensionGoodGapPath_strictMono z.1.1 htarget_good.1
  have hindices : taggedAdmittedJobIndicesAt start horizon target z 0 target = {0} := by
    ext n
    rw [mem_taggedAdmittedJobIndicesAt_iff]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨_hn, htime⟩
      apply hstrict.injective
      calc
        candidatePalmArrival z.1.1 n = 0 := by
          simpa [taggedAdmittedSourceArrival] using htime
        _ = candidatePalmArrival z.1.1 0 := htarget_good.2.symm
    · intro hn
      subst n
      refine ⟨?_, taggedAdmittedSourceArrival_target_zero target z⟩
      exact (mem_taggedAdmittedSourceJobLedger_iff start horizon target z target 0).mp
        ((mem_taggedAdmittedTargetSourceId_iff start horizon target z htarget_good).mpr
          ⟨hstart, hhorizon⟩)
  change
    ((taggedAdmittedJobIndicesAt start horizon target z 0 target).sort
      (fun left right : ℤ => left ≤ right)).map
        (fun n => taggedAdmittedFCFSJob target z (target, n)) =
      [taggedAdmittedFCFSJob target z (target, 0)]
  rw [hindices]
  simp

/-- The finite target-only comparator numerator is the literal target
pre-tag replay plus the selected source job's own work.  This is kept in work
units so a GPS front-work inequality does not need to divide by a rate. -/
def stationaryAdmittedTargetPalmFiniteComparatorNumerator
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) : ℝ :=
  stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
      target serviceRate z remoteStart +
    stationaryAdmittedTargetPalmWorkAtZero target z

/-- The finite comparator response is exactly its work numerator divided by
the declared constant service rate. -/
theorem stationaryAdmittedTargetPalmFiniteComparatorResponse_eq_numerator_div
    (target : Category) (serviceRate : ℝ)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (remoteStart : Nat) :
    stationaryAdmittedTargetPalmFiniteComparatorResponse
      target serviceRate z remoteStart =
      stationaryAdmittedTargetPalmFiniteComparatorNumerator
        target serviceRate z remoteStart / serviceRate := by
  rfl

/-- At the actual zero-time target endpoint, FCFS applies the concrete
preceding segment's service before appending the singleton Palm tag.  If that
post-service queue does not already contain the tag, its front work is the
remaining target work plus the tag's literal source work.  This is an exact
ordering identity, not the later GPS-versus-comparator inequality. -/
theorem taggedAdmittedTargetFrontWork_after_zero_source_endpoint_eq
    (start horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart : start ≤ 0) (hhorizon : 0 < horizon)
    (ledger : FiniteGPSFCFSJobLedger Category (TaggedAdmittedSourceJobId Category))
    (segment : FiniteGPSExecutionSegment Category)
    (hserved_no_tag : ∀ earlier ∈
      finiteGPSFCFSConsume (segment.serviceIncrement target) (ledger.residualJobs target),
      decide (earlier.identifier = (target, 0)) ≠ true) :
    finiteGPSFCFSFrontWork
        (fun identifier : TaggedAdmittedSourceJobId Category =>
          decide (identifier = (target, 0)))
        ((finiteGPSFCFSApplySegment ledger segment
          (taggedAdmittedFCFSJobsAt start horizon target z 0)).residualJobs target) =
      some
        (finiteGPSFCFSJobWork
          (finiteGPSFCFSConsume (segment.serviceIncrement target)
            (ledger.residualJobs target)) +
          stationaryAdmittedTargetPalmWorkAtZero target z) := by
  have hendpoint : (taggedAdmittedFCFSJobsAt start horizon target z 0).jobs target =
      [taggedAdmittedFCFSJob target z (target, 0)] :=
    taggedAdmittedFCFSJobsAt_target_zero_eq_singleton
      start horizon target z htarget_good hstart hhorizon
  have hfront := finiteGPSFCFSFrontWork_applySegment_singleton_endpoint_eq
    (fun identifier : TaggedAdmittedSourceJobId Category =>
      decide (identifier = (target, 0)))
    ledger segment (taggedAdmittedFCFSJobsAt start horizon target z 0) target
    (taggedAdmittedFCFSJob target z (target, 0)) hendpoint hserved_no_tag (by simp)
  simpa [taggedAdmittedFCFSJob, stationaryAdmittedTargetPalmWorkAtZero,
    stationaryAdmittedTargetPalmWorkPath] using hfront

/-- A strictly ordered target Palm path whose remote starts diverge to the
past has a first target predecessor strictly before any fixed physical reset
time.  Its index gives the exact half-open target-source window used by a
finite comparator replay.  In particular, the reset may be a passive-source
boundary: no target arrival at `resetTime` is required, while one at that
time is included because the window is lower-inclusive. -/
theorem exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_tendsto
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (hstrict : StrictMono (candidatePalmArrival z.1.1))
    (hlimit : Filter.Tendsto
      (fun n : Nat => -stationaryAdmittedTargetPalmPastStart target z n)
      Filter.atTop Filter.atTop) :
    ∃ remoteStart,
      TaggedAdmittedTargetPastWindowCoversRemoteStart
        resetTime target z remoteStart := by
  have hlimit' : Filter.Tendsto
      (fun n : Nat => -candidatePalmArrival z.1.1 (Int.negSucc n))
      Filter.atTop Filter.atTop := by
    simpa [stationaryAdmittedTargetPalmPastStart] using hlimit
  have hpast : ∃ n : Nat,
      candidatePalmArrival z.1.1 (Int.negSucc n) < resetTime := by
    rcases (hlimit'.eventually_gt_atTop (-resetTime)).exists with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    linarith
  let remoteStart := Nat.find hpast
  refine ⟨remoteStart, ?_⟩
  intro n
  constructor
  · intro hreset_le_arrival
    by_contra hnot_lt
    have hremote_le_n : remoteStart ≤ n := Nat.le_of_not_gt hnot_lt
    have harrival_le :
        candidatePalmArrival z.1.1 (Int.negSucc n) ≤
          candidatePalmArrival z.1.1 (Int.negSucc remoteStart) := by
      by_cases heq : n = remoteStart
      · subst n
        exact le_rfl
      · have hremote_lt_n : remoteStart < n :=
          lt_of_le_of_ne hremote_le_n (Ne.symm heq)
        have hindex : Int.negSucc n < Int.negSucc remoteStart := by
          simp only [Int.negSucc_eq]
          omega
        exact (hstrict hindex).le
    have hremote_before :
        candidatePalmArrival z.1.1 (Int.negSucc remoteStart) < resetTime :=
      Nat.find_spec hpast
    linarith
  · intro hn_lt
    apply le_of_not_gt
    intro hn_before
    have hremote_le_n : remoteStart ≤ n := Nat.find_min' hpast hn_before
    exact (not_le_of_gt hn_lt) hremote_le_n

/-- The target Palm good carrier supplies the strict source order needed by
the preceding threshold construction. -/
theorem exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_goodCarrier_and_tendsto
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hlimit : Filter.Tendsto
      (fun n : Nat => -stationaryAdmittedTargetPalmPastStart target z n)
      Filter.atTop Filter.atTop) :
    ∃ remoteStart,
      TaggedAdmittedTargetPastWindowCoversRemoteStart
        resetTime target z remoteStart := by
  exact exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_tendsto
    resetTime target z
    (suspensionGoodGapPath_strictMono z.1.1 htarget_good.1) hlimit

/-- For every fixed reset time, the direct target-Palm source almost surely
has a finite remote comparator start whose literal target jobs are exactly
the half-open interval from that reset to the Palm tag.  This is stronger
than the reset-time-at-most-zero use case and does not make any queue-state
or GPS comparison claim. -/
theorem ae_exists_taggedAdmittedTargetPastWindowCoversRemoteStart
    (M : SLA2026BoroughQueueingInput Category) (target : Category)
    (resetTime : ℝ) :
    ∀ᵐ z ∂(M.stationaryAdmittedTargetPassiveTaggedInput target).Ptag,
      ∃ remoteStart,
        TaggedAdmittedTargetPastWindowCoversRemoteStart
          resetTime target z remoteStart := by
  filter_upwards [M.ae_stationaryAdmittedTargetPassivePalmGoodCarrier target,
    M.ae_tendsto_neg_stationaryAdmittedTargetPalmPastStart_atTop target]
    with z htarget_good hlimit
  exact exists_taggedAdmittedTargetPastWindowCoversRemoteStart_of_goodCarrier_and_tendsto
    resetTime target z htarget_good hlimit

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
