import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateProjection
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSConstantRateComparison
import Mathlib.Tactic

/-!
# Literal-target projection certificate for the closed LG24 GPS trace

The executable tagged GPS ledger contains more endpoints than the target
arrival ledger: internal depletion endpoints and passive-source batches are
real service intervals, but are not target arrivals.  This file records the
precise source-facing certificate required to project the former to the
latter.

The certificate deliberately selects retained entries by literal target source
epochs, not by nonzero target work.  A target arrival whose exponential mark
happens to be zero is still retained.  Conversely, the terminal zero-batch
block represents service from the final target predecessor through the Palm
tag at physical time zero; it is not a fabricated source arrival.

This is a finite, pathwise interface.  It does not assert existence of the
certificate from the raw segment list: constructing it requires the
source-labelled external-endpoint partition proved by the adjacent source
adapter.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The target predecessor held at chronological retained position `j` of a
remote history of length `remoteStart`.  Thus position zero is the oldest
predecessor and position `remoteStart - 1` is the immediate predecessor.
This is a source-label index, not a test on a numerical work mark. -/
def taggedAdmittedChronologicalRemoteIndex
    (remoteStart : Nat) (j : Fin remoteStart) : Nat :=
  remoteStart - (j.1 + 1)

/-- A source-facing semantic certificate that the exact closed pre-tag GPS
segment ledger can be grouped into literal target-arrival blocks.

`block j` contains every selected-class-zero concrete segment after the
previous retained target epoch and before the next one, followed by the
actual segment ending at that next target epoch.  `terminalZero` contains all
remaining concrete segments after the immediate target predecessor, including
the computational horizon fence to time zero. -/
structure TaggedAdmittedClosedPreTagProjectionCertificate
    (resetTime : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight : Category → ℝ)
    (remoteStart : Nat) where
  /-- One retained source-epoch block for each literal target predecessor in
  chronological order.  The retained endpoint is kept even when its target
  work mark is zero. -/
  block : Fin remoteStart → FiniteGPSConstantRateProjectionBlock Category
  /-- The service-only suffix after the last retained target predecessor. -/
  terminalZero : List (FiniteGPSExecutionSegment Category)
  /-- Erasing the source annotation expands to exactly the closed executable
  segment history. -/
  projection_segments_eq :
    finiteGPSConstantRateProjectionSegments (List.ofFn block) terminalZero =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments
  /-- The retained endpoints are exactly the literal target source epochs in
  the physical window.  This is the zero-mark safeguard: selection is by
  source time and external-endpoint status, never by `endpointBatch ≠ 0`. -/
  literal_target_epoch_iff_retained :
    ∀ segment ∈ finiteGPSConstantRateProjectionSegments (List.ofFn block) terminalZero,
      (∃ n : Nat, n < remoteStart ∧
        segment.endpointIsExternalBatch = true ∧
        finiteGPSExecutionSegmentEndTime segment =
          candidatePalmArrival z.1.1 (Int.negSucc n)) ↔
        ∃ j : Fin remoteStart, segment = (block j).retained
  /-- The concrete selected-class batch at each retained source endpoint is
  the direct comparator's literal predecessor work mark. -/
  retained_target_batch : ∀ j : Fin remoteStart,
    (block j).retained.endpointBatch target =
      stationaryAdmittedTargetPalmRemotePastBatch target z
        (taggedAdmittedChronologicalRemoteIndex remoteStart j)
  /-- The retained endpoint's physical time is its named target predecessor
  epoch. -/
  retained_end_time : ∀ j : Fin remoteStart,
    finiteGPSExecutionSegmentEndTime (block j).retained =
      candidatePalmArrival z.1.1
        (Int.negSucc (taggedAdmittedChronologicalRemoteIndex remoteStart j))
  /-- Every prefix endpoint is semantically target-empty.  It may be an
  internal depletion or a passive external source batch. -/
  zero_prefix_target_batch : ∀ (j : Fin remoteStart) (segment : FiniteGPSExecutionSegment Category),
    segment ∈ (block j).zeroPrefix → segment.endpointBatch target = 0
  /-- The final source-to-tag service suffix is target-empty.  In particular,
  the endpoint at physical zero is the computational fence rather than a
  fake source batch. -/
  terminal_zero_target_batch : ∀ segment ∈ terminalZero,
    segment.endpointBatch target = 0
  /-- The executor emitted only nonnegative-time intervals. -/
  duration_nonneg : ∀ segment ∈
    finiteGPSConstantRateProjectionSegments (List.ofFn block) terminalZero,
    0 ≤ segment.duration
  /-- The initial target block starts at the actual physical reset, which may
  be a passive-source boundary.  Its duration is deliberately retained even
  though an empty scalar target queue makes its service algebraically inert. -/
  first_block_duration : ∀ j : Fin remoteStart, j.1 = 0 →
    finiteGPSConstantRateProjectionBlockDuration (block j) =
      candidatePalmArrival z.1.1
        (Int.negSucc (taggedAdmittedChronologicalRemoteIndex remoteStart j)) - resetTime
  /-- Every later target block spans the physical interval from the preceding
  retained target source epoch to the next one. -/
  later_block_duration : ∀ j : Fin remoteStart, 0 < j.1 →
    finiteGPSConstantRateProjectionBlockDuration (block j) =
      candidatePalmArrival z.1.1
        (Int.negSucc (taggedAdmittedChronologicalRemoteIndex remoteStart j)) -
      candidatePalmArrival z.1.1
        (Int.negSucc (remoteStart - j.1))
  /-- The terminal zero block is the actual physical service interval to the
  Palm tag.  With no retained predecessor it instead spans the whole reset to
  tag interval. -/
  terminal_zero_duration :
    finiteGPSExecutionSegmentsTotalDuration terminalZero =
      if remoteStart = 0 then 0 - resetTime else
        0 - candidatePalmArrival z.1.1 (Int.negSucc 0)

namespace TaggedAdmittedClosedPreTagProjectionCertificate

variable {resetTime : ℝ} {target : Category}
  {z : StationaryAdmittedTargetPassiveTaggedInput target}
  {htarget_good : palmTaggedArrivalGoodCarrier z.1.1}
  {capacity : ℝ} {weight : Category → ℝ} {remoteStart : Nat}
  (certificate : TaggedAdmittedClosedPreTagProjectionCertificate
    resetTime target z htarget_good capacity weight remoteStart)

/-- The certificate's expanded ledger is exactly the literal closed source
segment ledger, stated in the direction needed by the scalar comparator
bridge. -/
theorem projection_segments_eq_closed_history :
    finiteGPSConstantRateProjectionSegments (List.ofFn certificate.block)
      certificate.terminalZero =
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments :=
  certificate.projection_segments_eq

/-- The semantic certificate provides the exact zero-prefix premise required
by the source-agnostic projection algebra. -/
theorem all_zero_prefix_target_batch : ∀ block ∈ List.ofFn certificate.block,
    ∀ segment ∈ block.zeroPrefix, segment.endpointBatch target = 0 := by
  intro block hblock segment hsegment
  rw [List.mem_ofFn] at hblock
  rcases hblock with ⟨j, rfl⟩
  exact certificate.zero_prefix_target_batch j segment hsegment

/-- The executor duration invariant restricts to every retained target
endpoint. -/
theorem retained_duration_nonneg : ∀ block ∈ List.ofFn certificate.block,
    0 ≤ block.retained.duration := by
  intro block hblock
  rw [List.mem_ofFn] at hblock
  rcases hblock with ⟨j, rfl⟩
  apply certificate.duration_nonneg (certificate.block j).retained
  simp only [finiteGPSConstantRateProjectionSegments, List.mem_append,
    List.mem_flatMap, finiteGPSConstantRateProjectionBlockSegments]
  exact Or.inl ⟨certificate.block j, List.mem_ofFn.mpr ⟨j, rfl⟩, Or.inr (by simp)⟩

/-- The executor duration invariant restricts to every zero-prefix segment. -/
theorem zero_prefix_duration_nonneg : ∀ block ∈ List.ofFn certificate.block,
    ∀ segment ∈ block.zeroPrefix, 0 ≤ segment.duration := by
  intro block hblock segment hsegment
  rw [List.mem_ofFn] at hblock
  rcases hblock with ⟨j, rfl⟩
  apply certificate.duration_nonneg segment
  simp only [finiteGPSConstantRateProjectionSegments, List.mem_append,
    List.mem_flatMap, finiteGPSConstantRateProjectionBlockSegments]
  exact Or.inl ⟨certificate.block j, List.mem_ofFn.mpr ⟨j, rfl⟩, Or.inl hsegment⟩

/-- The executor duration invariant restricts to the service-only terminal
suffix. -/
theorem terminal_zero_duration_nonneg : ∀ segment ∈ certificate.terminalZero,
    0 ≤ segment.duration := by
  intro segment hsegment
  apply certificate.duration_nonneg segment
  simp only [finiteGPSConstantRateProjectionSegments, List.mem_append]
  exact Or.inr hsegment

/-- The terminal service-only block has nonnegative total elapsed duration.
This is derived from the concrete executable intervals rather than assumed as
a property of a synthetic final arrival. -/
theorem terminal_zero_total_duration_nonneg :
    0 ≤ finiteGPSExecutionSegmentsTotalDuration certificate.terminalZero := by
  unfold finiteGPSExecutionSegmentsTotalDuration
  apply List.sum_nonneg
  intro duration hduration
  rcases List.mem_map.mp hduration with ⟨segment, hsegment, rfl⟩
  exact certificate.terminal_zero_duration_nonneg segment hsegment

/-- Each retained literal target work mark is nonnegative under the explicit
source work condition.  This does not turn a zero mark into a non-arrival. -/
theorem retained_target_batch_nonneg
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    ∀ block ∈ List.ofFn certificate.block, 0 ≤ block.retained.endpointBatch target := by
  intro block hblock
  rw [List.mem_ofFn] at hblock
  rcases hblock with ⟨j, rfl⟩
  rw [certificate.retained_target_batch]
  rw [← taggedAdmittedSourceWork_target_negSucc_eq_remotePastBatch]
  exact taggedAdmittedSourceWork_nonneg target z hsource_work_nonneg
    (target, Int.negSucc (taggedAdmittedChronologicalRemoteIndex remoteStart j))

/-- The source-specific certificate, plus the generic semantic projection
lemma, identifies the scalar comparator over the exact closed executable
ledger with its target-epoch projection.  No target arrival is inferred from
a nonzero batch mark. -/
theorem constant_rate_closed_segment_comparator_eq_projection
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hrate_nonneg : 0 ≤ capacity * weight target) :
    finiteGPSConstantRateSegmentComparator (capacity * weight target) target
      (taggedAdmittedFiniteGPSClosedPreTagHistory
        resetTime 0 target z htarget_good capacity weight).segments =
      finiteGPSConstantRateProjectionComparatorFrom 0
        (capacity * weight target) target
        (List.ofFn certificate.block) certificate.terminalZero := by
  rw [← certificate.projection_segments_eq]
  exact finiteGPSConstantRateSegmentComparatorFrom_eq_projectionComparatorFrom
    0 (capacity * weight target) target
    (List.ofFn certificate.block) certificate.terminalZero
    (by norm_num) hrate_nonneg
    certificate.zero_prefix_duration_nonneg
    certificate.retained_duration_nonneg
    certificate.terminal_zero_duration_nonneg
    certificate.all_zero_prefix_target_batch
    certificate.terminal_zero_target_batch
    (certificate.retained_target_batch_nonneg hsource_work_nonneg)

/-- Once a source adapter has identified the retained literal-target blocks
with a chronological scalar replay, the projection comparator is exactly the
corresponding finite Lindley pre-batch workload.  The final service-only
suffix remains an actual reflected service update; this theorem never turns
it into an arrival at time zero.

The replay equality is deliberately an explicit premise.  Its proof is the
source-provenance obligation: it must establish the order of literal source
labels and their physical interarrival durations, including zero-work target
marks.  Keeping it visible prevents a scalar equality from silently assuming
that nonzero target batch work identifies an arrival. -/
theorem projection_comparator_eq_lateBatchPreWorkload_of_retainedReplay
    (rate : ℝ) (i : Category)
    (firstService : ℝ) (batch service : Nat → ℝ)
    (hretainedReplay :
      finiteGPSConstantRateProjectionRetainedReplaySteps rate i
        (List.ofFn certificate.block) =
        lateBatchChronologicalReplaySteps firstService batch service remoteStart)
    (hrate_nonneg : 0 ≤ rate)
    (hfirstService_nonneg : 0 ≤ firstService)
    (hterminalService_eq_final_of_succ : ∀ n, remoteStart = n + 1 →
      rate * finiteGPSExecutionSegmentsTotalDuration certificate.terminalZero =
        service n) :
    finiteGPSConstantRateProjectionComparatorFrom 0 rate i
      (List.ofFn certificate.block) certificate.terminalZero =
      lateBatchPreWorkload batch service remoteStart := by
  apply finiteGPSConstantRateProjectionComparatorFrom_eq_lateBatchPreWorkload_of_retainedReplay_eq
    rate i certificate.block certificate.terminalZero firstService batch service
    hretainedReplay hfirstService_nonneg
  · intro _
    exact mul_nonneg hrate_nonneg certificate.terminal_zero_total_duration_nonneg
  · exact hterminalService_eq_final_of_succ

/-- Source-specialized form of the preceding scalar bridge.  It identifies
the terminal service-only suffix with the actual interval from the immediate
target predecessor to the Palm tag, while the retained-replay premise records
the independently audited source-label ordering for all earlier blocks. -/
theorem projection_comparator_eq_stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
    (firstService : ℝ)
    (hretainedReplay :
      finiteGPSConstantRateProjectionRetainedReplaySteps
        (capacity * weight target) target (List.ofFn certificate.block) =
        lateBatchChronologicalReplaySteps firstService
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
          (reverseRemotePastIncrement
            (stationaryAdmittedTargetPalmRemotePastService
              target (capacity * weight target) z) remoteStart)
          remoteStart)
    (hrate_nonneg : 0 ≤ capacity * weight target)
    (hfirstService_nonneg : 0 ≤ firstService) :
    finiteGPSConstantRateProjectionComparatorFrom 0
      (capacity * weight target) target
      (List.ofFn certificate.block) certificate.terminalZero =
      stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload
        target (capacity * weight target) z remoteStart := by
  rw [stationaryAdmittedTargetPalmFiniteComparatorPreTagWorkload]
  apply certificate.projection_comparator_eq_lateBatchPreWorkload_of_retainedReplay
    (capacity * weight target) target firstService
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastBatch target z) remoteStart)
    (reverseRemotePastIncrement
      (stationaryAdmittedTargetPalmRemotePastService
        target (capacity * weight target) z) remoteStart)
    hretainedReplay hrate_nonneg hfirstService_nonneg
  intro n hremoteStart
  have hterminal_duration :
      finiteGPSExecutionSegmentsTotalDuration certificate.terminalZero =
        0 - candidatePalmArrival z.1.1 (Int.negSucc 0) := by
    rw [certificate.terminal_zero_duration]
    simp [hremoteStart]
  calc
    (capacity * weight target) *
        finiteGPSExecutionSegmentsTotalDuration certificate.terminalZero =
        (capacity * weight target) *
          (0 - candidatePalmArrival z.1.1 (Int.negSucc 0)) := by
      rw [hterminal_duration]
    _ = stationaryAdmittedTargetPalmRemotePastService
        target (capacity * weight target) z 0 := by
      symm
      exact stationaryAdmittedTargetPalmRemotePastService_zero_eq_rate_mul_tag_sub_predecessor
        target (capacity * weight target) z
    _ = reverseRemotePastIncrement
        (stationaryAdmittedTargetPalmRemotePastService
          target (capacity * weight target) z) remoteStart n := by
      simp [reverseRemotePastIncrement, hremoteStart]

end TaggedAdmittedClosedPreTagProjectionCertificate

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
