import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateRefinement
import Mathlib.Tactic

/-!
# Zero-batch compression for service-before-endpoint GPS comparators

The finite executable GPS trace has more endpoints than a chosen class's
arrival trace.  In particular, an internal depletion event and an external
arrival for another class both have a zero endpoint batch for the chosen
class.  Those endpoints cannot simply be deleted: their elapsed service must
remain before the next retained selected-class batch.

This module supplies the deterministic algebra for that operation.  It works
with arbitrary concrete `FiniteGPSExecutionSegment` values and inspects only
the selected class's stored endpoint batches and elapsed durations.  It makes
no claim about how the segments were generated, their event names, a source
process, a GPS path comparison, or a stochastic tail law.

The key API removes an arbitrary contiguous selected-class-zero block
immediately before a retained endpoint, accumulating the block's service into
that endpoint's preceding service interval.  A separate suffix theorem keeps
the final zero-batch service interval rather than silently discarding it.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The scalar service-before-endpoint comparator composes over chronological
segment-list concatenation.  This is purely the recursive fold identity and
does not require a GPS-chain certificate. -/
theorem finiteGPSConstantRateSegmentComparatorFrom_append
    (initial rate : Real) (i : Class)
    (left right : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i (left ++ right) =
      finiteGPSConstantRateSegmentComparatorFrom
        (finiteGPSConstantRateSegmentComparatorFrom initial rate i left)
        rate i right := by
  induction left generalizing initial with
  | nil =>
      simp [finiteGPSConstantRateSegmentComparatorFrom]
  | cons segment left ih =>
      simp only [List.cons_append, finiteGPSConstantRateSegmentComparatorFrom]
      exact ih (initial := lateBatchUpdate initial
        (rate * segment.duration) (segment.endpointBatch i))

/-- The scalar comparator remains nonnegative whenever its initial work and
the selected-class endpoint batches are nonnegative.  No condition on the
service values is needed: reflection occurs before every endpoint batch. -/
theorem finiteGPSConstantRateSegmentComparatorFrom_nonneg
    (initial rate : Real) (i : Class)
    (segments : List (FiniteGPSExecutionSegment Class))
    (hinitial_nonneg : 0 <= initial)
    (hbatch_nonneg : ∀ segment ∈ segments, 0 <= segment.endpointBatch i) :
    0 <= finiteGPSConstantRateSegmentComparatorFrom initial rate i segments := by
  induction segments generalizing initial with
  | nil =>
      simpa [finiteGPSConstantRateSegmentComparatorFrom] using hinitial_nonneg
  | cons segment segments ih =>
      apply ih
      · unfold lateBatchUpdate
        exact add_nonneg (le_max_right _ _) (hbatch_nonneg segment (by simp))
      · intro later hlater
        exact hbatch_nonneg later (by simp [hlater])

/--
Compress a consecutive selected-class-zero endpoint block into the service
interval immediately before the next retained endpoint.  The `zeroSegments`
may consist of any mixture of internal depletion endpoints and external
endpoints whose batch for `i` is zero.  Their durations are accumulated, while
the retained endpoint's actual selected-class batch is left unchanged.

The hypotheses say only that elapsed durations and the comparison rate are
nonnegative.  They deliberately do not mention a source event type or a
runner implementation.
-/
theorem finiteGPSConstantRateSegmentComparatorFrom_zeroBatchPrefix_then
    (initial rate : Real) (i : Class)
    (zeroSegments : List (FiniteGPSExecutionSegment Class))
    (retained : FiniteGPSExecutionSegment Class)
    (tail : List (FiniteGPSExecutionSegment Class))
    (hinitial_nonneg : 0 <= initial)
    (hrate_nonneg : 0 <= rate)
    (hduration_nonneg : ∀ segment ∈ zeroSegments, 0 <= segment.duration)
    (hretained_duration_nonneg : 0 <= retained.duration)
    (hzero_batch : ∀ segment ∈ zeroSegments, segment.endpointBatch i = 0) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i
        (zeroSegments ++ retained :: tail) =
      finiteGPSConstantRateSegmentComparatorFrom
        (lateBatchUpdate initial
          (rate * (finiteGPSExecutionSegmentsTotalDuration zeroSegments +
            retained.duration))
          (retained.endpointBatch i))
        rate i tail := by
  rw [finiteGPSConstantRateSegmentComparatorFrom_append]
  rw [finiteGPSConstantRateSegmentComparatorFrom_eq_combinedZeroBatchService
    initial rate i zeroSegments hinitial_nonneg hrate_nonneg hduration_nonneg
    hzero_batch]
  simp only [finiteGPSConstantRateSegmentComparatorFrom]
  have hretained_service_nonneg : 0 <= rate * retained.duration :=
    mul_nonneg hrate_nonneg hretained_duration_nonneg
  rw [lateBatchUpdate_zeroBatch_merge initial
    (rate * finiteGPSExecutionSegmentsTotalDuration zeroSegments)
    (rate * retained.duration) (retained.endpointBatch i)
    hretained_service_nonneg]
  rw [mul_add]

/--
Contextual form of `finiteGPSConstantRateSegmentComparatorFrom_zeroBatchPrefix_then`.
It removes a selected-class-zero block occurring after an arbitrary preceding
chronological prefix.  The caller supplies nonnegativity of the scalar state
at that boundary; for an actual nonnegative-work trace this is normally a
direct invariant, rather than an event-name convention.
-/
theorem finiteGPSConstantRateSegmentComparatorFrom_append_zeroBatchPrefix_then
    (initial rate : Real) (i : Class)
    (prior zeroSegments : List (FiniteGPSExecutionSegment Class))
    (retained : FiniteGPSExecutionSegment Class)
    (tail : List (FiniteGPSExecutionSegment Class))
    (hprior_nonneg : 0 <=
      finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
    (hrate_nonneg : 0 <= rate)
    (hduration_nonneg : ∀ segment ∈ zeroSegments, 0 <= segment.duration)
    (hretained_duration_nonneg : 0 <= retained.duration)
    (hzero_batch : ∀ segment ∈ zeroSegments, segment.endpointBatch i = 0) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i
        (prior ++ zeroSegments ++ retained :: tail) =
      finiteGPSConstantRateSegmentComparatorFrom
        (lateBatchUpdate
          (finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
          (rate * (finiteGPSExecutionSegmentsTotalDuration zeroSegments +
            retained.duration))
          (retained.endpointBatch i))
        rate i tail := by
  rw [show prior ++ zeroSegments ++ retained :: tail =
      prior ++ (zeroSegments ++ retained :: tail) by simp [List.append_assoc]]
  rw [finiteGPSConstantRateSegmentComparatorFrom_append]
  exact finiteGPSConstantRateSegmentComparatorFrom_zeroBatchPrefix_then
    (finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
    rate i zeroSegments retained tail hprior_nonneg hrate_nonneg
    hduration_nonneg hretained_duration_nonneg hzero_batch

/--
Compress a final selected-class-zero endpoint suffix to one terminal reflected
service update.  Unlike deleting the suffix, this retains every elapsed
service interval after the final selected-class batch.
-/
theorem finiteGPSConstantRateSegmentComparatorFrom_append_zeroBatchSuffix
    (initial rate : Real) (i : Class)
    (prior zeroSegments : List (FiniteGPSExecutionSegment Class))
    (hprior_nonneg : 0 <=
      finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
    (hrate_nonneg : 0 <= rate)
    (hduration_nonneg : ∀ segment ∈ zeroSegments, 0 <= segment.duration)
    (hzero_batch : ∀ segment ∈ zeroSegments, segment.endpointBatch i = 0) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i
        (prior ++ zeroSegments) =
      lateBatchUpdate
        (finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
        (rate * finiteGPSExecutionSegmentsTotalDuration zeroSegments) 0 := by
  rw [finiteGPSConstantRateSegmentComparatorFrom_append]
  exact finiteGPSConstantRateSegmentComparatorFrom_eq_combinedZeroBatchService
    (finiteGPSConstantRateSegmentComparatorFrom initial rate i prior)
    rate i zeroSegments hprior_nonneg hrate_nonneg hduration_nonneg hzero_batch

end

end AppliedModelingLib.Probability.Queueing
