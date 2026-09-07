import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateComparison
import Mathlib.Tactic

/-!
# Refining zero-batch intervals in a constant-rate GPS comparator

The executable GPS trace contains internal depletion endpoints and source
endpoints for other classes.  For a chosen class both have a zero endpoint
batch, but their service intervals are still real and must not be discarded.
This module proves the scalar algebra needed to merge such intervals into the
next selected-class batch interval.  It is deterministic and source-agnostic.

No GPS path comparison, stochastic source, or response-time conclusion is
claimed here.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Two consecutive service-before-endpoint updates can be merged when the
first endpoint carries no selected-class batch.  The second service amount
must be nonnegative: it is an elapsed service interval, not an arbitrary
algebraic subtraction. -/
theorem lateBatchUpdate_zeroBatch_merge
    (work firstService secondService batch : Real)
    (hsecondService_nonneg : 0 <= secondService) :
    lateBatchUpdate (lateBatchUpdate work firstService 0) secondService batch =
      lateBatchUpdate work (firstService + secondService) batch := by
  unfold lateBatchUpdate
  by_cases hfirst : work - firstService <= 0
  · rw [max_eq_right hfirst]
    have hleft : 0 - secondService <= 0 := by linarith
    simp only [zero_add]
    rw [max_eq_right hleft]
    have hright : work - (firstService + secondService) <= 0 := by linarith
    rw [max_eq_right hright]
  · have hfirst_nonneg : 0 <= work - firstService :=
      le_of_lt (lt_of_not_ge hfirst)
    rw [max_eq_left hfirst_nonneg]
    congr 2
    ring

/-- Total elapsed duration in a finite concrete segment block. -/
def finiteGPSExecutionSegmentsTotalDuration :
    List (FiniteGPSExecutionSegment Class) -> Real :=
  fun segments => (segments.map FiniteGPSExecutionSegment.duration).sum

/-- The total duration of two adjacent concrete segment blocks adds exactly. -/
theorem finiteGPSExecutionSegmentsTotalDuration_append
    (left right : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSExecutionSegmentsTotalDuration (left ++ right) =
      finiteGPSExecutionSegmentsTotalDuration left +
        finiteGPSExecutionSegmentsTotalDuration right := by
  simp [finiteGPSExecutionSegmentsTotalDuration]

/-- A finite block whose selected-class endpoint batches are all zero is one
reflected service interval of the combined duration.  The initial scalar work
is required to be nonnegative because the empty block otherwise cannot be
identified with a reflected update of zero service. -/
theorem finiteGPSConstantRateSegmentComparatorFrom_eq_combinedZeroBatchService
    (initial rate : Real) (i : Class)
    (segments : List (FiniteGPSExecutionSegment Class))
    (hinitial_nonneg : 0 <= initial)
    (hrate_nonneg : 0 <= rate)
    (hduration_nonneg : ∀ segment ∈ segments, 0 <= segment.duration)
    (hzero_batch : ∀ segment ∈ segments, segment.endpointBatch i = 0) :
    finiteGPSConstantRateSegmentComparatorFrom initial rate i segments =
      lateBatchUpdate initial
        (rate * finiteGPSExecutionSegmentsTotalDuration segments) 0 := by
  induction segments generalizing initial with
  | nil =>
      simp [finiteGPSConstantRateSegmentComparatorFrom,
        finiteGPSExecutionSegmentsTotalDuration, lateBatchUpdate,
        max_eq_left hinitial_nonneg]
  | cons segment segments ih =>
      have hduration_head : 0 <= segment.duration := hduration_nonneg segment (by simp)
      have hduration_tail : ∀ later ∈ segments, 0 <= later.duration := by
        intro later hlater
        exact hduration_nonneg later (by simp [hlater])
      have hbatch_head : segment.endpointBatch i = 0 := hzero_batch segment (by simp)
      have hbatch_tail : ∀ later ∈ segments, later.endpointBatch i = 0 := by
        intro later hlater
        exact hzero_batch later (by simp [hlater])
      let afterHead := lateBatchUpdate initial (rate * segment.duration) 0
      have hafterHead_nonneg : 0 <= afterHead := by
        dsimp [afterHead, lateBatchUpdate]
        exact add_nonneg (le_max_right _ _) le_rfl
      have htail := ih afterHead hafterHead_nonneg hduration_tail hbatch_tail
      rw [finiteGPSConstantRateSegmentComparatorFrom, hbatch_head]
      change finiteGPSConstantRateSegmentComparatorFrom afterHead rate i segments = _
      rw [htail]
      have htail_duration_nonneg : 0 <= finiteGPSExecutionSegmentsTotalDuration segments := by
        unfold finiteGPSExecutionSegmentsTotalDuration
        apply List.sum_nonneg
        intro duration hduration_mem
        rcases List.mem_map.mp hduration_mem with ⟨later, hlater, rfl⟩
        exact hduration_tail later hlater
      have hsecondService_nonneg : 0 <=
          rate * finiteGPSExecutionSegmentsTotalDuration segments :=
        mul_nonneg hrate_nonneg htail_duration_nonneg
      rw [lateBatchUpdate_zeroBatch_merge initial (rate * segment.duration)
        (rate * finiteGPSExecutionSegmentsTotalDuration segments) 0
        hsecondService_nonneg]
      congr 2
      simp only [finiteGPSExecutionSegmentsTotalDuration]
      rw [List.map_cons, List.sum_cons]
      ring

end

end AppliedModelingLib.Probability.Queueing
