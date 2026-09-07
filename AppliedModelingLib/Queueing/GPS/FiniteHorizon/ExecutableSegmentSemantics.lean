import AppliedModelingLib.Queueing.GPS.FiniteHorizon.ConstantRateProjection
import Mathlib.Tactic

/-!
# Local semantic facts for executable finite GPS segments

The finite GPS runner stores concrete segment fields.  This module records
two direct semantic consequences of its executable recursion: an active class
has a positive stored rate, and stored service is rate times duration.  The
results are stated over segment membership rather than runner function names,
so source-labelled adapters can use them after an erasure/provenance proof.

Everything here is finite and deterministic.  It does not add source labels,
stationarity, Palm conditioning, or a queueing tail result.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- In one concrete kernel segment, a class active at its left endpoint has
a strictly positive stored GPS rate. -/
theorem finiteGPSBuildExecutionSegment_classRate_pos_of_active
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hactive : 0 <
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).startWorkload i) :
    0 < (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).classRate i := by
  change 0 < finiteGPSClassRate capacity weight work i
  exact finiteGPSClassRate_pos_of_active hcapacity hweight_pos
    htotal_weight_le_one (by simpa using hactive)

/-- In one concrete kernel segment, stored service is exactly the stored
class rate times the stored duration. -/
theorem finiteGPSBuildExecutionSegment_serviceIncrement_eq_classRate_mul_duration
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).serviceIncrement i =
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).classRate i *
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).duration := by
  change finiteGPSServiceIncrement capacity weight work
      (finiteGPSNextStepDuration capacity weight work nextBatchDelay) i =
    finiteGPSClassRate capacity weight work i *
      finiteGPSNextStepDuration capacity weight work nextBatchDelay
  exact finiteGPSServiceIncrement_eq_rate_mul_nextStep
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg

/-- Every active class in every segment of one executable finite GPS gap has
a positive stored rate.  The induction follows the actual internal-depletion
recursion and carries the computed next workload rather than inventing a
separate segment relation. -/
theorem finiteGPSRunGapSegments_classRate_pos_of_active
    (fuel : ℕ) {capacity nextBatchDelay : ℝ}
    {weight work batchWork : Class → ℝ} {currentTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      0 < segment.startWorkload i → 0 < segment.classRate i := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · intro segment hsegment hactive
        have hsegment_eq :
            segment = finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hduration] using hsegment
        subst segment
        exact finiteGPSBuildExecutionSegment_classRate_pos_of_active
          hcapacity hweight_pos htotal_weight_le_one hactive
      · intro segment hsegment hactive
        have hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
            nextBatchDelay := by
          simpa [duration] using hduration
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hnext_delay_nonneg : 0 ≤ nextBatchDelay - duration := by
          rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
              nextBatchDelay)
        have hlist :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
              currentTime nextBatchDelay =
              finiteGPSBuildExecutionSegment capacity weight work batchWork
                currentTime nextBatchDelay ::
                finiteGPSRunGapSegments fuel capacity weight
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                  batchWork (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hduration]
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_classRate_pos_of_active
            hcapacity hweight_pos htotal_weight_le_one hactive
        · exact ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_work_nonneg hnext_delay_nonneg segment htail hactive

/-- Every segment of one executable finite GPS gap stores exact
rate-times-duration service. -/
theorem finiteGPSRunGapSegments_serviceIncrement_eq_classRate_mul_duration
    (fuel : ℕ) {capacity nextBatchDelay : ℝ}
    {weight work batchWork : Class → ℝ} {currentTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      segment.serviceIncrement i = segment.classRate i * segment.duration := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · intro segment hsegment
        have hsegment_eq :
            segment = finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hduration] using hsegment
        subst segment
        exact finiteGPSBuildExecutionSegment_serviceIncrement_eq_classRate_mul_duration
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      · intro segment hsegment
        have hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
            nextBatchDelay := by
          simpa [duration] using hduration
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hnext_delay_nonneg : 0 ≤ nextBatchDelay - duration := by
          rw [show duration = finiteGPSNextStepDuration capacity weight work nextBatchDelay by rfl]
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
              nextBatchDelay)
        have hlist :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
              currentTime nextBatchDelay =
              finiteGPSBuildExecutionSegment capacity weight work batchWork
                currentTime nextBatchDelay ::
                finiteGPSRunGapSegments fuel capacity weight
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                  batchWork (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hduration]
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_serviceIncrement_eq_classRate_mul_duration
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        · exact ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_work_nonneg hnext_delay_nonneg segment htail

/-- Every active class in every segment of a chronological executable batch
trace has a positive stored rate. -/
theorem finiteGPSRunBatchTraceSegments_classRate_pos_of_active
    {capacity : ℝ} {weight work : Class → ℝ} {batchWork : ℝ → Class → ℝ}
    {currentTime : ℝ} {i : Class} (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 ≤ batchWork eventTime j) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      0 < segment.startWorkload i → 0 < segment.classRate i := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_local : ∀ segment ∈
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime),
          0 < segment.startWorkload i → 0 < segment.classRate i := by
        exact finiteGPSRunGapSegments_classRate_pos_of_active
          gapFuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          (sub_nonneg.mpr hdelay)
      by_cases hbatch_applied : gap.batchApplied = true
      · have hgap_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap, gapFuel] using hbatch_applied
        have hnext_work_nonneg : ∀ j, 0 ≤ gap.workload j := by
          exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
            (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
        have htail := ih
          (currentTime := eventTime) (work := gap.workload)
          hnext_work_nonneg hchronological_tail hbatch_tail
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) ++
                finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
                  gap.workload times := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_batchApplied
              capacity weight batchWork currentTime work eventTime times hgap_applied)
        intro segment hsegment hactive
        rw [htrace] at hsegment
        rcases List.mem_append.mp hsegment with hgap_segment | htail_segment
        · exact hgap_local segment hgap_segment hactive
        · exact htail segment htail_segment hactive
      · have hbatch_not_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap, gapFuel] using hbatch_applied
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
              capacity weight batchWork currentTime work eventTime times hbatch_not_applied)
        intro segment hsegment hactive
        rw [htrace] at hsegment
        exact hgap_local segment hsegment hactive

/-- Every segment of a chronological executable batch trace stores exact
rate-times-duration service. -/
theorem finiteGPSRunBatchTraceSegments_serviceIncrement_eq_classRate_mul_duration
    {capacity : ℝ} {weight work : Class → ℝ} {batchWork : ℝ → Class → ℝ}
    {currentTime : ℝ} {i : Class} (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 ≤ batchWork eventTime j) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      segment.serviceIncrement i = segment.classRate i * segment.duration := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 ≤ batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_local : ∀ segment ∈
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime),
          segment.serviceIncrement i = segment.classRate i * segment.duration := by
        exact finiteGPSRunGapSegments_serviceIncrement_eq_classRate_mul_duration
          gapFuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          (sub_nonneg.mpr hdelay)
      by_cases hbatch_applied : gap.batchApplied = true
      · have hgap_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap, gapFuel] using hbatch_applied
        have hnext_work_nonneg : ∀ j, 0 ≤ gap.workload j := by
          exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
            (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
        have htail := ih
          (currentTime := eventTime) (work := gap.workload)
          hnext_work_nonneg hchronological_tail hbatch_tail
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) ++
                finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
                  gap.workload times := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_batchApplied
              capacity weight batchWork currentTime work eventTime times hgap_applied)
        intro segment hsegment
        rw [htrace] at hsegment
        rcases List.mem_append.mp hsegment with hgap_segment | htail_segment
        · exact hgap_local segment hgap_segment
        · exact htail segment htail_segment
      · have hbatch_not_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap, gapFuel] using hbatch_applied
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
              capacity weight batchWork currentTime work eventTime times hbatch_not_applied)
        intro segment hsegment
        rw [htrace] at hsegment
        exact hgap_local segment hsegment

/-- Every segment emitted while advancing toward one pending external batch
ends no later than that batch's clock.  This is a structural fact about the
actual recursive segment list and does not need a source interpretation. -/
theorem finiteGPSRunGapSegments_endTime_le_currentTime_add_delay
    (fuel : ℕ) {capacity nextBatchDelay : ℝ}
    {weight work batchWork : Class → ℝ} {currentTime : ℝ} :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      finiteGPSExecutionSegmentEndTime segment ≤ currentTime + nextBatchDelay := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hduration : duration = nextBatchDelay
      · intro segment hsegment
        have hsegment_eq :
            segment = finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hduration] using hsegment
        subst segment
        change currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤
          currentTime + nextBatchDelay
        linarith [finiteGPSNextStepDuration_le_nextBatchDelay
          capacity weight work nextBatchDelay]
      · have hlist :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
              currentTime nextBatchDelay =
              finiteGPSBuildExecutionSegment capacity weight work batchWork
                currentTime nextBatchDelay ::
                finiteGPSRunGapSegments fuel capacity weight
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
                  batchWork (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hduration]
        intro segment hsegment
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          change currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤
            currentTime + nextBatchDelay
          linarith [finiteGPSNextStepDuration_le_nextBatchDelay
            capacity weight work nextBatchDelay]
        · have htail_bound := ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration) segment htail
          linarith

/-- Every concrete segment emitted by a finite batch trace ends by any upper
bound shared by its literal external batch clocks.  The result follows the
runner's actual stop-or-continue recursion, so an unreached batch cannot
create a spurious later segment. -/
theorem finiteGPSRunBatchTraceSegments_endTime_le_of_times_le
    {capacity : ℝ} {weight work : Class → ℝ} {batchWork : ℝ → Class → ℝ}
    {currentTime horizon : ℝ} (times : List ℝ)
    (htimes_le_horizon : ∀ eventTime ∈ times, eventTime ≤ horizon) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      finiteGPSExecutionSegmentEndTime segment ≤ horizon := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      have heventTime_le_horizon : eventTime ≤ horizon :=
        htimes_le_horizon eventTime (by simp)
      have htail_times_le_horizon : ∀ laterTime ∈ times, laterTime ≤ horizon := by
        intro laterTime hlaterTime
        exact htimes_le_horizon laterTime (by simp [hlaterTime])
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_endTime : ∀ segment ∈
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime),
          finiteGPSExecutionSegmentEndTime segment ≤ horizon := by
        intro segment hsegment
        have hbound := finiteGPSRunGapSegments_endTime_le_currentTime_add_delay
          gapFuel (capacity := capacity) (weight := weight) (work := work)
          (batchWork := batchWork eventTime) (currentTime := currentTime)
          (nextBatchDelay := eventTime - currentTime) segment hsegment
        linarith
      by_cases hbatch_applied : gap.batchApplied = true
      · have hgap_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied = true := by
            simpa [gap, gapFuel] using hbatch_applied
        have htail := ih (currentTime := eventTime)
          (work := gap.workload) htail_times_le_horizon
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) ++
                finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
                  gap.workload times := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_batchApplied
              capacity weight batchWork currentTime work eventTime times hgap_applied)
        intro segment hsegment
        rw [htrace] at hsegment
        rcases List.mem_append.mp hsegment with hgap_segment | htail_segment
        · exact hgap_endTime segment hgap_segment
        · exact htail segment htail_segment
      · have hbatch_not_applied :
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork eventTime)
              (eventTime - currentTime)).batchApplied ≠ true := by
            simpa [gap, gapFuel] using hbatch_applied
        have htrace :
            finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times) =
              finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime) := by
          simpa [gap, gapFuel] using
            (finiteGPSRunBatchTraceSegments_cons_of_not_batchApplied
              capacity weight batchWork currentTime work eventTime times hbatch_not_applied)
        intro segment hsegment
        rw [htrace] at hsegment
        exact hgap_endTime segment hsegment

end

end AppliedModelingLib.Probability.Queueing
