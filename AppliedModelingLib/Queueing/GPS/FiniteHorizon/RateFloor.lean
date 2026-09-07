import AppliedModelingLib.Queueing.GPS.FiniteHorizon.SegmentTrace
import Mathlib.Tactic

/-!
# Per-class rate floors for finite GPS segments

This module records the elementary guaranteed-rate consequence of the
executable finite GPS kernel.  At a positive-workload snapshot, a class gets
at least its capacity-weight share; multiplying by the concrete nonnegative
next-event duration gives the corresponding stored-service floor for one
constructed segment.

The scope is one deterministic snapshot or segment.  It makes no completion,
trace-wide, stochastic, stationary, Palm, or tail claim.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- An active class receives at least its capacity-weight GPS floor.  The
non-strict statement also covers a zero capacity-weight floor. -/
theorem finiteGPSClassRate_ge_weightedCapacity_of_active
    {capacity : ℝ} {weight work : Class → ℝ} {i : Class}
    (hcapacity : 0 ≤ capacity) (hweight_nonneg : ∀ j, 0 ≤ weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hactive : 0 < work i) :
    capacity * weight i ≤ finiteGPSClassRate capacity weight work i := by
  rw [finiteGPSClassRate_eq_gpsBackloggedClassRate_of_active hactive]
  by_cases hfloor_pos : 0 < capacity * weight i
  · exact gpsBackloggedClassRate_ge_guaranteed_of_tag_backlogged
      hcapacity hweight_nonneg htotal_weight_le_one hfloor_pos
      (finiteGPSBacklogged_eq_true_iff.mpr hactive)
  · have hfloor_nonneg : 0 ≤ capacity * weight i :=
      mul_nonneg hcapacity (hweight_nonneg i)
    have hfloor_zero : capacity * weight i = 0 :=
      le_antisymm (le_of_not_gt hfloor_pos) hfloor_nonneg
    rw [hfloor_zero]
    exact gpsBackloggedClassRate_nonneg 0 hcapacity hweight_nonneg

/-- For a concrete finite GPS segment, an active class receives at least its
capacity-weight rate floor times the actual nonnegative segment duration.
The workload and pending-batch nonnegativity hypotheses are used solely to
establish that the constructed next-event duration is nonnegative. -/
theorem finiteGPSBuildExecutionSegment_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {startTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hactive : 0 < work i) :
    capacity * weight i *
        (finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).duration ≤
      (finiteGPSBuildExecutionSegment capacity weight work batchWork
        startTime nextBatchDelay).serviceIncrement i := by
  have hrate : capacity * weight i ≤ finiteGPSClassRate capacity weight work i :=
    finiteGPSClassRate_ge_weightedCapacity_of_active hcapacity.le
      (fun j => (hweight_pos j).le) htotal_weight_le_one hactive
  have hduration : 0 ≤ finiteGPSNextStepDuration capacity weight work nextBatchDelay :=
    finiteGPSNextStepDuration_nonneg hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg hnextBatchDelay_nonneg
  rw [finiteGPSBuildExecutionSegment_duration,
    finiteGPSBuildExecutionSegment_serviceIncrement,
    finiteGPSServiceIncrement_eq_rate_mul_nextStep hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg]
  exact mul_le_mul_of_nonneg_right hrate hduration

/-- Every concrete segment emitted by one bounded GPS gap has the stored
guaranteed-rate floor whenever the chosen class is actually backlogged at
that segment's left endpoint.  The quantification is over the executable
segment list, including internal depletion segments.  It deliberately says
nothing about a segment after the chosen class has emptied, nor does it make
an endpoint batch active during the preceding half-open interval. -/
theorem finiteGPSRunGapSegments_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    (fuel : ℕ) {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    {currentTime : ℝ} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      0 < segment.startWorkload i →
        capacity * weight i * segment.duration ≤ segment.serviceIncrement i := by
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
        have hactive' : 0 < work i := by
          simpa using hactive
        exact finiteGPSBuildExecutionSegment_weightedCapacity_mul_duration_le_serviceIncrement_of_active
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hnextBatchDelay_nonneg hactive'
      · intro segment hsegment hactive
        have hinternal :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
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
                  batchWork
                  (currentTime + duration) (nextBatchDelay - duration) := by
          simp [finiteGPSRunGapSegments, duration, hduration]
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          have hactive' : 0 < work i := by
            simpa using hactive
          exact finiteGPSBuildExecutionSegment_weightedCapacity_mul_duration_le_serviceIncrement_of_active
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            hnextBatchDelay_nonneg hactive'
        · exact ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_work_nonneg
            hnext_delay_nonneg segment htail hactive

/-- The same local guaranteed-rate fact for the complete executable finite
batch trace.  This preserves the literal chronological batch recursion: the
recursive call begins only after the current gap actually reaches its source
endpoint. -/
theorem finiteGPSRunBatchTraceSegments_weightedCapacity_mul_duration_le_serviceIncrement_of_active
    {capacity : ℝ} {weight work : Class → ℝ} {batchWork : ℝ → Class → ℝ}
    {currentTime : ℝ} {i : Class} (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 ≤ batchWork eventTime j) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      0 < segment.startWorkload i →
        capacity * weight i * segment.duration ≤ segment.serviceIncrement i := by
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
          0 < segment.startWorkload i →
            capacity * weight i * segment.duration ≤ segment.serviceIncrement i := by
        exact finiteGPSRunGapSegments_weightedCapacity_mul_duration_le_serviceIncrement_of_active
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
          hnext_work_nonneg
          hchronological_tail hbatch_tail
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

end

end AppliedModelingLib.Probability.Queueing
