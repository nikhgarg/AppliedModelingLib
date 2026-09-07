import AppliedModelingLib.Queueing.GPS.FiniteHorizon.RateFloor
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.Lindley.Recursion
import Mathlib.Tactic

/-!
# Constant-rate comparison for finite GPS execution segments

This module gives a deterministic comparison between the executable finite
GPS segment ledger and a one-class constant-rate, service-before-endpoint
batch recursion.  The scalar comparator processes the *same ordered segment
ledger*: each stored GPS interval contributes its actual duration, and the
class's endpoint batch is appended only after that interval's service.  Thus
internal depletion segments contribute a zero endpoint batch and no source
arrival is moved across a service interval.

The semantic propagation theorem is deliberately phrased for an arbitrary
chain of stored execution segments.  It needs only the actual endpoint
balance and a guaranteed-rate floor while the selected class is active; it
does not assume a stochastic source, stationarity, Palm conditioning, or a
tail law.  A later source adapter can instantiate it with a literal finite
batch trace.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The class workload at the final endpoint of an ordered concrete segment
ledger.  The list order is chronological, so each later segment starts from
the preceding endpoint workload when accompanied by
`FiniteGPSExecutionSegmentsChainFrom`. -/
def finiteGPSExecutionSegmentsFinalWorkload
    (initialWorkload : Class -> Real) :
    List (FiniteGPSExecutionSegment Class) -> Class -> Real
  | [] => initialWorkload
  | segment :: segments =>
      finiteGPSExecutionSegmentsFinalWorkload segment.endpointWorkload segments

/-- The clock at the final endpoint of an ordered concrete segment ledger. -/
def finiteGPSExecutionSegmentsFinalTime
    (initialTime : Real) :
    List (FiniteGPSExecutionSegment Class) -> Real
  | [] => initialTime
  | segment :: segments =>
      finiteGPSExecutionSegmentsFinalTime
        (finiteGPSExecutionSegmentEndTime segment) segments

/-- A scalar service-before-endpoint workload recursion over the exact ordered
GPS segment ledger.  It is initialized at an explicit pre-first-segment
workload.  The service amount in a segment is `rate * duration`, and the
class's stored endpoint batch is added afterwards. -/
def finiteGPSConstantRateSegmentComparatorFrom
    (initial rate : Real) (i : Class) :
    List (FiniteGPSExecutionSegment Class) -> Real
  | [] => initial
  | segment :: segments =>
      finiteGPSConstantRateSegmentComparatorFrom
        (lateBatchUpdate initial (rate * segment.duration) (segment.endpointBatch i))
        rate i segments

/-- The empty-start constant-rate comparator. -/
def finiteGPSConstantRateSegmentComparator
    (rate : Real) (i : Class)
    (segments : List (FiniteGPSExecutionSegment Class)) : Real :=
  finiteGPSConstantRateSegmentComparatorFrom 0 rate i segments

/-- A late-batch update is monotone in its pre-service workload. -/
theorem lateBatchUpdate_mono_postWork
    {left right service batch : Real} (hleft_right : left <= right) :
    lateBatchUpdate left service batch <= lateBatchUpdate right service batch := by
  unfold lateBatchUpdate
  gcongr

/-- Final endpoint workloads compose across concatenated chronological segment
ledgers. -/
theorem finiteGPSExecutionSegmentsFinalWorkload_append
    (initialWorkload : Class -> Real)
    (left right : List (FiniteGPSExecutionSegment Class)) (i : Class) :
    finiteGPSExecutionSegmentsFinalWorkload initialWorkload (left ++ right) i =
      finiteGPSExecutionSegmentsFinalWorkload
        (finiteGPSExecutionSegmentsFinalWorkload initialWorkload left) right i := by
  induction left generalizing initialWorkload with
  | nil => simp [finiteGPSExecutionSegmentsFinalWorkload]
  | cons segment left ih =>
      simpa [finiteGPSExecutionSegmentsFinalWorkload] using
        ih (initialWorkload := segment.endpointWorkload)

/-- Final endpoint clocks compose across concatenated chronological segment
ledgers. -/
theorem finiteGPSExecutionSegmentsFinalTime_append
    (initialTime : Real)
    (left right : List (FiniteGPSExecutionSegment Class)) :
    finiteGPSExecutionSegmentsFinalTime initialTime (left ++ right) =
      finiteGPSExecutionSegmentsFinalTime
        (finiteGPSExecutionSegmentsFinalTime initialTime left) right := by
  induction left generalizing initialTime with
  | nil => simp [finiteGPSExecutionSegmentsFinalTime]
  | cons segment left ih =>
      simpa [finiteGPSExecutionSegmentsFinalTime] using
        ih (initialTime := finiteGPSExecutionSegmentEndTime segment)

/-- Concatenate two verified segment chains at their literal common endpoint. -/
theorem finiteGPSExecutionSegmentsChainFrom_append
    (initialTime : Real) (initialWorkload : Class -> Real)
    (left right : List (FiniteGPSExecutionSegment Class))
    (hleft : FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload left)
    (hright : FiniteGPSExecutionSegmentsChainFrom
      (finiteGPSExecutionSegmentsFinalTime initialTime left)
      (finiteGPSExecutionSegmentsFinalWorkload initialWorkload left) right) :
    FiniteGPSExecutionSegmentsChainFrom initialTime initialWorkload (left ++ right) := by
  induction left generalizing initialTime initialWorkload with
  | nil =>
      simpa [finiteGPSExecutionSegmentsFinalTime,
        finiteGPSExecutionSegmentsFinalWorkload] using hright
  | cons segment left ih =>
      rcases hleft with ⟨hstartTime, hstartWorkload, hleftTail⟩
      refine ⟨hstartTime, hstartWorkload, ?_⟩
      simpa [finiteGPSExecutionSegmentsFinalTime,
        finiteGPSExecutionSegmentsFinalWorkload] using
        (ih (initialTime := finiteGPSExecutionSegmentEndTime segment)
          (initialWorkload := segment.endpointWorkload) hleftTail hright)

/--
Semantic one-segment comparison.  If an endpoint balance records the actual
stored service, and that service dominates `rate * duration` whenever the
class is backlogged at the left endpoint, then the actual endpoint workload
is bounded by the scalar service-before-endpoint update.  The inactive case
uses only nonnegative stored service, so it does not charge a later endpoint
batch to the preceding interval.
-/
theorem finiteGPSExecutionSegment_endpointWorkload_le_lateBatchUpdate_of_serviceFloor
    (segment : FiniteGPSExecutionSegment Class) (i : Class) (rate : Real)
    (hstart_nonneg : 0 <= segment.startWorkload i)
    (hservice_nonneg : 0 <= segment.serviceIncrement i)
    (hduration_nonneg : 0 <= segment.duration)
    (hrate_nonneg : 0 <= rate)
    (hactive_floor : 0 < segment.startWorkload i ->
      rate * segment.duration <= segment.serviceIncrement i)
    (hbalance : segment.endpointWorkload i =
      segment.startWorkload i + segment.endpointBatch i - segment.serviceIncrement i) :
    segment.endpointWorkload i <=
      lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
        (segment.endpointBatch i) := by
  by_cases hactive : 0 < segment.startWorkload i
  · calc
      segment.endpointWorkload i =
          segment.startWorkload i + segment.endpointBatch i -
            segment.serviceIncrement i := hbalance
      _ <= segment.startWorkload i + segment.endpointBatch i -
            rate * segment.duration := by
              linarith [hactive_floor hactive]
      _ = (segment.startWorkload i - rate * segment.duration) +
            segment.endpointBatch i := by ring
      _ <= max (segment.startWorkload i - rate * segment.duration) 0 +
            segment.endpointBatch i := by
              gcongr
              exact le_max_left _ _
      _ = lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
            (segment.endpointBatch i) := rfl
  · have hstart_zero : segment.startWorkload i = 0 :=
      le_antisymm (le_of_not_gt hactive) hstart_nonneg
    have hrate_duration_nonneg : 0 <= rate * segment.duration :=
      mul_nonneg hrate_nonneg hduration_nonneg
    calc
      segment.endpointWorkload i =
          segment.startWorkload i + segment.endpointBatch i -
            segment.serviceIncrement i := hbalance
      _ <= segment.endpointBatch i := by rw [hstart_zero]; linarith
      _ = lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
            (segment.endpointBatch i) := by
              unfold lateBatchUpdate
              rw [hstart_zero]
              rw [max_eq_right (sub_nonpos.mpr hrate_duration_nonneg)]
              ring

/--
Propagate the semantic one-segment comparison through an ordered concrete
segment ledger.  The chain predicate supplies the actual chronology; the
local premise is intentionally semantic, so callers need not rely on a
particular runner function name or event numbering.
-/
theorem finiteGPSExecutionSegmentsFinalWorkload_le_constantRateComparatorFrom
    (initialWorkload : Class -> Real) (initialComparator rate : Real) (i : Class)
    (segments : List (FiniteGPSExecutionSegment Class)) (startTime : Real)
    (hchain : FiniteGPSExecutionSegmentsChainFrom startTime initialWorkload segments)
    (hinitial : initialWorkload i <= initialComparator)
    (hstep : ∀ segment ∈ segments,
      segment.endpointWorkload i <=
        lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
          (segment.endpointBatch i)) :
    finiteGPSExecutionSegmentsFinalWorkload initialWorkload segments i <=
      finiteGPSConstantRateSegmentComparatorFrom initialComparator rate i segments := by
  induction segments generalizing initialWorkload initialComparator startTime with
  | nil =>
      simpa [finiteGPSExecutionSegmentsFinalWorkload,
        finiteGPSConstantRateSegmentComparatorFrom] using hinitial
  | cons segment segments ih =>
      rcases hchain with ⟨hstartTime, hstartWorkload, htailChain⟩
      have hhead_step := hstep segment (by simp)
      have htail_step : ∀ laterSegment ∈ segments,
          laterSegment.endpointWorkload i <=
            lateBatchUpdate (laterSegment.startWorkload i)
              (rate * laterSegment.duration) (laterSegment.endpointBatch i) := by
        intro laterSegment hlaterSegment
        exact hstep laterSegment (by simp [hlaterSegment])
      have hhead_bound : segment.endpointWorkload i <=
          lateBatchUpdate initialComparator (rate * segment.duration)
            (segment.endpointBatch i) := by
        calc
          segment.endpointWorkload i <=
              lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
                (segment.endpointBatch i) := hhead_step
          _ = lateBatchUpdate (initialWorkload i) (rate * segment.duration)
                (segment.endpointBatch i) := by rw [hstartWorkload]
          _ <= lateBatchUpdate initialComparator (rate * segment.duration)
                (segment.endpointBatch i) :=
              lateBatchUpdate_mono_postWork hinitial
      simpa [finiteGPSExecutionSegmentsFinalWorkload,
        finiteGPSConstantRateSegmentComparatorFrom] using
        (ih (initialWorkload := segment.endpointWorkload)
          (initialComparator := lateBatchUpdate initialComparator
            (rate * segment.duration) (segment.endpointBatch i))
          (startTime := finiteGPSExecutionSegmentEndTime segment)
          htailChain hhead_bound htail_step)

/-- Empty-start specialization of the chronological segment comparison. -/
theorem finiteGPSExecutionSegmentsFinalWorkload_le_constantRateComparator
    (initialWorkload : Class -> Real) (rate : Real) (i : Class)
    (segments : List (FiniteGPSExecutionSegment Class)) (startTime : Real)
    (hinitial_zero : initialWorkload i = 0)
    (hchain : FiniteGPSExecutionSegmentsChainFrom startTime initialWorkload segments)
    (hstep : ∀ segment ∈ segments,
      segment.endpointWorkload i <=
        lateBatchUpdate (segment.startWorkload i) (rate * segment.duration)
          (segment.endpointBatch i)) :
    finiteGPSExecutionSegmentsFinalWorkload initialWorkload segments i <=
      finiteGPSConstantRateSegmentComparator rate i segments := by
  unfold finiteGPSConstantRateSegmentComparator
  apply finiteGPSExecutionSegmentsFinalWorkload_le_constantRateComparatorFrom
    initialWorkload 0 rate i segments startTime hchain
  · simpa [hinitial_zero]
  · exact hstep

/-- The concrete executable GPS event kernel discharges the semantic local
comparison at its guaranteed class rate.  Its endpoint batch is still the
kernel's actual service-after-arrival batch, including an exact
arrival/depletion tie. -/
theorem finiteGPSBuildExecutionSegment_endpointWorkload_le_weightedCapacityLateBatchUpdate
    {capacity nextBatchDelay : Real} {weight work batchWork : Class -> Real}
    {startTime : Real} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hnextBatchDelay_nonneg : 0 <= nextBatchDelay) :
    (finiteGPSBuildExecutionSegment capacity weight work batchWork
      startTime nextBatchDelay).endpointWorkload i <=
      lateBatchUpdate
        ((finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).startWorkload i)
        (capacity * weight i *
          (finiteGPSBuildExecutionSegment capacity weight work batchWork
            startTime nextBatchDelay).duration)
        ((finiteGPSBuildExecutionSegment capacity weight work batchWork
          startTime nextBatchDelay).endpointBatch i) := by
  apply finiteGPSExecutionSegment_endpointWorkload_le_lateBatchUpdate_of_serviceFloor
    (finiteGPSBuildExecutionSegment capacity weight work batchWork startTime nextBatchDelay)
    i (capacity * weight i)
  · simpa using hwork_nonneg i
  · exact finiteGPSBuildExecutionSegment_serviceIncrement_nonneg
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg
  · exact finiteGPSBuildExecutionSegment_duration_nonneg
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hnextBatchDelay_nonneg
  · exact mul_nonneg hcapacity.le (hweight_pos i).le
  · intro hactive
    exact finiteGPSBuildExecutionSegment_weightedCapacity_mul_duration_le_serviceIncrement_of_active
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      hnextBatchDelay_nonneg hactive
  · exact finiteGPSBuildExecutionSegment_balance capacity weight work batchWork
      startTime nextBatchDelay i

/-- The endpoint-workload fold of the concrete gap segment ledger is exactly
the workload returned by the executable gap runner, for every fuel value.
This is a deterministic representation identity, including a deliberately
stopped partial gap when fuel is exhausted. -/
theorem finiteGPSExecutionSegmentsFinalWorkload_runGapSegments
    (fuel : Nat) (capacity : Real) (weight work batchWork : Class -> Real)
    (currentTime nextBatchDelay : Real) :
    finiteGPSExecutionSegmentsFinalWorkload work
      (finiteGPSRunGapSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay) =
      (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload := by
  funext i
  induction fuel generalizing currentTime work nextBatchDelay with
  | zero => rfl
  | succ fuel ih =>
      unfold finiteGPSRunGapSegments finiteGPSRunGap
      dsimp only
      split
      · rfl
      · exact ih
          (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          (currentTime := currentTime +
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (nextBatchDelay := nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)

/-- The final clock of the concrete gap segment ledger is the supplied start
clock plus elapsed gap time, including only the event intervals the bounded
runner actually executed. -/
theorem finiteGPSExecutionSegmentsFinalTime_runGapSegments
    (fuel : Nat) (capacity : Real) (weight work batchWork : Class -> Real)
    (currentTime nextBatchDelay : Real) :
    finiteGPSExecutionSegmentsFinalTime currentTime
      (finiteGPSRunGapSegments fuel capacity weight work batchWork
        currentTime nextBatchDelay) =
      currentTime + nextBatchDelay -
        (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).remainingDelay := by
  induction fuel generalizing currentTime work nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments, finiteGPSRunGap,
        finiteGPSExecutionSegmentsFinalTime]
  | succ fuel ih =>
      unfold finiteGPSRunGapSegments finiteGPSRunGap
      dsimp only
      split
      · rename_i hexternal
        rw [finiteGPSExecutionSegmentsFinalTime,
          finiteGPSBuildExecutionSegment_endTime, hexternal]
        simp [finiteGPSExecutionSegmentsFinalTime]
      · rename_i hinternal
        rw [finiteGPSExecutionSegmentsFinalTime,
          finiteGPSBuildExecutionSegment_endTime]
        change finiteGPSExecutionSegmentsFinalTime
            (currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay)
            (finiteGPSRunGapSegments fuel capacity weight
              (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
              batchWork
              (currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              (nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)) =
          currentTime + nextBatchDelay -
            (finiteGPSRunGap fuel capacity weight
              (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
              batchWork
              (nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)).remainingDelay
        rw [ih
          (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          (currentTime := currentTime +
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (nextBatchDelay := nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)]
        ring

/-- Every segment emitted by an actual bounded GPS gap satisfies the local
guaranteed-rate scalar update bound.  The recursive branch is an actual
internal depletion event, so its endpoint batch is zero; no arrival is
inserted at that intermediate endpoint. -/
theorem finiteGPSRunGapSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
    (fuel : Nat) {capacity nextBatchDelay : Real}
    {weight work batchWork : Class -> Real} {currentTime : Real} {i : Class}
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hnextBatchDelay_nonneg : 0 <= nextBatchDelay) :
    ∀ segment ∈ finiteGPSRunGapSegments fuel capacity weight work batchWork
      currentTime nextBatchDelay,
      segment.endpointWorkload i <=
        lateBatchUpdate (segment.startWorkload i)
          (capacity * weight i * segment.duration) (segment.endpointBatch i) := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hexternal : duration = nextBatchDelay
      · intro segment hsegment
        have hsegment_eq :
            segment = finiteGPSBuildExecutionSegment capacity weight work batchWork
              currentTime nextBatchDelay := by
          simpa [finiteGPSRunGapSegments, duration, hexternal] using hsegment
        subst segment
        exact finiteGPSBuildExecutionSegment_endpointWorkload_le_weightedCapacityLateBatchUpdate
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          hnextBatchDelay_nonneg
      · have hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
            nextBatchDelay := by
          simpa [duration] using hexternal
        have hnext_work_nonneg : ∀ j, 0 <=
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j := by
          exact finiteGPSNextEventState_nonneg_of_internal hinternal
        have hremaining_delay_nonneg : 0 <= nextBatchDelay - duration := by
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
          simp [finiteGPSRunGapSegments, duration, hexternal]
        intro segment hsegment
        rw [hlist] at hsegment
        rcases List.mem_cons.mp hsegment with hhead | htail
        · subst segment
          exact finiteGPSBuildExecutionSegment_endpointWorkload_le_weightedCapacityLateBatchUpdate
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            hnextBatchDelay_nonneg
        · exact ih
            (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
            hnext_work_nonneg hremaining_delay_nonneg segment htail

/-- The complete finite batch runner emits one literal chronological segment
chain when its listed external batches are chronological and nonnegative.
Each gap reaches its actual scheduled endpoint under the executable
active-class fuel bound; the proof concatenates only at that verified
post-batch endpoint. -/
theorem finiteGPSRunBatchTraceSegments_chainFrom
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    FiniteGPSExecutionSegmentsChainFrom currentTime work
      (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times) := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments, FiniteGPSExecutionSegmentsChainFrom]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : forall j, 0 <= batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 <= batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true /\ gap.remainingDelay = 0 := by
        simpa [gap, gapFuel] using
          (finiteGPSRunGap_terminates_of_activeCard_lt
            gapFuel (capacity := capacity) (weight := weight) (work := work)
            (batchWork := batchWork eventTime)
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            (sub_nonneg.mpr hdelay) (Nat.lt_succ_self _))
      have hgap_work_nonneg : forall j, 0 <= gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail_chain := ih (currentTime := eventTime) (work := gap.workload)
        hgap_work_nonneg hchronological_tail hbatch_tail
      have hgap_chain : FiniteGPSExecutionSegmentsChainFrom currentTime work
          (finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime)) := by
        exact finiteGPSRunGapSegments_chainFrom gapFuel capacity weight work
          (batchWork eventTime) currentTime (eventTime - currentTime)
      have hgap_final_work : finiteGPSExecutionSegmentsFinalWorkload work
          (finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime)) =
          gap.workload := by
        simpa [gap] using
          (finiteGPSExecutionSegmentsFinalWorkload_runGapSegments gapFuel capacity
            weight work (batchWork eventTime) currentTime (eventTime - currentTime))
      have hgap_final_time : finiteGPSExecutionSegmentsFinalTime currentTime
          (finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime)) = eventTime := by
        calc
          finiteGPSExecutionSegmentsFinalTime currentTime
              (finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime)) =
              currentTime + (eventTime - currentTime) - gap.remainingDelay := by
                simpa [gap] using
                  (finiteGPSExecutionSegmentsFinalTime_runGapSegments gapFuel capacity
                    weight work (batchWork eventTime) currentTime
                    (eventTime - currentTime))
          _ = eventTime := by rw [hgap_terminates.2]; ring
      have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
          currentTime work (eventTime :: times) =
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
        simpa [gap, gapFuel] using
          (finiteGPSRunBatchTraceSegments_cons_of_batchApplied capacity weight
            batchWork currentTime work eventTime times hgap_terminates.1)
      rw [htrace]
      apply finiteGPSExecutionSegmentsChainFrom_append currentTime work
        (finiteGPSRunGapSegments gapFuel capacity weight work
          (batchWork eventTime) currentTime (eventTime - currentTime))
        (finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
          gap.workload times) hgap_chain
      simpa only [hgap_final_time, hgap_final_work] using htail_chain

/-- Every segment emitted by a complete chronological finite batch trace
inherits the actual GPS guaranteed-rate local comparison.  This is a lift of
the semantic per-gap result, not a new recurrence: batches remain at their
literal right endpoints and all other classes may receive arbitrary
nonnegative work there. -/
theorem finiteGPSRunBatchTraceSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real} {i : Class}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    ∀ segment ∈ finiteGPSRunBatchTraceSegments capacity weight batchWork
      currentTime work times,
      segment.endpointWorkload i <=
        lateBatchUpdate (segment.startWorkload i)
          (capacity * weight i * segment.duration) (segment.endpointBatch i) := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceSegments]
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : forall j, 0 <= batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 <= batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true /\ gap.remainingDelay = 0 := by
        simpa [gap, gapFuel] using
          (finiteGPSRunGap_terminates_of_activeCard_lt
            gapFuel (capacity := capacity) (weight := weight) (work := work)
            (batchWork := batchWork eventTime)
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            (sub_nonneg.mpr hdelay) (Nat.lt_succ_self _))
      have hgap_work_nonneg : forall j, 0 <= gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have hgap_local :=
        finiteGPSRunGapSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
          gapFuel (capacity := capacity) (weight := weight) (work := work)
          (batchWork := batchWork eventTime) (currentTime := currentTime) (i := i)
          hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
          (sub_nonneg.mpr hdelay)
      have htail_local := ih (currentTime := eventTime) (work := gap.workload)
        hgap_work_nonneg hchronological_tail hbatch_tail
      have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
          currentTime work (eventTime :: times) =
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
        simpa [gap, gapFuel] using
          (finiteGPSRunBatchTraceSegments_cons_of_batchApplied capacity weight
            batchWork currentTime work eventTime times hgap_terminates.1)
      intro segment hsegment
      rw [htrace] at hsegment
      rcases List.mem_append.mp hsegment with hgap_segment | htail_segment
      · exact hgap_local segment hgap_segment
      · exact htail_local segment htail_segment

/-- The endpoint-workload fold of a complete finite segment trace is the
workload returned by the executable batch runner.  This identifies the
comparison's left-hand side with the actual runner state, rather than an
auxiliary recurrence. -/
theorem finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    finiteGPSExecutionSegmentsFinalWorkload work
      (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times) =
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).workload := by
  induction times generalizing currentTime work with
  | nil => rfl
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : forall j, 0 <= batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 <= batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true /\ gap.remainingDelay = 0 := by
        simpa [gap, gapFuel] using
          (finiteGPSRunGap_terminates_of_activeCard_lt
            gapFuel (capacity := capacity) (weight := weight) (work := work)
            (batchWork := batchWork eventTime)
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            (sub_nonneg.mpr hdelay) (Nat.lt_succ_self _))
      have hgap_work_nonneg : forall j, 0 <= gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail_final := ih (currentTime := eventTime) (work := gap.workload)
        hgap_work_nonneg hchronological_tail hbatch_tail
      have hgap_final_work : finiteGPSExecutionSegmentsFinalWorkload work
          (finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime)) =
          gap.workload := by
        simpa [gap] using
          (finiteGPSExecutionSegmentsFinalWorkload_runGapSegments gapFuel capacity
            weight work (batchWork eventTime) currentTime (eventTime - currentTime))
      have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
          currentTime work (eventTime :: times) =
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
        simpa [gap, gapFuel] using
          (finiteGPSRunBatchTraceSegments_cons_of_batchApplied capacity weight
            batchWork currentTime work eventTime times hgap_terminates.1)
      funext i
      calc
        finiteGPSExecutionSegmentsFinalWorkload work
            (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times)) i =
            finiteGPSExecutionSegmentsFinalWorkload gap.workload
              (finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
                gap.workload times) i := by
              rw [htrace, finiteGPSExecutionSegmentsFinalWorkload_append,
                hgap_final_work]
        _ = (finiteGPSRunBatchTrace capacity weight batchWork eventTime
              gap.workload times).workload i := congrFun htail_final i
        _ = (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
              (eventTime :: times)).workload i := by
              rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
                currentTime work eventTime times (by simpa [gap, gapFuel] using hgap_terminates.1)]

/-- The concrete segment ledger ends at exactly the finite batch runner's
actual clock.  This is the time counterpart of
`finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments`; it permits a
later computational horizon fence to be appended at the literal runner
endpoint rather than at a synthetic source event. -/
theorem finiteGPSExecutionSegmentsFinalTime_runBatchTraceSegments
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    finiteGPSExecutionSegmentsFinalTime currentTime
      (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times) =
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).currentTime := by
  induction times generalizing currentTime work with
  | nil => rfl
  | cons eventTime times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 <= batchWork eventTime j := by
        intro j
        exact hbatch_nonneg eventTime (by simp) j
      have hbatch_tail : ∀ laterTime ∈ times, ∀ j,
          0 <= batchWork laterTime j := by
        intro laterTime hlaterTime j
        exact hbatch_nonneg laterTime (by simp [hlaterTime]) j
      let gapFuel := (finiteGPSActiveClasses work).card + 1
      let gap := finiteGPSRunGap gapFuel capacity weight work
        (batchWork eventTime) (eventTime - currentTime)
      have hgap_terminates : gap.batchApplied = true /\ gap.remainingDelay = 0 := by
        simpa [gap, gapFuel] using
          (finiteGPSRunGap_terminates_of_activeCard_lt
            gapFuel (capacity := capacity) (weight := weight) (work := work)
            (batchWork := batchWork eventTime)
            hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            (sub_nonneg.mpr hdelay) (Nat.lt_succ_self _))
      have hgap_work_nonneg : ∀ j, 0 <= gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg gapFuel capacity weight work
          (batchWork eventTime) (eventTime - currentTime) hwork_nonneg hbatch_head
      have htail_final := ih (currentTime := eventTime) (work := gap.workload)
        hgap_work_nonneg hchronological_tail hbatch_tail
      have hgap_final_time : finiteGPSExecutionSegmentsFinalTime currentTime
          (finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime)) = eventTime := by
        calc
          finiteGPSExecutionSegmentsFinalTime currentTime
              (finiteGPSRunGapSegments gapFuel capacity weight work
                (batchWork eventTime) currentTime (eventTime - currentTime)) =
              currentTime + (eventTime - currentTime) - gap.remainingDelay := by
                simpa [gap] using
                  (finiteGPSExecutionSegmentsFinalTime_runGapSegments gapFuel capacity
                    weight work (batchWork eventTime) currentTime
                    (eventTime - currentTime))
          _ = eventTime := by rw [hgap_terminates.2]; ring
      have htrace : finiteGPSRunBatchTraceSegments capacity weight batchWork
          currentTime work (eventTime :: times) =
          finiteGPSRunGapSegments gapFuel capacity weight work
            (batchWork eventTime) currentTime (eventTime - currentTime) ++
            finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
              gap.workload times := by
        simpa [gap, gapFuel] using
          (finiteGPSRunBatchTraceSegments_cons_of_batchApplied capacity weight batchWork
            currentTime work eventTime times hgap_terminates.1)
      calc
        finiteGPSExecutionSegmentsFinalTime currentTime
            (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work
              (eventTime :: times)) =
            finiteGPSExecutionSegmentsFinalTime eventTime
              (finiteGPSRunBatchTraceSegments capacity weight batchWork eventTime
                gap.workload times) := by
              rw [htrace, finiteGPSExecutionSegmentsFinalTime_append, hgap_final_time]
        _ = (finiteGPSRunBatchTrace capacity weight batchWork eventTime
              gap.workload times).currentTime := htail_final
        _ = (finiteGPSRunBatchTrace capacity weight batchWork currentTime work
              (eventTime :: times)).currentTime := by
              rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
                currentTime work eventTime times (by simpa [gap, gapFuel] using hgap_terminates.1)]

/-- Empty-start finite-trace comparison for the executable GPS batch runner.
The scalar side consumes exactly the runner's emitted interval ledger, using
the class's actual endpoint batches and the guaranteed rate
`capacity * weight i`.  This theorem is deterministic and makes no claim
about a source process, an infinite extension, or a response-time tail. -/
theorem finiteGPSRunBatchTrace_workload_le_constantRateSegmentComparator_of_initialZero
    {capacity : Real} {weight work : Class -> Real}
    {batchWork : Real -> Class -> Real} {currentTime : Real} {i : Class}
    (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : forall j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight <= 1)
    (hwork_nonneg : forall j, 0 <= work j)
    (hinitial_zero : work i = 0)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ eventTime ∈ times, ∀ j, 0 <= batchWork eventTime j) :
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).workload i <=
      finiteGPSConstantRateSegmentComparator (capacity * weight i) i
        (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times) := by
  have hfinal := finiteGPSExecutionSegmentsFinalWorkload_runBatchTraceSegments
    (capacity := capacity) (weight := weight) (work := work) (batchWork := batchWork)
    (currentTime := currentTime) times hcapacity hweight_pos htotal_weight_le_one
    hwork_nonneg hchronological hbatch_nonneg
  rw [<- hfinal]
  apply finiteGPSExecutionSegmentsFinalWorkload_le_constantRateComparator
    work (capacity * weight i) i
      (finiteGPSRunBatchTraceSegments capacity weight batchWork currentTime work times)
      currentTime hinitial_zero
  · exact finiteGPSRunBatchTraceSegments_chainFrom times hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg
  · exact finiteGPSRunBatchTraceSegments_endpointWorkload_le_weightedCapacityLateBatchUpdate
      times hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological
      hbatch_nonneg

end

end AppliedModelingLib.Probability.Queueing
