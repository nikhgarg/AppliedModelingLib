import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Reset
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FenceSplit
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedFiniteGPSFCFS
import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedResetPartition
import Mathlib.Tactic

/-!
# Deterministic restart of a tagged admitted finite GPS trace

This module connects the literal half-open source split at an arbitrary time
`resetTime` to the executable finite GPS runner.  It proves only deterministic
conditional statements: if the finite prefix runner has actually reached the
reset time with zero workload, then the full source run has the corresponding
zero-state suffix form.  It does not assert that such a reset occurs, add a
zero-work fence, or make a stationary, Palm, response-time, or tail claim.

An actual source batch at `resetTime` remains in the suffix, as established by
the imported source-ledger partition.
-/

namespace LG24ServiceLevelAgreements

open AppliedModelingLib.Probability.PoissonProcess
open AppliedModelingLib.Probability.Queueing
open scoped BigOperators NNReal

noncomputable section

namespace SLA2026BoroughQueueingInput

variable {Category : Type*} [Fintype Category] [DecidableEq Category]

/-- The real tagged external-batch trace has exactly the literal prefix/suffix
time decomposition at an arbitrary half-open reset boundary. -/
theorem taggedAdmittedExternalBatchTrace_times_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times =
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times := by
  exact taggedAdmittedBatchTimeTrace_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon

omit [DecidableEq Category] in
/-- A paper-local extensionality fact for the executable finite runner: only
the batch vectors at listed trace times affect its result.  This stays local
because the present use is the literal tagged source restriction at a reset
boundary. -/
private theorem finiteGPSRunBatchTrace_eq_of_batchWork_eq_on_trace
    (capacity : ℝ) (weight : Category → ℝ)
    (leftBatchWork rightBatchWork : ℝ → Category → ℝ)
    (currentTime : ℝ) (work : Category → ℝ) (times : List ℝ)
    (hbatch_eq : ∀ eventTime ∈ times,
      leftBatchWork eventTime = rightBatchWork eventTime) :
    finiteGPSRunBatchTrace capacity weight leftBatchWork currentTime work times =
      finiteGPSRunBatchTrace capacity weight rightBatchWork currentTime work times := by
  induction times generalizing currentTime work with
  | nil =>
      rfl
  | cons eventTime times ih =>
      have hhead : leftBatchWork eventTime = rightBatchWork eventTime :=
        hbatch_eq eventTime (by simp)
      have htail : ∀ laterTime ∈ times,
          leftBatchWork laterTime = rightBatchWork laterTime := by
        intro laterTime hlaterTime
        exact hbatch_eq laterTime (by simp [hlaterTime])
      rw [finiteGPSRunBatchTrace]
      rw [hhead]
      split
      · rename_i hbatchApplied
        rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight rightBatchWork
          currentTime work eventTime times hbatchApplied]
        rw [ih (currentTime := eventTime)
          (work := (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (rightBatchWork eventTime)
            (eventTime - currentTime)).workload) htail]
      · rename_i hbatchNotApplied
        rw [finiteGPSRunBatchTrace_cons_of_not_batchApplied capacity weight rightBatchWork
          currentTime work eventTime times hbatchNotApplied]

/-- Running the full batch function over the literal prefix times is exactly
the tagged source run built from the prefix ledger. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hreset_horizon : resetTime ≤ horizon) :
    finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z) =
      taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork := by
  unfold taggedAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  apply finiteGPSRunBatchTrace_eq_of_batchWork_eq_on_trace
  intro eventTime heventTime
  have heventTime_lt : eventTime < resetTime := by
    exact taggedAdmittedBatchTimes_prefix_lt_reset start resetTime target z htarget_good
      eventTime ((Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp heventTime)
  exact taggedAdmittedBatchAt_eq_prefix_of_lt_reset
    start resetTime horizon target z htarget_good hreset_horizon eventTime heventTime_lt

/-- Running the full batch function over the literal suffix times is exactly
the tagged source run built from the suffix ledger. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_suffix_eq_fullBatchTrace
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) :
    finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        resetTime initialWork
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) =
      taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
        capacity weight initialWork := by
  unfold taggedAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  apply finiteGPSRunBatchTrace_eq_of_batchWork_eq_on_trace
  intro eventTime heventTime
  have heventTime_ge : resetTime ≤ eventTime := by
    exact taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime ((Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp heventTime)
  exact taggedAdmittedBatchAt_eq_suffix_of_reset_le
    start resetTime horizon target z htarget_good hstart_reset eventTime heventTime_ge

omit [Fintype Category] in
/-- The source-identified FCFS endpoint record before the reset is unchanged
when the full source ledger is restricted to its literal prefix. -/
theorem taggedAdmittedFCFSJobsAt_eq_prefix_of_lt_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hreset_horizon : resetTime ≤ horizon)
    (eventTime : ℝ) (heventTime : eventTime < resetTime) :
    taggedAdmittedFCFSJobsAt start horizon target z eventTime =
      taggedAdmittedFCFSJobsAt start resetTime target z eventTime := by
  unfold taggedAdmittedFCFSJobsAt
  congr 1
  funext k
  unfold taggedAdmittedJobIndicesAt
  rw [taggedAdmittedArrivalIndicesBetween_filter_eq_prefix_of_lt_reset
    start resetTime horizon target z htarget_good hreset_horizon eventTime heventTime k]

omit [Fintype Category] in
/-- The source-identified FCFS endpoint record at or after the reset is
unchanged when the full source ledger is restricted to its literal suffix. -/
theorem taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime)
    (eventTime : ℝ) (heventTime : resetTime ≤ eventTime) :
    taggedAdmittedFCFSJobsAt start horizon target z eventTime =
      taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime := by
  unfold taggedAdmittedFCFSJobsAt
  congr 1
  funext k
  unfold taggedAdmittedJobIndicesAt
  rw [taggedAdmittedArrivalIndicesBetween_filter_eq_suffix_of_reset_le
    start resetTime horizon target z htarget_good hstart_reset eventTime heventTime k]

/-- The chronological list of literal source-identified endpoint batches
factors at the reset time.  This is only an external-source-batch statement;
it does not insert a computational fence into the segment runner. -/
theorem taggedAdmittedFCFSSourceBatchTrace_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon) :
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.map
        (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) =
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start resetTime target z eventTime) ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime) := by
  have hprefix_map :
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) =
        (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start resetTime target z eventTime) := by
    apply List.map_congr_left
    intro eventTime heventTime
    apply taggedAdmittedFCFSJobsAt_eq_prefix_of_lt_reset
      start resetTime horizon target z htarget_good hreset_horizon eventTime
    apply taggedAdmittedBatchTimes_prefix_lt_reset start resetTime target z htarget_good
      eventTime
    exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
      (by simpa [taggedAdmittedExternalBatchTrace,
        taggedAdmittedBatchTimeTrace] using heventTime)
  have hsuffix_map :
      (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) =
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime) := by
    apply List.map_congr_left
    intro eventTime heventTime
    apply taggedAdmittedFCFSJobsAt_eq_suffix_of_reset_le
      start resetTime horizon target z htarget_good hstart_reset eventTime
    apply taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime
    exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp
      (by simpa [taggedAdmittedExternalBatchTrace,
        taggedAdmittedBatchTimeTrace] using heventTime)
  rw [taggedAdmittedExternalBatchTrace_times_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon,
    List.map_append, hprefix_map, hsuffix_map]

/-- The actual source-labelled FCFS external endpoint batches emitted by the
finite tagged GPS construction have the same literal reset-time partition.
Internal depletion endpoints remain excluded by the existing external-batch
projection. -/
theorem taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_reset_partition
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    taggedAdmittedFiniteGPSExternalEndpointJobBatches
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) =
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start resetTime target z eventTime) ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime) := by
  calc
    taggedAdmittedFiniteGPSExternalEndpointJobBatches
      (taggedAdmittedFiniteGPSPreTerminalFCFSSteps
        start horizon target z htarget_good capacity weight initialWork) =
      (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times.map
        (fun eventTime => taggedAdmittedFCFSJobsAt start horizon target z eventTime) :=
      taggedAdmittedFiniteGPSPreTerminalFCFSSteps_externalEndpointJobBatches_eq_sourceBatchTrace
        start horizon target z htarget_good capacity weight initialWork
        hcapacity hweight_pos htotal_weight_le_one hinit_nonneg hsource_work_nonneg
    _ =
      (taggedAdmittedExternalBatchTrace start resetTime target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt start resetTime target z eventTime) ++
        (taggedAdmittedExternalBatchTrace resetTime horizon target z htarget_good).times.map
          (fun eventTime => taggedAdmittedFCFSJobsAt resetTime horizon target z eventTime) :=
      taggedAdmittedFCFSSourceBatchTrace_reset_partition
        start resetTime horizon target z htarget_good hstart_reset hreset_horizon

/-- The full literal tagged finite GPS run is the generic restart runner over
the exact source-trace prefix and suffix.  This is a deterministic trace
factorization; it does not say that the prefix is empty at `resetTime`. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_restart_at_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      finiteGPSRunBatchTraceRestart capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) := by
  have hchronological :=
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  rw [taggedAdmittedExternalBatchTrace_times_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon] at hchronological
  unfold taggedAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  rw [show (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times =
      (taggedAdmittedBatchTimeTrace start resetTime target z) ++
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) by
    exact taggedAdmittedExternalBatchTrace_times_reset_partition
      start resetTime horizon target z htarget_good hstart_reset hreset_horizon]
  apply finiteGPSRunBatchTrace_append_eq_restart
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · exact hinit_nonneg
  · exact hchronological
  · intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg
      start horizon target z hsource_work_nonneg eventTime j

/-- If the tagged source prefix has actually run to `resetTime` and emptied
every class, the full pre-terminal source run has the deterministic
zero-workload suffix form.  The reset condition is an explicit hypothesis,
not a claim about the stochastic source model. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_zero_suffix_of_prefix_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hprefix_currentTime :
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)).currentTime = resetTime)
    (hprefix_workload_zero : ∀ i,
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)).workload i = 0) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      { workload :=
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).workload
        currentTime :=
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).currentTime
        service := fun i =>
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            start initialWork
            (taggedAdmittedBatchTimeTrace start resetTime target z)).service i +
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).service i } := by
  have hchronological :=
    (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).chronological
  rw [taggedAdmittedExternalBatchTrace_times_reset_partition
    start resetTime horizon target z htarget_good hstart_reset hreset_horizon] at hchronological
  unfold taggedAdmittedFiniteGPSPreTerminalRun finiteGPSRunExternalBatchTrace
  rw [show (taggedAdmittedExternalBatchTrace start horizon target z htarget_good).times =
      (taggedAdmittedBatchTimeTrace start resetTime target z) ++
        (taggedAdmittedBatchTimeTrace resetTime horizon target z) by
    exact taggedAdmittedExternalBatchTrace_times_reset_partition
      start resetTime horizon target z htarget_good hstart_reset hreset_horizon]
  apply finiteGPSRunBatchTrace_append_eq_zero_suffix_of_prefix_reset
  · exact hcapacity
  · exact hweight_pos
  · exact htotal_weight_le_one
  · exact hinit_nonneg
  · exact hchronological
  · intro eventTime _ j
    exact taggedAdmittedBatchAt_nonneg
      start horizon target z hsource_work_nonneg eventTime j
  · exact hprefix_currentTime
  · exact hprefix_workload_zero

/-- The source-facing reset law.  If the actual tagged prefix execution has
reached `resetTime` with zero workload, the actual full tagged source run is
the prefix service followed by the actual zero-state suffix execution.  An
event precisely at `resetTime` is included in that suffix execution. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_source_zero_suffix_of_prefix_reset
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hprefix_currentTime :
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).currentTime = resetTime)
    (hprefix_workload_zero : ∀ i,
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).workload i = 0) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      { workload :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).workload
        currentTime :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
            capacity weight initialWork).service i +
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).service i } := by
  have hprefix_eq := taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
    start resetTime horizon target z htarget_good capacity weight initialWork hreset_horizon
  have hsuffix_eq := taggedAdmittedFiniteGPSPreTerminalRun_suffix_eq_fullBatchTrace
    start resetTime horizon target z htarget_good capacity weight (fun _ => 0) hstart_reset
  have hraw_prefix_currentTime :
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)).currentTime = resetTime := by
    rw [hprefix_eq]
    exact hprefix_currentTime
  have hraw_prefix_workload_zero : ∀ i,
      (finiteGPSRunBatchTrace capacity weight
        (taggedAdmittedBatchAt start horizon target z)
        start initialWork
        (taggedAdmittedBatchTimeTrace start resetTime target z)).workload i = 0 := by
    intro i
    rw [hprefix_eq]
    exact hprefix_workload_zero i
  calc
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      { workload :=
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).workload
        currentTime :=
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).currentTime
        service := fun i =>
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            start initialWork
            (taggedAdmittedBatchTimeTrace start resetTime target z)).service i +
          (finiteGPSRunBatchTrace capacity weight
            (taggedAdmittedBatchAt start horizon target z)
            resetTime (fun _ => 0)
            (taggedAdmittedBatchTimeTrace resetTime horizon target z)).service i } :=
        taggedAdmittedFiniteGPSPreTerminalRun_eq_zero_suffix_of_prefix_reset
          start resetTime horizon target z htarget_good capacity weight initialWork
          hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
          hinit_nonneg hsource_work_nonneg hraw_prefix_currentTime hraw_prefix_workload_zero
    _ =
      { workload :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).workload
        currentTime :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).currentTime
        service := fun i =>
          (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
            capacity weight initialWork).service i +
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).service i } := by
        rw [hprefix_eq, hsuffix_eq]

/-- A usable computational-reset bridge for the literal tagged source run.
When the source suffix contains a next batch and the prefix has enough
remaining capacity to drain before `resetTime`, the unfenced full source run
equals the actual prefix closed by the computational zero-work fence followed
by the literal suffix source run.  A source batch exactly at `resetTime` is
the first suffix batch and is applied at zero delay after the fence.

The nonempty-suffix condition is necessary for equality with the *unfenced*
pre-terminal run: if no later source batch exists, that run deliberately stops
at its last source time rather than advancing its clock to the computational
fence. -/
theorem taggedAdmittedFiniteGPSPreTerminalRun_eq_closed_prefix_then_source_suffix_of_aggregate_drain
    (start resetTime horizon : ℝ) (target : Category)
    (z : StationaryAdmittedTargetPassiveTaggedInput target)
    (htarget_good : palmTaggedArrivalGoodCarrier z.1.1)
    (capacity : ℝ) (weight initialWork : Category → ℝ)
    (hstart_reset : start ≤ resetTime) (hreset_horizon : resetTime ≤ horizon)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ j, 0 ≤ initialWork j)
    (hsource_work_nonneg : TaggedAdmittedSourceWorkNonnegative target z)
    (hsuffix_nonempty : taggedAdmittedBatchTimeTrace resetTime horizon target z ≠ [])
    (hprefix_aggregate_drain : finiteGPSAggregateWork
      (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
        capacity weight initialWork).workload ≤
      capacity * (resetTime -
        (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
          capacity weight initialWork).currentTime)) :
    taggedAdmittedFiniteGPSPreTerminalRun start horizon target z htarget_good
        capacity weight initialWork =
      { workload :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).workload
        currentTime :=
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).currentTime
        service := fun i =>
          (finiteGPSCloseAtHorizon capacity weight
            (taggedAdmittedFiniteGPSPreTerminalRun start resetTime target z htarget_good
              capacity weight initialWork) resetTime).service i +
          (taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
            capacity weight (fun _ => 0)).service i } := by
  let prefixRun := taggedAdmittedFiniteGPSPreTerminalRun
    start resetTime target z htarget_good capacity weight initialWork
  let suffixTimes := taggedAdmittedBatchTimeTrace resetTime horizon target z
  have hsuffixTimes_ne : suffixTimes ≠ [] := by
    simpa [suffixTimes] using hsuffix_nonempty
  obtain ⟨eventTime, tail, hsuffixTimes⟩ :
      ∃ eventTime tail, suffixTimes = eventTime :: tail := by
    cases htimes : suffixTimes with
    | nil => exact (hsuffixTimes_ne htimes).elim
    | cons eventTime tail => exact ⟨eventTime, tail, rfl⟩
  have hsourceSuffixTimes :
      taggedAdmittedBatchTimeTrace resetTime horizon target z = eventTime :: tail := by
    simpa [suffixTimes] using hsuffixTimes
  have hprefix_nonneg : ∀ i, 0 ≤ prefixRun.workload i := by
    intro i
    simpa [prefixRun] using
      (taggedAdmittedFiniteGPSPreTerminalRun_workload_nonneg
        start resetTime target z htarget_good capacity weight initialWork
        hinit_nonneg hsource_work_nonneg i)
  have hprefix_currentTime_le : prefixRun.currentTime ≤ resetTime := by
    simpa [prefixRun] using
      (taggedAdmittedFiniteGPSPreTerminalRun_currentTime_le_horizon
        start resetTime target z htarget_good capacity weight initialWork hstart_reset)
  have heventTime_mem : eventTime ∈ taggedAdmittedBatchTimeTrace resetTime horizon target z := by
    rw [hsourceSuffixTimes]
    simp
  have heventTime_ge : resetTime ≤ eventTime := by
    apply taggedAdmittedBatchTimes_suffix_ge_reset resetTime horizon target z htarget_good
      eventTime
    exact (Finset.mem_sort (fun left right : ℝ => left ≤ right)).mp heventTime_mem
  have hprefix_eq := taggedAdmittedFiniteGPSPreTerminalRun_prefix_eq_fullBatchTrace
    start resetTime horizon target z htarget_good capacity weight initialWork hreset_horizon
  have hsuffix_eq := taggedAdmittedFiniteGPSPreTerminalRun_suffix_eq_fullBatchTrace
    start resetTime horizon target z htarget_good capacity weight (fun _ => 0) hstart_reset
  have hfull_restart := taggedAdmittedFiniteGPSPreTerminalRun_eq_restart_at_reset
    start resetTime horizon target z htarget_good capacity weight initialWork
    hstart_reset hreset_horizon hcapacity hweight_pos htotal_weight_le_one
    hinit_nonneg hsource_work_nonneg
  have hclosed_currentTime :
      (finiteGPSCloseAtHorizon capacity weight prefixRun resetTime).currentTime = resetTime := by
    apply finiteGPSCloseAtHorizon_currentTime capacity weight prefixRun resetTime
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg hprefix_currentTime_le
  have hclosed_suffix_eq :
      finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z)
        (finiteGPSCloseAtHorizon capacity weight prefixRun resetTime).currentTime
        (finiteGPSCloseAtHorizon capacity weight prefixRun resetTime).workload
        (eventTime :: tail) =
      taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
        capacity weight (fun _ => 0) := by
    calc
      finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z)
          (finiteGPSCloseAtHorizon capacity weight prefixRun resetTime).currentTime
          (finiteGPSCloseAtHorizon capacity weight prefixRun resetTime).workload
          (eventTime :: tail) =
        finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z)
          resetTime (fun _ => 0) (eventTime :: tail) := by
            apply finiteGPSRunBatchTrace_after_horizon_reset_eq_zero
              capacity weight (taggedAdmittedBatchAt start horizon target z)
              prefixRun resetTime (eventTime :: tail)
              hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
              hprefix_currentTime_le hprefix_aggregate_drain
      _ = taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
          capacity weight (fun _ => 0) := by
        rw [← hsourceSuffixTimes]
        exact hsuffix_eq
  have hraw_suffix_eq :
      finiteGPSRunBatchTrace capacity weight (taggedAdmittedBatchAt start horizon target z)
        resetTime (finiteGPSHorizonFence capacity weight prefixRun resetTime).workload
        (eventTime :: tail) =
      taggedAdmittedFiniteGPSPreTerminalRun resetTime horizon target z htarget_good
        capacity weight (fun _ => 0) := by
    have hclosed_suffix_eq' := hclosed_suffix_eq
    rw [hclosed_currentTime] at hclosed_suffix_eq'
    simpa [finiteGPSCloseAtHorizon] using hclosed_suffix_eq'
  have hfence_continuation :=
    finiteGPSRunBatchTrace_cons_eq_afterZeroFence_of_aggregate_drain
      capacity weight prefixRun.workload (taggedAdmittedBatchAt start horizon target z)
      prefixRun.currentTime resetTime eventTime tail
      hcapacity hweight_pos htotal_weight_le_one hprefix_nonneg
      hprefix_currentTime_le heventTime_ge hprefix_aggregate_drain
  rw [hfull_restart]
  simp only [finiteGPSRunBatchTraceRestart]
  rw [hprefix_eq, hsourceSuffixTimes]
  rw [hfence_continuation]
  unfold finiteGPSRunBatchTraceAfterZeroFence
  dsimp only
  have hfence_eq :
      finiteGPSRunGap ((finiteGPSActiveClasses prefixRun.workload).card + 1)
        capacity weight prefixRun.workload (fun _ => 0)
        (resetTime - prefixRun.currentTime) =
      finiteGPSHorizonFence capacity weight prefixRun resetTime := rfl
  rw [hfence_eq]
  rw [hraw_suffix_eq]
  rw [FiniteGPSBatchTraceResult.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  simp [finiteGPSCloseAtHorizon, prefixRun, add_assoc]

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
