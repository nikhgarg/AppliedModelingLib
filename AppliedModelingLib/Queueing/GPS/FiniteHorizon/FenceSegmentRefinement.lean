import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonTerminalBatch
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.HorizonSegments
import Mathlib.Tactic

/-!
# Concrete segment factorization at a finite GPS drain fence

An inserted zero-work fence can split an idle interval into a computational
endpoint and a later real external endpoint.  The raw GPS segment lists are
therefore not generally equal: `endpointIsExternalBatch` and zero-service
idle segmentation encode bookkeeping choices rather than FCFS behavior.

This module exposes the common active prefix through an observation relation
that retains the fields used by concrete FCFS accounting and completion
records: start time, duration, class rate, and service increment.  Endpoint
job annotations remain outside the generic scheduler; a caller must attach
literal empty job batches to the zero-batch lead-ins and the same real job
batch to the two displayed terminals.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- The concrete fields of a GPS segment that are observable to the FCFS
executor and its completion records.  In particular, the relation retains
both endpoints of the service interval through `startTime` and `duration`,
but intentionally ignores the Boolean source/bookkeeping tag. -/
def FiniteGPSExecutionSegment.FCFSObservableEq
    (left right : FiniteGPSExecutionSegment Class) : Prop :=
  left.startTime = right.startTime ∧
    left.duration = right.duration ∧
    left.classRate = right.classRate ∧
    left.serviceIncrement = right.serviceIncrement

/-- The active part of a zero-batch finite GPS gap.  Unlike the ordinary gap
runner, this helper stops once the workload is already empty, instead of
emitting its final zero-service endpoint segment.  It never carries a source
batch. -/
def finiteGPSRunGapActiveSegments
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) : List (FiniteGPSExecutionSegment Class) :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
      if hactive : (finiteGPSActiveClasses work).Nonempty then
        let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
        let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
        let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
          nextBatchDelay
        if duration = nextBatchDelay then
          [segment]
        else
          segment :: finiteGPSRunGapActiveSegments fuel capacity weight nextWork
            (currentTime + duration) (nextBatchDelay - duration)
      else
        []

/-- Equal next-event durations produce FCFS-observationally equal concrete
segments when the start workload and clock agree, regardless of the pending
endpoint batch. -/
theorem finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
    (capacity : ℝ) (weight work leftBatch rightBatch : Class → ℝ)
    (currentTime leftDelay rightDelay : ℝ)
    (hduration : finiteGPSNextStepDuration capacity weight work leftDelay =
      finiteGPSNextStepDuration capacity weight work rightDelay) :
    FiniteGPSExecutionSegment.FCFSObservableEq
      (finiteGPSBuildExecutionSegment capacity weight work leftBatch currentTime leftDelay)
      (finiteGPSBuildExecutionSegment capacity weight work rightBatch currentTime rightDelay) := by
  simp [FiniteGPSExecutionSegment.FCFSObservableEq,
    finiteGPSBuildExecutionSegment, hduration]

/-- At a strictly internal event, extending the pending external delay leaves
the chosen duration unchanged.  This is a local event-kernel fact, not an
inference from a final runner state. -/
theorem finiteGPSNextStepDuration_eq_of_internal_of_le
    (capacity : ℝ) (weight work : Class → ℝ)
    (shortDelay longDelay : ℝ)
    (hinternal : finiteGPSNextStepDuration capacity weight work shortDelay ≠ shortDelay)
    (hshort_le_long : shortDelay ≤ longDelay) :
    finiteGPSNextStepDuration capacity weight work longDelay =
      finiteGPSNextStepDuration capacity weight work shortDelay := by
  have hactive : (finiteGPSActiveClasses work).Nonempty :=
    finiteGPSActiveClasses_nonempty_of_internal hinternal
  have hearliest_lt_short : finiteGPSEarliestEmptyDelay capacity weight work < shortDelay := by
    by_contra hnot
    have hshort_le_earliest : shortDelay ≤
        finiteGPSEarliestEmptyDelay capacity weight work := le_of_not_gt hnot
    apply hinternal
    simp [finiteGPSNextStepDuration, hactive,
      min_eq_left hshort_le_earliest]
  have hearliest_le_long : finiteGPSEarliestEmptyDelay capacity weight work ≤ longDelay :=
    hearliest_lt_short.le.trans hshort_le_long
  simp [finiteGPSNextStepDuration, hactive,
    min_eq_right hearliest_lt_short.le, min_eq_right hearliest_le_long]

/-- Before a strictly internal endpoint, the next state is independent of
the later endpoint batch and of an extension of the pending delay. -/
theorem finiteGPSNextEventState_eq_of_internal_of_le
    (capacity : ℝ) (weight work leftBatch rightBatch : Class → ℝ)
    (shortDelay longDelay : ℝ)
    (hinternal : finiteGPSNextStepDuration capacity weight work shortDelay ≠ shortDelay)
    (hshort_le_long : shortDelay ≤ longDelay) :
    finiteGPSNextEventState capacity weight work rightBatch longDelay =
      finiteGPSNextEventState capacity weight work leftBatch shortDelay := by
  have hduration := finiteGPSNextStepDuration_eq_of_internal_of_le
    capacity weight work shortDelay longDelay hinternal hshort_le_long
  have hlong_internal : finiteGPSNextStepDuration capacity weight work longDelay ≠ longDelay := by
    intro hlong
    have hshort_lt : finiteGPSNextStepDuration capacity weight work shortDelay < shortDelay :=
      lt_of_le_of_ne
        (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work shortDelay)
        hinternal
    have hlong_lt_short : longDelay < shortDelay := by
      calc
        longDelay = finiteGPSNextStepDuration capacity weight work longDelay := hlong.symm
        _ = finiteGPSNextStepDuration capacity weight work shortDelay := hduration
        _ < shortDelay := hshort_lt
    exact (not_lt_of_ge hshort_le_long) hlong_lt_short
  have hlong_batch_zero : ∀ i,
      finiteGPSBatchApplied capacity weight work rightBatch longDelay i = 0 := by
    intro i
    simp [finiteGPSBatchApplied, hlong_internal]
  have hshort_batch_zero : ∀ i,
      finiteGPSBatchApplied capacity weight work leftBatch shortDelay i = 0 := by
    intro i
    simp [finiteGPSBatchApplied, hinternal]
  funext i
  simp only [finiteGPSNextEventState]
  rw [hlong_batch_zero i, hshort_batch_zero i, add_zero, add_zero, hduration]

/-- Changing only the endpoint batch of a bounded GPS gap leaves its emitted
service intervals FCFS-observationally equivalent.  Before the real endpoint
the batch is not yet applied, and at the endpoint it changes only bookkeeping
fields excluded from this relation.  This holds even if the finite fuel ends
before the endpoint. -/
theorem finiteGPSRunGapSegments_forall2_fcfsObservableEq_of_endpointBatch
    (fuel : ℕ) (capacity : ℝ) (weight work leftBatch rightBatch : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    List.Forall₂ FiniteGPSExecutionSegment.FCFSObservableEq
      (finiteGPSRunGapSegments fuel capacity weight work leftBatch
        currentTime nextBatchDelay)
      (finiteGPSRunGapSegments fuel capacity weight work rightBatch
        currentTime nextBatchDelay) := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapSegments]
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let leftSegment := finiteGPSBuildExecutionSegment capacity weight work leftBatch
        currentTime nextBatchDelay
      let rightSegment := finiteGPSBuildExecutionSegment capacity weight work rightBatch
        currentTime nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · have hhead : FiniteGPSExecutionSegment.FCFSObservableEq
            leftSegment rightSegment := by
            apply finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
            rfl
        simpa [finiteGPSRunGapSegments, duration, leftSegment, rightSegment,
          hterminal] using (List.Forall₂.cons hhead List.Forall₂.nil)
      · have hnext :
            finiteGPSNextEventState capacity weight work leftBatch nextBatchDelay =
              finiteGPSNextEventState capacity weight work rightBatch nextBatchDelay := by
            symm
            exact finiteGPSNextEventState_eq_of_internal_of_le
              capacity weight work leftBatch rightBatch nextBatchDelay nextBatchDelay
              (by simpa [duration] using hterminal) le_rfl
        have hhead : FiniteGPSExecutionSegment.FCFSObservableEq
            leftSegment rightSegment := by
            apply finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
            rfl
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work leftBatch nextBatchDelay)
          (currentTime := currentTime + duration)
          (nextBatchDelay := nextBatchDelay - duration)
        rw [hnext] at htail
        simpa [finiteGPSRunGapSegments, duration, leftSegment, rightSegment,
          hterminal, hnext] using List.Forall₂.cons hhead htail

/-- If an active zero-batch event reaches a delay that has enough aggregate
capacity to drain the workload, its post-event state is identically zero.
This is the one-step terminal case used to expose the physical drain point. -/
theorem finiteGPSNextEventState_zero_eq_zero_of_aggregate_drain_of_terminal
    (capacity : ℝ) (weight work : Class → ℝ) (nextBatchDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * nextBatchDelay)
    (hactive : (finiteGPSActiveClasses work).Nonempty)
    (hterminal : finiteGPSNextStepDuration capacity weight work nextBatchDelay =
      nextBatchDelay) :
    ∀ i, finiteGPSNextEventState capacity weight work (fun _ => 0)
      nextBatchDelay i = 0 := by
  let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
    nextBatchDelay
  have hnext_nonneg : ∀ i, 0 ≤ nextWork i := by
    intro i
    exact finiteGPSNextEventState_nonneg (i := i) (by intro j; norm_num)
  have hnext_aggregate : finiteGPSAggregateWork nextWork =
      finiteGPSAggregateWork work -
        capacity * finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
    exact finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
  have hnext_aggregate_le_zero : finiteGPSAggregateWork nextWork ≤ 0 := by
    rw [hnext_aggregate, hterminal]
    linarith
  have hnext_aggregate_eq_zero : finiteGPSAggregateWork nextWork = 0 :=
    le_antisymm hnext_aggregate_le_zero
      (finiteGPSAggregateWork_nonneg hnext_nonneg)
  have hnext_zero : ∀ i, nextWork i = 0 :=
    (finiteGPSAggregateWork_eq_zero_iff_all_work_eq_zero hnext_nonneg).mp
      hnext_aggregate_eq_zero
  simpa [nextWork] using hnext_zero

/-- In the terminal drain case, extending the pending endpoint by any
nonnegative delay does not change the active service duration: it remains the
physical drain duration. -/
theorem finiteGPSNextStepDuration_eq_of_aggregate_drain_terminal_extension
    (capacity : ℝ) (weight work : Class → ℝ)
    (firstDelay secondDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * firstDelay)
    (hactive : (finiteGPSActiveClasses work).Nonempty)
    (hterminal : finiteGPSNextStepDuration capacity weight work firstDelay = firstDelay)
    (hsecond_nonneg : 0 ≤ secondDelay) :
    finiteGPSNextStepDuration capacity weight work (firstDelay + secondDelay) =
      firstDelay := by
  have hnext_zero :=
    finiteGPSNextEventState_zero_eq_zero_of_aggregate_drain_of_terminal
      capacity weight work firstDelay hcapacity hweight_pos htotal_weight_le_one
      hwork_nonneg haggregate_drain hactive hterminal
  have hactive_nonempty := hactive
  obtain ⟨j, hj⟩ := hactive
  have hj_active : 0 < work j := mem_finiteGPSActiveClasses_iff.mp hj
  have hrate_pos : 0 < finiteGPSClassRate capacity weight work j :=
    finiteGPSClassRate_pos_of_active hcapacity hweight_pos htotal_weight_le_one hj_active
  have hremaining_zero : finiteGPSRemainingAfter capacity weight work firstDelay j = 0 := by
    have hstate_zero := hnext_zero j
    simp [finiteGPSNextEventState, finiteGPSBatchApplied, hterminal] at hstate_zero
    simpa [hterminal] using hstate_zero
  have hlinear_zero : work j - finiteGPSClassRate capacity weight work j * firstDelay = 0 := by
    calc
      work j - finiteGPSClassRate capacity weight work j * firstDelay =
          finiteGPSRemainingAfter capacity weight work
            (finiteGPSNextStepDuration capacity weight work firstDelay) j := by
            have hlinear := finiteGPSRemainingAfter_eq_linear_nextStep
              (nextBatchDelay := firstDelay) (i := j)
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
            rw [hterminal] at hlinear
            simpa [hterminal] using hlinear.symm
      _ = finiteGPSRemainingAfter capacity weight work firstDelay j := by
            rw [hterminal]
      _ = 0 := hremaining_zero
  have hempty_le : finiteGPSClassEmptyDelay capacity weight work j ≤ firstDelay := by
    unfold finiteGPSClassEmptyDelay
    apply (div_le_iff₀ hrate_pos).mpr
    nlinarith
  have hearliest_le : finiteGPSEarliestEmptyDelay capacity weight work ≤ firstDelay := by
    simpa [finiteGPSEarliestEmptyDelay, hactive_nonempty] using
      (Finset.inf'_le (finiteGPSClassEmptyDelay capacity weight work) hj).trans hempty_le
  have hfirst_le_earliest : firstDelay ≤ finiteGPSEarliestEmptyDelay capacity weight work := by
    by_contra hnot
    have hearliest_lt : finiteGPSEarliestEmptyDelay capacity weight work < firstDelay :=
      lt_of_not_ge hnot
    have hduration : finiteGPSNextStepDuration capacity weight work firstDelay =
        finiteGPSEarliestEmptyDelay capacity weight work := by
      simp [finiteGPSNextStepDuration, hactive_nonempty,
        min_eq_right hearliest_lt.le]
    have hcontra : firstDelay = finiteGPSEarliestEmptyDelay capacity weight work :=
      hterminal.symm.trans hduration
    exact (ne_of_gt hearliest_lt) hcontra
  have hearliest_eq : finiteGPSEarliestEmptyDelay capacity weight work = firstDelay :=
    le_antisymm hearliest_le hfirst_le_earliest
  simp [finiteGPSNextStepDuration, hactive_nonempty, hearliest_eq,
    min_eq_right (le_add_of_nonneg_right hsecond_nonneg)]

/-- From a zero workload, every positive-fuel concrete segment run consists
of exactly one terminal segment carrying the supplied endpoint batch. -/
theorem finiteGPSRunGapSegments_zeroWork_succ
    (fuel : ℕ) (capacity : ℝ) (weight batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    finiteGPSRunGapSegments (fuel + 1) capacity weight (fun _ => 0) batchWork
      currentTime nextBatchDelay =
      [finiteGPSBuildExecutionSegment capacity weight (fun _ => 0) batchWork
        currentTime nextBatchDelay] := by
  simp [finiteGPSRunGapSegments, finiteGPSNextStepDuration,
    finiteGPSActiveClasses]

/-- One strictly internal concrete GPS event exposes exactly one head segment
and the recursive tail.  Keeping this as a one-step equation prevents later
factorization proofs from unfolding the tail's unrelated endpoint case. -/
theorem finiteGPSRunGapSegments_succ_eq_cons_of_internal
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime nextBatchDelay : ℝ)
    (hinternal : finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠
      nextBatchDelay) :
    finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
      currentTime nextBatchDelay =
      finiteGPSBuildExecutionSegment capacity weight work batchWork
        currentTime nextBatchDelay ::
        finiteGPSRunGapSegments fuel capacity weight
          (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          batchWork
          (currentTime + finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (nextBatchDelay - finiteGPSNextStepDuration capacity weight work nextBatchDelay) := by
  rw [finiteGPSRunGapSegments]
  rw [if_neg hinternal]

/-- Every segment in the active prefix has an identically zero endpoint
batch.  A source adapter may therefore attach literal empty endpoint jobs to
these segments, but this generic result does not invent those job labels. -/
theorem finiteGPSRunGapActiveSegments_forall_endpointBatch_eq_zero
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∀ segment ∈ finiteGPSRunGapActiveSegments fuel capacity weight work
      currentTime nextBatchDelay, ∀ i, segment.endpointBatch i = 0 := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      simp [finiteGPSRunGapActiveSegments]
  | succ fuel ih =>
      by_cases hactive : (finiteGPSActiveClasses work).Nonempty
      · let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
        let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
        let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
          nextBatchDelay
        by_cases hterminal : duration = nextBatchDelay
        · intro candidate hcandidate i
          have hsegment : candidate = segment := by
            simpa [finiteGPSRunGapActiveSegments, hactive, duration, segment,
              nextWork, hterminal] using hcandidate
          subst candidate
          exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
            capacity weight work currentTime nextBatchDelay i
        · intro candidate hcandidate i
          rcases List.mem_cons.mp (by
            simpa [finiteGPSRunGapActiveSegments, hactive, duration, segment,
              nextWork, hterminal] using hcandidate) with hhead | htail
          · subst candidate
            exact finiteGPSBuildExecutionSegment_endpointBatch_eq_zero_of_zeroBatch
              capacity weight work currentTime nextBatchDelay i
          · exact ih (work := nextWork) (currentTime := currentTime + duration)
              (nextBatchDelay := nextBatchDelay - duration) candidate htail i
      · simp [finiteGPSRunGapActiveSegments, hactive]

/-- The ordinary zero-batch segment runner is the active prefix followed by
at most the bookkeeping tail it emits after the workload is empty.  This is
an exact list factorization and does not assume a source event at that tail. -/
theorem finiteGPSRunGapSegments_zeroBatch_exists_active_append
    (fuel : ℕ) (capacity : ℝ) (weight work : Class → ℝ)
    (currentTime nextBatchDelay : ℝ) :
    ∃ idle,
      finiteGPSRunGapSegments fuel capacity weight work (fun _ => 0)
        currentTime nextBatchDelay =
        finiteGPSRunGapActiveSegments fuel capacity weight work
          currentTime nextBatchDelay ++ idle := by
  induction fuel generalizing work currentTime nextBatchDelay with
  | zero =>
      exact ⟨[], by simp [finiteGPSRunGapSegments, finiteGPSRunGapActiveSegments]⟩
  | succ fuel ih =>
      by_cases hactive : (finiteGPSActiveClasses work).Nonempty
      · let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
        let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
        let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
          nextBatchDelay
        by_cases hterminal : duration = nextBatchDelay
        · exact ⟨[], by
            simp [finiteGPSRunGapSegments, finiteGPSRunGapActiveSegments, hactive,
              duration, hterminal]⟩
        · obtain ⟨idle, htail⟩ := ih (work := nextWork)
            (currentTime := currentTime + duration)
            (nextBatchDelay := nextBatchDelay - duration)
          refine ⟨idle, ?_⟩
          simp [finiteGPSRunGapSegments, finiteGPSRunGapActiveSegments, hactive,
            duration, nextWork, hterminal, htail, List.cons_append]
      · let segment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime nextBatchDelay
        refine ⟨[segment], ?_⟩
        simp [finiteGPSRunGapSegments, finiteGPSRunGapActiveSegments, hactive,
          segment, finiteGPSNextStepDuration]

/-- Under aggregate drain at `firstDelay` and a strictly later real endpoint,
the direct gap consists of a prefix observationally matching the active
zero-batch prefix followed by one real terminal segment.  The terminal batch
is kept explicit; it is never folded into the computational fence. -/
theorem finiteGPSRunGapSegments_exists_activeFactor_of_aggregate_drain
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (currentTime firstDelay secondDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hfirstDelay_nonneg : 0 ≤ firstDelay)
    (hsecondDelay_pos : 0 < secondDelay)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * firstDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel) :
    ∃ directActive terminal,
      finiteGPSRunGapSegments fuel capacity weight work batchWork
          currentTime (firstDelay + secondDelay) = directActive ++ [terminal] ∧
        List.Forall₂ FiniteGPSExecutionSegment.FCFSObservableEq
          (finiteGPSRunGapActiveSegments fuel capacity weight work
            currentTime firstDelay) directActive ∧
        (∀ segment ∈ directActive, ∀ i, segment.endpointBatch i = 0) ∧
        terminal.endpointIsExternalBatch = true ∧
        terminal.endpointBatch = batchWork ∧
        (∀ i, terminal.startWorkload i = 0) ∧
        finiteGPSExecutionSegmentEndTime terminal =
          currentTime + (firstDelay + secondDelay) := by
  induction fuel generalizing work currentTime firstDelay with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      by_cases hactive : (finiteGPSActiveClasses work).Nonempty
      · let shortDuration := finiteGPSNextStepDuration capacity weight work firstDelay
        let activeSegment := finiteGPSBuildExecutionSegment capacity weight work (fun _ => 0)
          currentTime firstDelay
        let nextWork := finiteGPSNextEventState capacity weight work (fun _ => 0)
          firstDelay
        by_cases hterminal : shortDuration = firstDelay
        · have hnext_zero : ∀ i, nextWork i = 0 := by
            simpa [shortDuration, nextWork] using
              (finiteGPSNextEventState_zero_eq_zero_of_aggregate_drain_of_terminal
                capacity weight work firstDelay hcapacity hweight_pos
                htotal_weight_le_one hwork_nonneg haggregate_drain hactive
                (by simpa [shortDuration] using hterminal))
          have hlongDuration :
              finiteGPSNextStepDuration capacity weight work
                (firstDelay + secondDelay) = firstDelay := by
            exact finiteGPSNextStepDuration_eq_of_aggregate_drain_terminal_extension
              capacity weight work firstDelay secondDelay hcapacity hweight_pos
              htotal_weight_le_one hwork_nonneg haggregate_drain hactive
              (by simpa [shortDuration] using hterminal) hsecondDelay_pos.le
          have hlong_internal :
              finiteGPSNextStepDuration capacity weight work
                (firstDelay + secondDelay) ≠ firstDelay + secondDelay := by
            rw [hlongDuration]
            linarith
          have hlong_batch_zero : ∀ i,
              finiteGPSBatchApplied capacity weight work batchWork
                (firstDelay + secondDelay) i = 0 := by
            intro i
            simp [finiteGPSBatchApplied, hlong_internal]
          have hshort_batch_zero : ∀ i,
              finiteGPSBatchApplied capacity weight work (fun _ => 0) firstDelay i = 0 := by
            intro i
            simp [finiteGPSBatchApplied]
          have hdirect_next :
              finiteGPSNextEventState capacity weight work batchWork
                (firstDelay + secondDelay) = nextWork := by
            funext i
            change finiteGPSRemainingAfter capacity weight work
                (finiteGPSNextStepDuration capacity weight work
                  (firstDelay + secondDelay)) i +
                finiteGPSBatchApplied capacity weight work batchWork
                  (firstDelay + secondDelay) i =
              finiteGPSRemainingAfter capacity weight work
                (finiteGPSNextStepDuration capacity weight work firstDelay) i +
                finiteGPSBatchApplied capacity weight work (fun _ => 0)
                  firstDelay i
            rw [hlong_batch_zero i, hshort_batch_zero i, add_zero, add_zero,
              hlongDuration]
            rw [show finiteGPSNextStepDuration capacity weight work firstDelay =
                firstDelay by simpa [shortDuration] using hterminal]
          have hactive_card_pos : 0 < (finiteGPSActiveClasses work).card :=
            Finset.card_pos.mpr hactive
          have hnextWork_zero : nextWork = fun _ => 0 := by
            funext i
            exact hnext_zero i
          cases fuel with
          | zero =>
              omega
          | succ tailFuel =>
              let directSegment := finiteGPSBuildExecutionSegment capacity weight work batchWork
                currentTime (firstDelay + secondDelay)
              let terminalSegment := finiteGPSBuildExecutionSegment capacity weight
                (fun _ => 0) batchWork (currentTime + firstDelay) secondDelay
              have hdirect_steps :
                  finiteGPSRunGapSegments (tailFuel + 2) capacity weight work batchWork
                    currentTime (firstDelay + secondDelay) =
                    directSegment :: [terminalSegment] := by
                have hdelay : firstDelay + secondDelay - firstDelay = secondDelay := by ring
                calc
                  finiteGPSRunGapSegments (tailFuel + 2) capacity weight work batchWork
                      currentTime (firstDelay + secondDelay) =
                      directSegment ::
                        finiteGPSRunGapSegments (tailFuel + 1) capacity weight
                          (finiteGPSNextEventState capacity weight work batchWork
                            (firstDelay + secondDelay))
                          batchWork
                          (currentTime + finiteGPSNextStepDuration capacity weight work
                            (firstDelay + secondDelay))
                          ((firstDelay + secondDelay) -
                            finiteGPSNextStepDuration capacity weight work
                              (firstDelay + secondDelay)) := by
                        simpa [directSegment] using
                          (finiteGPSRunGapSegments_succ_eq_cons_of_internal
                            (tailFuel + 1) capacity weight work batchWork currentTime
                            (firstDelay + secondDelay) hlong_internal)
                  _ = directSegment ::
                        finiteGPSRunGapSegments (tailFuel + 1) capacity weight
                          (fun _ => 0) batchWork (currentTime + firstDelay) secondDelay := by
                        rw [hdirect_next, hlongDuration, hnextWork_zero, hdelay]
                  _ = directSegment :: [terminalSegment] := by
                        rw [finiteGPSRunGapSegments_zeroWork_succ tailFuel capacity weight
                          batchWork (currentTime + firstDelay) secondDelay]
              have hactive_steps :
                  finiteGPSRunGapActiveSegments (tailFuel + 2) capacity weight work
                    currentTime firstDelay = [activeSegment] := by
                rw [show tailFuel + 2 = (tailFuel + 1) + 1 by omega]
                simp [finiteGPSRunGapActiveSegments, hactive, shortDuration,
                  activeSegment, hterminal]
              have hhead_observable :
                  FiniteGPSExecutionSegment.FCFSObservableEq activeSegment directSegment := by
                apply finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
                calc
                  finiteGPSNextStepDuration capacity weight work firstDelay = firstDelay := by
                    simpa [shortDuration] using hterminal
                  _ = finiteGPSNextStepDuration capacity weight work
                    (firstDelay + secondDelay) := hlongDuration.symm
              have hdirect_head_batch_zero : ∀ i, directSegment.endpointBatch i = 0 := by
                intro i
                simp [directSegment, finiteGPSBuildExecutionSegment,
                  finiteGPSBatchApplied, hlong_internal]
              refine ⟨[directSegment], terminalSegment, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [directSegment, terminalSegment, List.cons_append] using hdirect_steps
              · rw [hactive_steps]
                exact List.Forall₂.cons hhead_observable List.Forall₂.nil
              · intro segment hsegment i
                rcases List.mem_singleton.mp hsegment with rfl
                exact hdirect_head_batch_zero i
              · simp [terminalSegment, finiteGPSBuildExecutionSegment,
                  finiteGPSNextStepDuration, finiteGPSActiveClasses]
              · funext i
                simp [terminalSegment, finiteGPSBuildExecutionSegment,
                  finiteGPSNextStepDuration, finiteGPSActiveClasses,
                  finiteGPSBatchApplied]
              · intro i
                simp [terminalSegment, finiteGPSBuildExecutionSegment]
              · simp [terminalSegment, finiteGPSExecutionSegmentEndTime,
                  finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration,
                  finiteGPSActiveClasses]
                ring
        · have hnext_nonneg : ∀ i, 0 ≤ nextWork i := by
            intro i
            simpa [nextWork] using
              (finiteGPSNextEventState_nonneg_of_internal (batchWork := fun _ => 0)
                (by simpa [shortDuration] using hterminal) i)
          have hnext_active_ssubset : finiteGPSActiveClasses nextWork ⊂
              finiteGPSActiveClasses work := by
            exact finiteGPSActiveClasses_ssubset_nextEvent_of_internal
              (batchWork := fun _ => 0) hcapacity hweight_pos htotal_weight_le_one
              hwork_nonneg (by simpa [shortDuration, nextWork] using hterminal)
          have hnext_fuel : (finiteGPSActiveClasses nextWork).card < fuel := by
            exact lt_of_lt_of_le (Finset.card_lt_card hnext_active_ssubset)
              (Nat.lt_succ_iff.mp hfuel)
          have hremaining_nonneg : 0 ≤ firstDelay - shortDuration := by
            exact sub_nonneg.mpr
              (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work firstDelay)
          have hnext_aggregate : finiteGPSAggregateWork nextWork =
              finiteGPSAggregateWork work - capacity * shortDuration := by
            exact finiteGPSNextEventState_aggregateWork_eq_sub_capacity_mul_duration_of_zeroBatch
              hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hactive
          have hnext_aggregate_drain : finiteGPSAggregateWork nextWork ≤
              capacity * (firstDelay - shortDuration) := by
            rw [hnext_aggregate]
            ring_nf
            linarith
          have hdelay_le_total : firstDelay ≤ firstDelay + secondDelay :=
            le_add_of_nonneg_right hsecondDelay_pos.le
          have hlongDuration :
              finiteGPSNextStepDuration capacity weight work
                (firstDelay + secondDelay) = shortDuration := by
            exact finiteGPSNextStepDuration_eq_of_internal_of_le
              capacity weight work firstDelay (firstDelay + secondDelay)
              (by simpa [shortDuration] using hterminal) hdelay_le_total
          have hlong_internal :
              finiteGPSNextStepDuration capacity weight work
                (firstDelay + secondDelay) ≠ firstDelay + secondDelay := by
            intro hlong
            have hshort_lt : shortDuration < firstDelay := by
              exact lt_of_le_of_ne
                (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work firstDelay)
                (by simpa [shortDuration] using hterminal)
            have htotal_eq_short : firstDelay + secondDelay = shortDuration :=
              hlong.symm.trans hlongDuration
            linarith
          have hdirect_next :
              finiteGPSNextEventState capacity weight work batchWork
                (firstDelay + secondDelay) = nextWork := by
            exact finiteGPSNextEventState_eq_of_internal_of_le
              capacity weight work (fun _ => 0) batchWork firstDelay
              (firstDelay + secondDelay)
              (by simpa [shortDuration] using hterminal) hdelay_le_total
          obtain ⟨tailActive, terminal, htail_steps, htail_observable,
            htail_batches, hterminal_external, hterminal_batch, hterminal_start,
            hterminal_time⟩ :=
            ih (work := nextWork) (currentTime := currentTime + shortDuration)
              (firstDelay := firstDelay - shortDuration)
              hnext_nonneg hremaining_nonneg hnext_aggregate_drain hnext_fuel
          let directSegment := finiteGPSBuildExecutionSegment capacity weight work batchWork
            currentTime (firstDelay + secondDelay)
          have hactive_steps :
              finiteGPSRunGapActiveSegments (fuel + 1) capacity weight work
                currentTime firstDelay = activeSegment ::
                  finiteGPSRunGapActiveSegments fuel capacity weight nextWork
                    (currentTime + shortDuration) (firstDelay - shortDuration) := by
            simp [finiteGPSRunGapActiveSegments, hactive, shortDuration,
              activeSegment, nextWork, hterminal]
          have hdirect_steps :
              finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
                currentTime (firstDelay + secondDelay) = directSegment ::
                  finiteGPSRunGapSegments fuel capacity weight nextWork batchWork
                    (currentTime + shortDuration)
                    ((firstDelay - shortDuration) + secondDelay) := by
            calc
              finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
                  currentTime (firstDelay + secondDelay) = directSegment ::
                    finiteGPSRunGapSegments fuel capacity weight
                      (finiteGPSNextEventState capacity weight work batchWork
                        (firstDelay + secondDelay))
                      batchWork
                      (currentTime + finiteGPSNextStepDuration capacity weight work
                        (firstDelay + secondDelay))
                      ((firstDelay + secondDelay) -
                        finiteGPSNextStepDuration capacity weight work
                          (firstDelay + secondDelay)) := by
                    simpa [directSegment] using
                      (finiteGPSRunGapSegments_succ_eq_cons_of_internal fuel
                        capacity weight work batchWork currentTime
                        (firstDelay + secondDelay) hlong_internal)
              _ = directSegment ::
                    finiteGPSRunGapSegments fuel capacity weight nextWork batchWork
                      (currentTime + shortDuration)
                      ((firstDelay - shortDuration) + secondDelay) := by
                    rw [hdirect_next, hlongDuration]
                    congr
                    ring
          have hhead_observable :
              FiniteGPSExecutionSegment.FCFSObservableEq activeSegment directSegment := by
            apply finiteGPSBuildExecutionSegment_fcfsObservableEq_of_duration_eq
            exact hlongDuration.symm
          have hdirect_head_batch_zero : ∀ i, directSegment.endpointBatch i = 0 := by
            intro i
            simp [directSegment, finiteGPSBuildExecutionSegment,
              finiteGPSBatchApplied, hlong_internal]
          refine ⟨directSegment :: tailActive, terminal, ?_, ?_, ?_,
            hterminal_external, hterminal_batch, hterminal_start, ?_⟩
          · rw [hdirect_steps, htail_steps]
            simp [List.cons_append]
          · rw [hactive_steps]
            exact List.Forall₂.cons hhead_observable htail_observable
          · intro segment hsegment i
            rcases List.mem_cons.mp hsegment with hhead | htail
            · subst segment
              exact hdirect_head_batch_zero i
            · exact htail_batches segment htail i
          · calc
              finiteGPSExecutionSegmentEndTime terminal =
                  (currentTime + shortDuration) +
                    ((firstDelay - shortDuration) + secondDelay) := hterminal_time
              _ = currentTime + (firstDelay + secondDelay) := by ring
      · let directSegment := finiteGPSBuildExecutionSegment capacity weight work batchWork
            currentTime (firstDelay + secondDelay)
        have hactive_steps :
            finiteGPSRunGapActiveSegments (fuel + 1) capacity weight work
              currentTime firstDelay = [] := by
          simp [finiteGPSRunGapActiveSegments, hactive]
        have hdirect_steps :
            finiteGPSRunGapSegments (fuel + 1) capacity weight work batchWork
              currentTime (firstDelay + secondDelay) = [directSegment] := by
          simp [finiteGPSRunGapSegments, hactive, directSegment,
            finiteGPSNextStepDuration]
        refine ⟨[], directSegment, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [directSegment] using hdirect_steps
        · rw [hactive_steps]
          exact List.Forall₂.nil
        · simp
        · simp [directSegment, finiteGPSBuildExecutionSegment,
            finiteGPSNextStepDuration, hactive]
        · funext i
          simp [directSegment, finiteGPSBuildExecutionSegment,
            finiteGPSNextStepDuration, hactive, finiteGPSBatchApplied]
        · intro i
          have hnot_pos : ¬ 0 < work i := by
            intro hi
            apply hactive
            exact ⟨i, mem_finiteGPSActiveClasses_iff.mpr hi⟩
          have hwork_zero : work i = 0 :=
            le_antisymm (le_of_not_gt hnot_pos) (hwork_nonneg i)
          simp [directSegment, finiteGPSBuildExecutionSegment,
            finiteGPSNextStepDuration, hactive, hwork_zero]
        · simp [directSegment, finiteGPSExecutionSegmentEndTime,
          finiteGPSBuildExecutionSegment, finiteGPSNextStepDuration, hactive]

end

end AppliedModelingLib.Probability.Queueing
