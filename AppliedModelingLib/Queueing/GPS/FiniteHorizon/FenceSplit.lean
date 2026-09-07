import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Drain
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

/-!
# Terminal-batch separation for a finite GPS gap

The finite GPS gap runner evolves the workload through internal depletion
events and applies its external batch only at the terminal endpoint.  This
module records that deterministic separation explicitly.  It is a finite
execution fact only; it contains no stochastic or regeneration statement.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Apply a pending external batch to the endpoint of a zero-batch gap run.
If the bounded run did not reach its endpoint, no batch is applied. -/
def finiteGPSRunGapApplyTerminalBatch
    (zeroBatchResult : FiniteGPSGapRunResult Class)
    (batchWork : Class → ℝ) : FiniteGPSGapRunResult Class :=
  { workload := if zeroBatchResult.batchApplied = true then
      fun i => zeroBatchResult.workload i + batchWork i
    else zeroBatchResult.workload
    remainingDelay := zeroBatchResult.remainingDelay
    service := zeroBatchResult.service
    batchApplied := zeroBatchResult.batchApplied }

omit [DecidableEq Class] in
/-- A pending external batch affects a finite GPS gap only when its endpoint
is reached.  The service and residual delay are exactly those of the zero-batch
run, and the terminal workload is then incremented by the actual batch. -/
theorem finiteGPSRunGap_eq_zeroBatch_then_terminalBatch
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) :
    finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay =
      finiteGPSRunGapApplyTerminalBatch
        (finiteGPSRunGap fuel capacity weight work (fun _ => 0) nextBatchDelay)
        batchWork := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      rfl
  | succ fuel ih =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      by_cases hterminal : duration = nextBatchDelay
      · have hterminal' :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay = nextBatchDelay := by
            simpa [duration] using hterminal
        have hstate :
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay =
              fun i => finiteGPSNextEventState capacity weight work (fun _ => 0)
                nextBatchDelay i + batchWork i := by
            funext i
            simp [finiteGPSNextEventState, finiteGPSBatchApplied, hterminal']
        simp [finiteGPSRunGap, duration, hterminal,
          finiteGPSRunGapApplyTerminalBatch, hstate]
      · have hterminal' :
            finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay := by
            simpa [duration] using hterminal
        have hstate :
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay =
              finiteGPSNextEventState capacity weight work (fun _ => 0)
                nextBatchDelay := by
            funext i
            simp [finiteGPSNextEventState, finiteGPSBatchApplied, hterminal']
        simp only [finiteGPSRunGap]
        rw [if_neg hterminal, if_neg hterminal']
        rw [hstate]
        have htail := ih
          (work := finiteGPSNextEventState capacity weight work (fun _ => 0)
            nextBatchDelay)
          (nextBatchDelay := nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
        rw [htail]
        by_cases htailApplied :
            (finiteGPSRunGap fuel capacity weight
              (finiteGPSNextEventState capacity weight work (fun _ => 0)
                nextBatchDelay)
              (fun _ => 0)
              (nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)).batchApplied = true
        · simp [finiteGPSRunGapApplyTerminalBatch, htailApplied]
        · simp [finiteGPSRunGapApplyTerminalBatch, htailApplied]

omit [DecidableEq Class] in
/-- The finite GPS service accumulated toward an endpoint does not depend on
the endpoint batch: that batch is applied after the gap service. -/
theorem finiteGPSRunGap_service_eq_zeroBatch
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) :
    (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).service =
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0) nextBatchDelay).service := by
  rw [finiteGPSRunGap_eq_zeroBatch_then_terminalBatch]
  rfl

omit [DecidableEq Class] in
/-- The residual delay and endpoint-reached flag of a finite GPS gap are
independent of its endpoint batch. -/
theorem finiteGPSRunGap_remainingDelay_batchApplied_eq_zeroBatch
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) :
    (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).remainingDelay =
        (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
          nextBatchDelay).remainingDelay ∧
      (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).batchApplied =
        (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
          nextBatchDelay).batchApplied := by
  rw [finiteGPSRunGap_eq_zeroBatch_then_terminalBatch]
  exact ⟨rfl, rfl⟩

omit [DecidableEq Class] in
/-- Once the endpoint is reached, the finite GPS workload is the corresponding
zero-batch workload plus the actual endpoint batch. -/
theorem finiteGPSRunGap_workload_eq_zeroBatch_add_of_batchApplied
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ)
    (hzeroBatchApplied :
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
        nextBatchDelay).batchApplied = true)
    (i : Class) :
    (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload i =
      (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
        nextBatchDelay).workload i + batchWork i := by
  rw [finiteGPSRunGap_eq_zeroBatch_then_terminalBatch]
  simp [finiteGPSRunGapApplyTerminalBatch, hzeroBatchApplied]

omit [DecidableEq Class] in
/-- From an identically zero workload, any positive-fuel gap reaches its
external endpoint immediately: it delivers no service and simply applies the
endpoint batch. -/
theorem finiteGPSRunGap_zeroWork_succ
    (fuel : ℕ) (capacity : ℝ) (weight batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) :
    finiteGPSRunGap (fuel + 1) capacity weight (fun _ => 0) batchWork
        nextBatchDelay =
      { workload := batchWork
        remainingDelay := 0
        service := fun _ => 0
        batchApplied := true } := by
  have hduration :
      finiteGPSNextStepDuration capacity weight (fun _ => 0) nextBatchDelay =
        nextBatchDelay := by
    simp [finiteGPSNextStepDuration, finiteGPSActiveClasses]
  have hstate :
      finiteGPSNextEventState capacity weight (fun _ => 0) batchWork nextBatchDelay =
        batchWork := by
    funext i
    simp [finiteGPSNextEventState, finiteGPSBatchApplied,
      finiteGPSRemainingAfter, finiteGPSClassRate, hduration]
  have hservice :
      finiteGPSServiceIncrement capacity weight (fun _ => 0) nextBatchDelay = fun _ => 0 := by
    funext i
    simp [finiteGPSServiceIncrement, finiteGPSRemainingAfter, finiteGPSClassRate]
  simp [finiteGPSRunGap, hduration, hstate, hservice]

/-- Split one pending external batch gap by inserting a computational
zero-work fence after `firstDelay`.  The fence is an execution artifact, not
an arrival batch. -/
def finiteGPSRunGapSplitAtZeroFence
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (firstDelay secondDelay : ℝ) : FiniteGPSGapRunResult Class :=
  let fence := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
    capacity weight work (fun _ => 0) firstDelay
  let suffix := finiteGPSRunGap ((finiteGPSActiveClasses fence.workload).card + 1)
    capacity weight fence.workload batchWork secondDelay
  { workload := suffix.workload
    remainingDelay := suffix.remainingDelay
    service := fun i => fence.service i + suffix.service i
    batchApplied := suffix.batchApplied }

/-- If the inserted zero-work fence has enough capacity to drain the initial
workload, splitting a later pending external batch gap at that fence preserves
every field of the actual finite GPS result.  Both legs use the runner's
dynamic active-class fuel.  This is deterministic and does not assert that a
stochastic source has an arrival-free interval. -/
theorem finiteGPSRunGap_fields_eq_splitAtZeroFence_of_aggregate_drain
    (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (firstDelay secondDelay : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hfirstDelay_nonneg : 0 ≤ firstDelay) (hsecondDelay_nonneg : 0 ≤ secondDelay)
    (haggregate_drain : finiteGPSAggregateWork work ≤ capacity * firstDelay) :
    (∀ i,
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work batchWork (firstDelay + secondDelay)).workload i =
        (finiteGPSRunGapSplitAtZeroFence capacity weight work batchWork
          firstDelay secondDelay).workload i) ∧
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work batchWork (firstDelay + secondDelay)).remainingDelay =
        (finiteGPSRunGapSplitAtZeroFence capacity weight work batchWork
          firstDelay secondDelay).remainingDelay ∧
      (∀ i,
        (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
          capacity weight work batchWork (firstDelay + secondDelay)).service i =
          (finiteGPSRunGapSplitAtZeroFence capacity weight work batchWork
            firstDelay secondDelay).service i) ∧
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work batchWork (firstDelay + secondDelay)).batchApplied =
        (finiteGPSRunGapSplitAtZeroFence capacity weight work batchWork
          firstDelay secondDelay).batchApplied := by
  let fuel := (finiteGPSActiveClasses work).card + 1
  let fence := finiteGPSRunGap fuel capacity weight work (fun _ => 0) firstDelay
  let totalZero := finiteGPSRunGap fuel capacity weight work (fun _ => 0)
    (firstDelay + secondDelay)
  let suffix := finiteGPSRunGap ((finiteGPSActiveClasses fence.workload).card + 1)
    capacity weight fence.workload batchWork secondDelay
  have hfuel : (finiteGPSActiveClasses work).card < fuel := by
    simp [fuel]
  have htotalDelay_nonneg : 0 ≤ firstDelay + secondDelay :=
    add_nonneg hfirstDelay_nonneg hsecondDelay_nonneg
  have hcapacity_secondDelay : 0 ≤ capacity * secondDelay :=
    mul_nonneg hcapacity.le hsecondDelay_nonneg
  have haggregate_drain_total :
      finiteGPSAggregateWork work ≤ capacity * (firstDelay + secondDelay) := by
    calc
      finiteGPSAggregateWork work ≤ capacity * firstDelay := haggregate_drain
      _ ≤ capacity * firstDelay + capacity * secondDelay :=
        le_add_of_nonneg_right hcapacity_secondDelay
      _ = capacity * (firstDelay + secondDelay) := by ring
  have hfence_workload_zero : ∀ i, fence.workload i = 0 := by
    simpa [fence, fuel] using
      (finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
        fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hfirstDelay_nonneg haggregate_drain hfuel)
  have htotalZero_workload_zero : ∀ i, totalZero.workload i = 0 := by
    simpa [totalZero, fuel] using
      (finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
        fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        htotalDelay_nonneg haggregate_drain_total hfuel)
  have hfence_terminates : fence.batchApplied = true ∧ fence.remainingDelay = 0 := by
    simpa [fence, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg hfirstDelay_nonneg hfuel)
  have htotalZero_terminates :
      totalZero.batchApplied = true ∧ totalZero.remainingDelay = 0 := by
    simpa [totalZero, fuel] using
      (finiteGPSRunGap_terminates_of_activeCard_lt fuel hcapacity hweight_pos
        htotal_weight_le_one hwork_nonneg htotalDelay_nonneg hfuel)
  have hfence_service : ∀ i, fence.service i = work i := by
    intro i
    have hbalance := finiteGPSRunGap_balance fuel capacity weight work
      (fun _ => 0) firstDelay i
    rw [show (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
      firstDelay).workload i = 0 by simpa [fence] using hfence_workload_zero i,
      hfence_terminates.1] at hbalance
    change fence.service i = work i
    have : 0 = work i - fence.service i := by
      simpa [fence] using hbalance
    linarith
  have htotalZero_service : ∀ i, totalZero.service i = work i := by
    intro i
    have hbalance := finiteGPSRunGap_balance fuel capacity weight work
      (fun _ => 0) (firstDelay + secondDelay) i
    rw [show (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
      (firstDelay + secondDelay)).workload i = 0 by
        simpa [totalZero] using htotalZero_workload_zero i,
      htotalZero_terminates.1] at hbalance
    change totalZero.service i = work i
    have : 0 = work i - totalZero.service i := by
      simpa [totalZero] using hbalance
    linarith
  have hfence_workload : fence.workload = fun _ => 0 := by
    funext i
    exact hfence_workload_zero i
  have hsuffix_eq : suffix =
      { workload := batchWork
        remainingDelay := 0
        service := fun _ => 0
        batchApplied := true } := by
    dsimp only [suffix]
    rw [hfence_workload]
    simpa [suffix, finiteGPSActiveClasses] using
      (finiteGPSRunGap_zeroWork_succ (Class := Class) 0 capacity weight batchWork
        secondDelay)
  have hdirect_workload : ∀ i,
      (finiteGPSRunGap fuel capacity weight work batchWork
        (firstDelay + secondDelay)).workload i = batchWork i := by
    intro i
    rw [finiteGPSRunGap_workload_eq_zeroBatch_add_of_batchApplied
      fuel capacity weight work batchWork (firstDelay + secondDelay)
      (by simpa [totalZero, fuel] using htotalZero_terminates.1) i]
    rw [show (finiteGPSRunGap fuel capacity weight work (fun _ => 0)
      (firstDelay + secondDelay)).workload i = 0 by
        simpa [totalZero] using htotalZero_workload_zero i]
    ring
  have hdirect_service : ∀ i,
      (finiteGPSRunGap fuel capacity weight work batchWork
        (firstDelay + secondDelay)).service i = work i := by
    intro i
    rw [finiteGPSRunGap_service_eq_zeroBatch]
    simpa [totalZero] using htotalZero_service i
  have hdirect_remaining_batchApplied :
      (finiteGPSRunGap fuel capacity weight work batchWork
        (firstDelay + secondDelay)).remainingDelay = 0 ∧
      (finiteGPSRunGap fuel capacity weight work batchWork
        (firstDelay + secondDelay)).batchApplied = true := by
    have hfields := finiteGPSRunGap_remainingDelay_batchApplied_eq_zeroBatch
      fuel capacity weight work batchWork (firstDelay + secondDelay)
    constructor
    · rw [hfields.1]
      simpa [totalZero] using htotalZero_terminates.2
    · rw [hfields.2]
      simpa [totalZero] using htotalZero_terminates.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    change (finiteGPSRunGap fuel capacity weight work batchWork
      (firstDelay + secondDelay)).workload i = suffix.workload i
    rw [hdirect_workload i, hsuffix_eq]
  · change (finiteGPSRunGap fuel capacity weight work batchWork
      (firstDelay + secondDelay)).remainingDelay = suffix.remainingDelay
    rw [hdirect_remaining_batchApplied.1, hsuffix_eq]
  · intro i
    change (finiteGPSRunGap fuel capacity weight work batchWork
      (firstDelay + secondDelay)).service i = fence.service i + suffix.service i
    rw [hdirect_service i, hfence_service i, hsuffix_eq]
    norm_num
  · change (finiteGPSRunGap fuel capacity weight work batchWork
      (firstDelay + secondDelay)).batchApplied = suffix.batchApplied
    rw [hdirect_remaining_batchApplied.2, hsuffix_eq]

/-- Continue a raw finite GPS trace after a computational zero-work fence.
The fence contributes service but is deliberately not represented as a source
batch in `times`. -/
def finiteGPSRunBatchTraceAfterZeroFence
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (resetTime : ℝ) (times : List ℝ) :
    FiniteGPSBatchTraceResult Class :=
  let fence := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
    capacity weight work (fun _ => 0) (resetTime - currentTime)
  let suffix := finiteGPSRunBatchTrace capacity weight batchWork resetTime fence.workload times
  { workload := suffix.workload
    currentTime := suffix.currentTime
    service := fun i => fence.service i + suffix.service i }

/-- A raw finite GPS trace whose next source batch is at or after `resetTime`
is unchanged by first executing a drain-certified computational zero-work
fence at `resetTime`.  When the source batch is exactly at the reset time, it
is still processed separately at zero delay after the fence; no two-batch
same-time encoding is smuggled into the time-indexed source batch function. -/
theorem finiteGPSRunBatchTrace_cons_eq_afterZeroFence_of_aggregate_drain
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime resetTime eventTime : ℝ) (tail : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hcurrentTime_reset : currentTime ≤ resetTime)
    (hresetTime_event : resetTime ≤ eventTime)
    (haggregate_drain : finiteGPSAggregateWork work ≤
      capacity * (resetTime - currentTime)) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work (eventTime :: tail) =
      finiteGPSRunBatchTraceAfterZeroFence capacity weight batchWork currentTime work
        resetTime (eventTime :: tail) := by
  let fuel := (finiteGPSActiveClasses work).card + 1
  let fence := finiteGPSRunGap fuel capacity weight work (fun _ => 0)
    (resetTime - currentTime)
  let sourceGap := finiteGPSRunGap ((finiteGPSActiveClasses fence.workload).card + 1)
    capacity weight fence.workload (batchWork eventTime) (eventTime - resetTime)
  have hsplit := finiteGPSRunGap_fields_eq_splitAtZeroFence_of_aggregate_drain
    capacity weight work (batchWork eventTime)
    (resetTime - currentTime) (eventTime - resetTime)
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    (sub_nonneg.mpr hcurrentTime_reset) (sub_nonneg.mpr hresetTime_event)
    haggregate_drain
  have hdelay : eventTime - currentTime =
      (resetTime - currentTime) + (eventTime - resetTime) := by ring
  have hfence_workload_zero : ∀ i, fence.workload i = 0 := by
    have hfuel : (finiteGPSActiveClasses work).card < fuel := by simp [fuel]
    simpa [fence, fuel] using
      (finiteGPSRunGap_zeroBatch_workload_eq_zero_of_aggregate_le_capacity_mul
        fuel hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        (sub_nonneg.mpr hcurrentTime_reset) haggregate_drain hfuel)
  have hfence_workload : fence.workload = fun _ => 0 := by
    funext i
    exact hfence_workload_zero i
  have hsourceGap_eq : sourceGap =
      { workload := batchWork eventTime
        remainingDelay := 0
        service := fun _ => 0
        batchApplied := true } := by
    dsimp only [sourceGap]
    rw [hfence_workload]
    simpa [finiteGPSActiveClasses] using
      (finiteGPSRunGap_zeroWork_succ (Class := Class) 0 capacity weight (batchWork eventTime)
        (eventTime - resetTime))
  have hsourceGap_batchApplied : sourceGap.batchApplied = true := by
    rw [hsourceGap_eq]
  have hsplit_workload :
      (finiteGPSRunGap fuel capacity weight work (batchWork eventTime)
        (eventTime - currentTime)).workload = sourceGap.workload := by
    funext i
    rw [hdelay]
    simpa [finiteGPSRunGapSplitAtZeroFence, fence, sourceGap, fuel] using hsplit.1 i
  have hsplit_service :
      (finiteGPSRunGap fuel capacity weight work (batchWork eventTime)
        (eventTime - currentTime)).service =
        fun i => fence.service i + sourceGap.service i := by
    funext i
    rw [hdelay]
    simpa [finiteGPSRunGapSplitAtZeroFence, fence, sourceGap, fuel] using hsplit.2.2.1 i
  have hsplit_batchApplied :
      (finiteGPSRunGap fuel capacity weight work (batchWork eventTime)
        (eventTime - currentTime)).batchApplied = true := by
    rw [hdelay]
    rw [hsplit.2.2.2]
    simpa [finiteGPSRunGapSplitAtZeroFence, fence, sourceGap, fuel] using
      hsourceGap_batchApplied
  have hsourceGap_def :
      finiteGPSRunGap ((finiteGPSActiveClasses fence.workload).card + 1)
        capacity weight fence.workload (batchWork eventTime)
        (eventTime - resetTime) = sourceGap := rfl
  unfold finiteGPSRunBatchTraceAfterZeroFence
  dsimp only
  rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
    currentTime work eventTime tail (by simpa [fuel] using hsplit_batchApplied)]
  rw [show finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
      capacity weight work (fun _ => 0) (resetTime - currentTime) = fence by rfl]
  rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
    resetTime fence.workload eventTime tail (by simpa [hsourceGap_def] using hsourceGap_batchApplied)]
  rw [hsplit_workload, hsplit_service]
  rw [FiniteGPSBatchTraceResult.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext i
  simp [hsourceGap_def, add_assoc]

end

end AppliedModelingLib.Probability.Queueing
