import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Runner
import Mathlib.Tactic

/-!
# Finite external-batch GPS traces

This module folds the finite GPS gap runner over a chronological finite list
of distinct external batch times. Each gap is processed through every required
internal class-emptying event before its external batch is applied. Thus an
arrival at the right endpoint of a gap is applied after the service accrued on
the preceding half-open interval, including exact arrival/completion ties.

The construction is deterministic. A concrete adapter supplies the
batch-time list and batch-work vectors from a concrete stochastic carrier.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- A finite batch-time trace is chronological from `start` when each listed
time is at least the previous one. -/
def FiniteGPSChronologicalFrom (start : ℝ) : List ℝ → Prop
  | [] => True
  | t :: times => start ≤ t ∧ FiniteGPSChronologicalFrom t times

/-- A pairwise nondecreasing list whose elements all lie after `start` is a
chronological batch trace. -/
theorem finiteGPSChronologicalFrom_of_pairwise_le
    (start : ℝ) (times : List ℝ)
    (hstart : ∀ t ∈ times, start ≤ t)
    (hpairwise : List.Pairwise (fun s t : ℝ => s ≤ t) times) :
    FiniteGPSChronologicalFrom start times := by
  induction times generalizing start with
  | nil => trivial
  | cons t times ih =>
      constructor
      · exact hstart t (by simp)
      · apply ih t
        · intro u hu
          exact (List.pairwise_cons.mp hpairwise).1 u hu
        · exact (List.pairwise_cons.mp hpairwise).2

/-- Valid external batch times are chronological and distinct. Distinctness is
essential because `batchWork` is indexed by time: all simultaneous arrivals
must first be aggregated into one batch rather than replayed once per list
occurrence. -/
structure FiniteGPSExternalBatchTrace (start : ℝ) where
  times : List ℝ
  chronological : FiniteGPSChronologicalFrom start times
  nodup : times.Nodup

/-- Computed result of a finite sequence of external GPS batches. -/
structure FiniteGPSBatchTraceResult (Class : Type*) where
  workload : Class → ℝ
  currentTime : ℝ
  service : Class → ℝ

/-- Run a finite list of external batches. The `(currentTime, t]` convention
is encoded by evolving to `t` first and applying `batchWork t` only at the
event endpoint. If the bounded gap computation cannot reach that endpoint,
the trace stops at its actual partial clock and never fabricates later batch
events. -/
def finiteGPSRunBatchTrace
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) : List ℝ →
      FiniteGPSBatchTraceResult Class
  | [] =>
      { workload := work
        currentTime := currentTime
        service := fun _ => 0 }
  | t :: times =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)
      if gap.batchApplied = true then
        let later := finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times
        { workload := later.workload
          currentTime := later.currentTime
          service := fun i => gap.service i + later.service i }
      else
        { workload := gap.workload
          currentTime := t - gap.remainingDelay
          service := gap.service }

omit [DecidableEq Class] in
/-- When the bounded gap reaches an external batch, the trace continues from
that exact post-batch state. -/
theorem finiteGPSRunBatchTrace_cons_of_batchApplied
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (t : ℝ) (times : List ℝ)
    (hbatchApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)).batchApplied = true) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work (t :: times) =
      { workload :=
          (finiteGPSRunBatchTrace capacity weight batchWork t
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork t) (t - currentTime)).workload times).workload
        currentTime :=
          (finiteGPSRunBatchTrace capacity weight batchWork t
            (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
              capacity weight work (batchWork t) (t - currentTime)).workload times).currentTime
        service := fun i =>
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).service i +
            (finiteGPSRunBatchTrace capacity weight batchWork t
              (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
                capacity weight work (batchWork t) (t - currentTime)).workload times).service i } := by
  simp [finiteGPSRunBatchTrace, hbatchApplied]

omit [DecidableEq Class] in
/-- When the bounded gap has not reached its pending batch, the trace stops
at the actual partial state and does not inspect later batch times. -/
theorem finiteGPSRunBatchTrace_cons_of_not_batchApplied
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (t : ℝ) (times : List ℝ)
    (hbatchNotApplied :
      (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)).batchApplied ≠ true) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work (t :: times) =
      { workload :=
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).workload
        currentTime := t -
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).remainingDelay
        service :=
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).service } := by
  simp [finiteGPSRunBatchTrace, hbatchNotApplied]

/-- Execute a valid external batch trace. The raw list runner remains useful
for recursion proofs; paper-facing callers should use this distinct-time
wrapper. -/
def finiteGPSRunExternalBatchTrace
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (start : ℝ) (work : Class → ℝ)
    (trace : FiniteGPSExternalBatchTrace start) : FiniteGPSBatchTraceResult Class :=
  finiteGPSRunBatchTrace capacity weight batchWork start work trace.times

/-- If the initial clock and every listed external-batch time are no later
than `horizon`, the finite batch runner's clock is also no later than
`horizon`.  This is independent of the workload dynamics and lets a caller
close the remaining service interval with a terminal zero batch. -/
theorem finiteGPSRunBatchTrace_currentTime_le
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime horizon : ℝ) (times : List ℝ)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hcurrentTime : currentTime ≤ horizon)
    (htimes : ∀ t ∈ times, t ≤ horizon) :
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).currentTime ≤
      horizon := by
  induction times generalizing currentTime work with
  | nil =>
      simpa [finiteGPSRunBatchTrace] using hcurrentTime
  | cons t times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have htime : t ≤ horizon := htimes t (by simp)
      have htimes_tail : ∀ u ∈ times, u ≤ horizon := by
        intro u hu
        exact htimes u (by simp [hu])
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have htail := ih (currentTime := t) (work := gap.workload)
          hchronological_tail htime htimes_tail
        simpa [finiteGPSRunBatchTrace, gap, hbatch] using htail
      · have hremaining_nonneg : 0 ≤ gap.remainingDelay := by
          exact finiteGPSRunGap_remainingDelay_nonneg
            ((finiteGPSActiveClasses work).card + 1) capacity weight work
            (batchWork t) (t - currentTime) (sub_nonneg.mpr hdelay)
        have hpartial : t - gap.remainingDelay ≤ horizon :=
          (sub_le_self t hremaining_nonneg).trans htime
        simpa [finiteGPSRunBatchTrace, gap, hbatch] using hpartial

/-- The valid-trace wrapper inherits the finite runner's clock upper bound. -/
theorem finiteGPSRunExternalBatchTrace_currentTime_le
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (start horizon : ℝ) (trace : FiniteGPSExternalBatchTrace start)
    (hstart : start ≤ horizon)
    (htimes : ∀ t ∈ trace.times, t ≤ horizon) :
    (finiteGPSRunExternalBatchTrace capacity weight batchWork start work trace).currentTime ≤
      horizon := by
  exact finiteGPSRunBatchTrace_currentTime_le capacity weight work batchWork start horizon
    trace.times trace.chronological hstart htimes

/-- A terminal horizon fence is a computational zero-work clock event used to
finish service through a requested endpoint.  It is deliberately not an
external arrival and carries no source-event metadata. -/
def finiteGPSHorizonFence
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) :
    FiniteGPSGapRunResult Class :=
  finiteGPSRunGap ((finiteGPSActiveClasses result.workload).card + 1)
    capacity weight result.workload (fun _ => 0) (horizon - result.currentTime)

/-- When the pre-fence clock is not after `horizon`, the bounded active-class
fuel reaches the terminal horizon fence. -/
theorem finiteGPSHorizonFence_terminates
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon) :
    (finiteGPSHorizonFence capacity weight result horizon).batchApplied = true ∧
      (finiteGPSHorizonFence capacity weight result horizon).remainingDelay = 0 := by
  simpa [finiteGPSHorizonFence] using
    (finiteGPSRunGap_terminates_of_activeCard_lt
      ((finiteGPSActiveClasses result.workload).card + 1)
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
      (sub_nonneg.mpr hcurrentTime_le_horizon) (Nat.lt_succ_self _))

/-- A terminal horizon fence preserves nonnegative workload from a
nonnegative pre-fence state. -/
theorem finiteGPSHorizonFence_workload_nonneg
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j) :
    ∀ i, 0 ≤ (finiteGPSHorizonFence capacity weight result horizon).workload i := by
  simpa [finiteGPSHorizonFence] using
    (finiteGPSRunGap_workload_nonneg
      ((finiteGPSActiveClasses result.workload).card + 1)
      capacity weight result.workload (fun _ => 0) (horizon - result.currentTime)
      hwork_nonneg (by intro j; norm_num))

/-- A reached terminal horizon fence only subtracts its own service: its
zero-work event cannot add workload. -/
theorem finiteGPSHorizonFence_balance
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon) (i : Class) :
    (finiteGPSHorizonFence capacity weight result horizon).workload i =
      result.workload i - (finiteGPSHorizonFence capacity weight result horizon).service i := by
  have hterminal := finiteGPSRunGap_terminates_of_activeCard_lt
    ((finiteGPSActiveClasses result.workload).card + 1)
    (batchWork := fun _ => 0)
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    (sub_nonneg.mpr hcurrentTime_le_horizon) (Nat.lt_succ_self _)
  have hbalance := finiteGPSRunGap_balance
    ((finiteGPSActiveClasses result.workload).card + 1)
    capacity weight result.workload (fun _ => 0) (horizon - result.currentTime) i
  rw [hterminal.1] at hbalance
  simpa [finiteGPSHorizonFence] using hbalance

/-- Close a finite trace toward a requested horizon with a terminal zero-work
fence.  Its clock records the actual reached endpoint as `horizon` minus the
unconsumed delay, so it equals `horizon` only once the fence is proved to have
terminated.  This result contains no assertion that the fence was a source
arrival. -/
def finiteGPSCloseAtHorizon
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ) :
    FiniteGPSBatchTraceResult Class :=
  let fence := finiteGPSHorizonFence capacity weight result horizon
  { workload := fence.workload
    currentTime := horizon - fence.remainingDelay
    service := fun i => result.service i + fence.service i }

/-- A terminal closure reaches the requested clock exactly when its fence has
been shown to consume all remaining delay. -/
theorem finiteGPSCloseAtHorizon_currentTime
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon) :
    (finiteGPSCloseAtHorizon capacity weight result horizon).currentTime = horizon := by
  have hterminal := finiteGPSHorizonFence_terminates capacity weight result horizon
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hcurrentTime_le_horizon
  simp [finiteGPSCloseAtHorizon, hterminal.2]

/-- Closing at a horizon preserves nonnegative workload. -/
theorem finiteGPSCloseAtHorizon_workload_nonneg
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j) :
    ∀ i, 0 ≤ (finiteGPSCloseAtHorizon capacity weight result horizon).workload i := by
  change ∀ i, 0 ≤ (finiteGPSHorizonFence capacity weight result horizon).workload i
  exact finiteGPSHorizonFence_workload_nonneg capacity weight result horizon hwork_nonneg

/-- A previously balanced finite trace remains balanced after terminal closure:
the fence adds no work and its service is added to the cumulative service. -/
theorem finiteGPSCloseAtHorizon_balance
    (capacity : ℝ) (weight : Class → ℝ)
    (result : FiniteGPSBatchTraceResult Class) (horizon : ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ result.workload j)
    (hcurrentTime_le_horizon : result.currentTime ≤ horizon)
    (initialWork admittedWork : ℝ) (i : Class)
    (hbalance : result.workload i = initialWork + admittedWork - result.service i) :
    (finiteGPSCloseAtHorizon capacity weight result horizon).workload i =
      initialWork + admittedWork -
        (finiteGPSCloseAtHorizon capacity weight result horizon).service i := by
  change (finiteGPSHorizonFence capacity weight result horizon).workload i =
    initialWork + admittedWork -
      (result.service i + (finiteGPSHorizonFence capacity weight result horizon).service i)
  rw [finiteGPSHorizonFence_balance capacity weight result horizon hcapacity hweight_pos
    htotal_weight_le_one hwork_nonneg hcurrentTime_le_horizon i, hbalance]
  ring

/-- A finite trace preserves nonnegative workload when the initial workload
and every computed external batch are nonnegative. -/
theorem finiteGPSRunBatchTrace_workload_nonneg
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hbatch_nonneg : ∀ t ∈ times, ∀ j, 0 ≤ batchWork t j) :
    ∀ i, 0 ≤
      (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).workload i := by
  induction times generalizing currentTime work with
  | nil =>
      simpa [finiteGPSRunBatchTrace] using hwork_nonneg
  | cons t times ih =>
      have hbatch_head : ∀ j, 0 ≤ batchWork t j := by
        intro j
        exact hbatch_nonneg t (by simp) j
      have hbatch_tail : ∀ u ∈ times, ∀ j, 0 ≤ batchWork u j := by
        intro u hu j
        exact hbatch_nonneg u (by simp [hu]) j
      have hgap_nonneg : ∀ j, 0 ≤
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).workload j :=
        finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork t) (t - currentTime) hwork_nonneg hbatch_head
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)
      by_cases hbatch : gap.batchApplied = true
      · have htail := ih (work := gap.workload) (currentTime := t)
          hgap_nonneg hbatch_tail
        simpa [finiteGPSRunBatchTrace, gap, hbatch] using htail
      · simpa [finiteGPSRunBatchTrace, gap, hbatch] using hgap_nonneg

/-- The finite trace telescopes all per-gap workload balances. It requires the
actual GPS positivity conditions explicitly and only evolves over
chronological, nonnegative-duration gaps. -/
theorem finiteGPSRunBatchTrace_balance
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (times : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ j, 0 ≤ batchWork t j)
    (i : Class) :
    (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).workload i =
      work i + (times.map fun t => batchWork t i).sum -
        (finiteGPSRunBatchTrace capacity weight batchWork currentTime work times).service i := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTrace]
  | cons t times ih =>
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork t j := by
        intro j
        exact hbatch_nonneg t (by simp) j
      have hbatch_tail : ∀ u ∈ times, ∀ j, 0 ≤ batchWork u j := by
        intro u hu j
        exact hbatch_nonneg u (by simp [hu]) j
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork t) (t - currentTime)
      have hgap_terminates : gap.batchApplied = true ∧ gap.remainingDelay = 0 := by
        exact finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses work).card + 1) hcapacity hweight_pos
          htotal_weight_le_one hwork_nonneg (sub_nonneg.mpr hdelay)
          (Nat.lt_succ_self _)
      have hgap_nonneg : ∀ j, 0 ≤ gap.workload j := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork t) (t - currentTime) hwork_nonneg hbatch_head
      have hgap_balance : gap.workload i =
          work i + batchWork t i - gap.service i := by
        have hbalance := finiteGPSRunGap_balance
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork t) (t - currentTime) i
        rw [hgap_terminates.1] at hbalance
        simpa [gap] using hbalance
      have htail := ih (currentTime := t) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      have hbatch_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates.1
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        currentTime work t times hbatch_applied]
      change
        (finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times).workload i =
          work i + (batchWork t i + (times.map fun u => batchWork u i).sum) -
            (gap.service i +
              (finiteGPSRunBatchTrace capacity weight batchWork t gap.workload times).service i)
      rw [htail, hgap_balance]
      ring

/-- The paper-facing distinct-time wrapper inherits the trace balance. -/
theorem finiteGPSRunExternalBatchTrace_balance
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (start : ℝ) (trace : FiniteGPSExternalBatchTrace start)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hbatch_nonneg : ∀ t ∈ trace.times, ∀ j, 0 ≤ batchWork t j)
    (i : Class) :
    (finiteGPSRunExternalBatchTrace capacity weight batchWork start work trace).workload i =
      work i + (trace.times.map fun t => batchWork t i).sum -
        (finiteGPSRunExternalBatchTrace capacity weight batchWork start work trace).service i := by
  exact finiteGPSRunBatchTrace_balance capacity weight work batchWork start trace.times
    hcapacity hweight_pos htotal_weight_le_one hwork_nonneg trace.chronological
    hbatch_nonneg i

end

end AppliedModelingLib.Probability.Queueing
