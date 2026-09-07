import AppliedModelingLib.Queueing.GPS.FiniteHorizon.FCFS
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.RateFloor
import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic

/-!
# Active-interval GPS rate floors for finite FCFS traces

The finite GPS executor stores a concrete service increment for every
constant-rate interval, while the FCFS ledger retains the literal jobs at
external endpoints.  This module records the trace-level consequence needed
for a later tagged-job comparison: sum only intervals whose chosen class was
backlogged at the *left* endpoint, and their stored class service dominates
the guaranteed GPS rate times their elapsed duration.

The active filter preserves the original concrete segment order.  In
particular, an endpoint arrival is not treated as active in the preceding
half-open interval, and an interval after the class has emptied is not
silently charged to that class.  This remains a finite deterministic result;
it makes no source, stochastic, Palm, stationary, completion, or tail claim.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class JobId : Type*}

variable [Fintype Class] [DecidableEq Class]

/-- The ordered subsequence of FCFS segment steps for which class `i` was
strictly backlogged at the segment's left endpoint. -/
def finiteGPSFCFSSegmentStepsActiveAtStart
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) :=
  steps.filter fun step => 0 < step.segment.startWorkload i

/-- Total elapsed duration of the concrete intervals in which `i` was active
at the left endpoint. -/
def finiteGPSFCFSSegmentStepsActiveDuration
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℝ :=
  ((finiteGPSFCFSSegmentStepsActiveAtStart i steps).map
    fun step => step.segment.duration).sum

/-- Total elapsed duration of a concrete FCFS segment list, with no claim
that the class was active in every interval. -/
def finiteGPSFCFSSegmentStepsTotalDuration
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℝ :=
  (steps.map fun step => step.segment.duration).sum

/-- Total stored class service over exactly the concrete intervals in which
`i` was active at the left endpoint. -/
def finiteGPSFCFSSegmentStepsActiveService
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℝ :=
  ((finiteGPSFCFSSegmentStepsActiveAtStart i steps).map
    fun step => step.segment.serviceIncrement i).sum

/-- The maximal initial consecutive run of concrete steps whose chosen class
is backlogged at every left endpoint.  Unlike the general active filter, this
stops permanently at the first empty-left-endpoint step, so it cannot silently
join a later busy period after a new source endpoint arrival reactivates the
class.  A tagged-job comparison should use this form after selecting the
literal suffix beginning at that job's arrival endpoint. -/
def finiteGPSFCFSSegmentStepsInitialActivePrefix
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    List (FiniteGPSFCFSSegmentJobStep Class JobId) :=
  steps.takeWhile fun step => 0 < step.segment.startWorkload i

/-- Exact elapsed duration of the initial consecutive busy prefix. -/
def finiteGPSFCFSSegmentStepsInitialActiveDuration
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℝ :=
  ((finiteGPSFCFSSegmentStepsInitialActivePrefix i steps).map
    fun step => step.segment.duration).sum

/-- Exact stored class service in the initial consecutive busy prefix. -/
def finiteGPSFCFSSegmentStepsInitialActiveService
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) : ℝ :=
  ((finiteGPSFCFSSegmentStepsInitialActivePrefix i steps).map
    fun step => step.segment.serviceIncrement i).sum

/-- The active-step filter keeps the original executable order and removes
only inactive steps. -/
theorem finiteGPSFCFSSegmentStepsActiveAtStart_sublist
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId)) :
    (finiteGPSFCFSSegmentStepsActiveAtStart i steps).Sublist steps := by
  exact List.filter_sublist

/-- Every step retained in the initial busy prefix was genuinely active at
its left endpoint. -/
theorem finiteGPSFCFSSegmentStepsInitialActivePrefix_mem_active
    (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (step : FiniteGPSFCFSSegmentJobStep Class JobId)
    (hstep : step ∈ finiteGPSFCFSSegmentStepsInitialActivePrefix i steps) :
    0 < step.segment.startWorkload i := by
  have hmem : step ∈ List.takeWhile
      (fun laterStep : FiniteGPSFCFSSegmentJobStep Class JobId =>
        decide (0 < laterStep.segment.startWorkload i)) steps := by
    simpa [finiteGPSFCFSSegmentStepsInitialActivePrefix] using hstep
  have hbool : decide (0 < step.segment.startWorkload i) = true :=
    @List.mem_takeWhile_imp _
      (fun laterStep : FiniteGPSFCFSSegmentJobStep Class JobId =>
        decide (0 < laterStep.segment.startWorkload i)) steps step hmem
  exact of_decide_eq_true hbool

/-- If each concrete step of a finite FCFS trace has the stored GPS
guaranteed-rate floor whenever `i` is active at its left endpoint, then the
sum of the actual stored service over the active ordered subsequence dominates
that floor times the exact active elapsed duration.  The premise is semantic:
it speaks only about each stored segment's workload, duration, and service,
not about a function name or a synthetic event numbering. -/
theorem finiteGPSFCFSSegmentSteps_weightedCapacity_mul_activeDuration_le_activeService
    (capacity : ℝ) (weight : Class → ℝ) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i) :
    capacity * weight i * finiteGPSFCFSSegmentStepsActiveDuration i steps ≤
      finiteGPSFCFSSegmentStepsActiveService i steps := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsActiveDuration,
        finiteGPSFCFSSegmentStepsActiveService,
        finiteGPSFCFSSegmentStepsActiveAtStart]
  | cons step steps ih =>
      have htail_floor : ∀ laterStep ∈ steps,
          0 < laterStep.segment.startWorkload i →
            capacity * weight i * laterStep.segment.duration ≤
              laterStep.segment.serviceIncrement i := by
        intro laterStep hlater hactive
        exact hsegment_floor laterStep (by simp [hlater]) hactive
      by_cases hactive : 0 < step.segment.startWorkload i
      · have hhead_floor :
            capacity * weight i * step.segment.duration ≤
              step.segment.serviceIncrement i :=
          hsegment_floor step (by simp) hactive
        have htail := ih htail_floor
        simpa [finiteGPSFCFSSegmentStepsActiveDuration,
          finiteGPSFCFSSegmentStepsActiveService,
          finiteGPSFCFSSegmentStepsActiveAtStart, hactive, mul_add] using
          (add_le_add hhead_floor htail)
      · have htail := ih htail_floor
        simpa [finiteGPSFCFSSegmentStepsActiveDuration,
          finiteGPSFCFSSegmentStepsActiveService,
          finiteGPSFCFSSegmentStepsActiveAtStart, hactive] using htail

/-- If a chosen class is active at every left endpoint of a selected concrete
trace, its total stored service over that exact ordered trace dominates its
GPS floor times the full trace duration.  Callers selecting a tagged-job busy
period must establish this left-endpoint premise; it is never inferred from a
later endpoint batch. -/
theorem finiteGPSFCFSSegmentSteps_weightedCapacity_mul_totalDuration_le_totalService_of_all_active
    (capacity : ℝ) (weight : Class → ℝ) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i)
    (hall_active : ∀ step ∈ steps, 0 < step.segment.startWorkload i) :
    capacity * weight i * finiteGPSFCFSSegmentStepsTotalDuration steps ≤
      finiteGPSFCFSSegmentStepsTotalService steps i := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsTotalDuration,
        finiteGPSFCFSSegmentStepsTotalService]
  | cons step steps ih =>
      have hhead_floor :
          capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i :=
        hsegment_floor step (by simp) (hall_active step (by simp))
      have htail_floor : ∀ laterStep ∈ steps,
          0 < laterStep.segment.startWorkload i →
            capacity * weight i * laterStep.segment.duration ≤
              laterStep.segment.serviceIncrement i := by
        intro laterStep hlaterStep hactive
        exact hsegment_floor laterStep (by simp [hlaterStep]) hactive
      have htail_active : ∀ laterStep ∈ steps,
          0 < laterStep.segment.startWorkload i := by
        intro laterStep hlaterStep
        exact hall_active laterStep (by simp [hlaterStep])
      have htail := ih htail_floor htail_active
      simpa [finiteGPSFCFSSegmentStepsTotalDuration,
        finiteGPSFCFSSegmentStepsTotalService, mul_add] using
        (add_le_add hhead_floor htail)

/-- The same stored-service floor for the consecutive busy prefix beginning
at the first supplied step.  This is the trace form appropriate after a
literal tagged-job arrival has selected its actual post-arrival suffix: no
interval after the class first empties can enter the bound. -/
theorem finiteGPSFCFSSegmentSteps_weightedCapacity_mul_initialActiveDuration_le_initialActiveService
    (capacity : ℝ) (weight : Class → ℝ) (i : Class)
    (steps : List (FiniteGPSFCFSSegmentJobStep Class JobId))
    (hsegment_floor : ∀ step ∈ steps,
      0 < step.segment.startWorkload i →
        capacity * weight i * step.segment.duration ≤ step.segment.serviceIncrement i) :
    capacity * weight i * finiteGPSFCFSSegmentStepsInitialActiveDuration i steps ≤
      finiteGPSFCFSSegmentStepsInitialActiveService i steps := by
  induction steps with
  | nil =>
      simp [finiteGPSFCFSSegmentStepsInitialActiveDuration,
        finiteGPSFCFSSegmentStepsInitialActiveService,
        finiteGPSFCFSSegmentStepsInitialActivePrefix]
  | cons step steps ih =>
      by_cases hactive : 0 < step.segment.startWorkload i
      · have hhead_floor :
            capacity * weight i * step.segment.duration ≤
              step.segment.serviceIncrement i :=
          hsegment_floor step (by simp) hactive
        have htail_floor : ∀ laterStep ∈ steps,
            0 < laterStep.segment.startWorkload i →
              capacity * weight i * laterStep.segment.duration ≤
                laterStep.segment.serviceIncrement i := by
          intro laterStep hlater hactive_later
          exact hsegment_floor laterStep (by simp [hlater]) hactive_later
        have htail := ih htail_floor
        simpa [finiteGPSFCFSSegmentStepsInitialActiveDuration,
          finiteGPSFCFSSegmentStepsInitialActiveService,
          finiteGPSFCFSSegmentStepsInitialActivePrefix, hactive, mul_add] using
          (add_le_add hhead_floor htail)
      · simp [finiteGPSFCFSSegmentStepsInitialActiveDuration,
          finiteGPSFCFSSegmentStepsInitialActiveService,
          finiteGPSFCFSSegmentStepsInitialActivePrefix, hactive]

end

end AppliedModelingLib.Probability.Queueing
