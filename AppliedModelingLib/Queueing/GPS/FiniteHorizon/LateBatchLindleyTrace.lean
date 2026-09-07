import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchIndexedTrace
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Lindley coordinates of an actual finite GPS batch trace

This module gives only a finite deterministic coordinate change.  An actual
GPS aggregate-step list stores the service accrued *before* each endpoint
batch.  In contrast, `lateBatchPreWorkloadFrom` starts immediately before its
first batch.  Accordingly, the Lindley service at index `n` is the service
stored by the next actual GPS step.  The terminal default used to totalize the
finite coordinate functions is never an arrival or a source event.

There is no stochastic, Palm, stationary, or infinite-trace assertion here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- A harmless out-of-range value for finite step-coordinate functions. -/
def finiteGPSAggregateLateBatchStepDefault : FiniteGPSAggregateLateBatchStep :=
  { startTime := 0
    batchTime := 0
    startAggregateWork := 0
    serviceAmount := 0
    batchAggregateWork := 0
    preBatchAggregateWork := 0
    postBatchAggregateWork := 0 }

/-- Totalized coordinate access to a finite actual GPS step list. -/
def finiteGPSAggregateLateBatchStepAt
    (steps : List FiniteGPSAggregateLateBatchStep) (n : Nat) :
    FiniteGPSAggregateLateBatchStep :=
  steps.getD n finiteGPSAggregateLateBatchStepDefault

/-- The endpoint batch at each finite actual GPS step. -/
def finiteGPSAggregateLateBatchBatch
    (steps : List FiniteGPSAggregateLateBatchStep) (n : Nat) : Real :=
  (finiteGPSAggregateLateBatchStepAt steps n).batchAggregateWork

/--
The service between actual endpoint batches `n` and `n + 1`.  This is recorded
in the next step because each actual step stores service from its preceding
clock to its own endpoint batch.
-/
def finiteGPSAggregateLateBatchInterBatchService
    (steps : List FiniteGPSAggregateLateBatchStep) (n : Nat) : Real :=
  (finiteGPSAggregateLateBatchStepAt steps (n + 1)).serviceAmount

/-- The pre-batch scalar state of the first actual finite GPS step. -/
def finiteGPSAggregateLateBatchInitialPre
    (steps : List FiniteGPSAggregateLateBatchStep) : Real :=
  (finiteGPSAggregateLateBatchStepAt steps 0).preBatchAggregateWork

/-- A valid step's post-batch scalar aggregate is pre-batch work plus its batch. -/
theorem FiniteGPSAggregateLateBatchStep.post_eq_pre_add_batch
    {step : FiniteGPSAggregateLateBatchStep} (hvalid : step.Valid) :
    step.postBatchAggregateWork =
      step.preBatchAggregateWork + step.batchAggregateWork := by
  rw [hvalid.2.2, hvalid.2.1, lateBatchUpdate]

/-- Pointwise validity of a totalized finite step coordinate in range. -/
theorem finiteGPSAggregateLateBatchStepAt_valid
    (steps : List FiniteGPSAggregateLateBatchStep)
    (hvalid : ∀ step ∈ steps, step.Valid)
    (n : Nat) (hn : n < steps.length) :
    (finiteGPSAggregateLateBatchStepAt steps n).Valid := by
  rw [finiteGPSAggregateLateBatchStepAt, List.getD_eq_getElem steps
    finiteGPSAggregateLateBatchStepDefault hn]
  exact hvalid steps[n] (List.getElem_mem hn)

/-- Consecutive in-range actual GPS steps join at the preceding post-batch state. -/
theorem FiniteGPSAggregateLateBatchStepsContiguous.next_start_eq_post
    (steps : List FiniteGPSAggregateLateBatchStep)
    (hcontiguous : FiniteGPSAggregateLateBatchStepsContiguous steps)
    (n : Nat) (hn : n + 1 < steps.length) :
    (finiteGPSAggregateLateBatchStepAt steps (n + 1)).startAggregateWork =
      (finiteGPSAggregateLateBatchStepAt steps n).postBatchAggregateWork := by
  induction steps generalizing n with
  | nil =>
      simp at hn
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp at hn
      | cons second tail =>
          cases n with
          | zero =>
              simpa [finiteGPSAggregateLateBatchStepAt] using hcontiguous.2.1
          | succ n =>
              have hn_tail : n + 1 < (second :: tail).length := by
                simp only [List.length_cons] at hn ⊢
                omega
              have htail :
                  FiniteGPSAggregateLateBatchStepsContiguous (second :: tail) :=
                hcontiguous.2.2
              simpa [finiteGPSAggregateLateBatchStepAt, Nat.succ_eq_add_one,
                Nat.add_assoc] using ih htail n hn_tail

/--
For a finite contiguous valid step list, each recorded actual pre-batch
aggregate is exactly the service-before-arrival Lindley coordinate.  The
initial coordinate is the first recorded pre-batch state, and the shifted
service convention is explicit in `finiteGPSAggregateLateBatchInterBatchService`.
-/
theorem finiteGPSAggregateLateBatchStepAt_pre_eq_lateBatchPreWorkloadFrom
    (steps : List FiniteGPSAggregateLateBatchStep)
    (hvalid : ∀ step ∈ steps, step.Valid)
    (hcontiguous : FiniteGPSAggregateLateBatchStepsContiguous steps)
    (n : Nat) (hn : n < steps.length) :
    (finiteGPSAggregateLateBatchStepAt steps n).preBatchAggregateWork =
      lateBatchPreWorkloadFrom
        (finiteGPSAggregateLateBatchInitialPre steps)
        (finiteGPSAggregateLateBatchBatch steps)
        (finiteGPSAggregateLateBatchInterBatchService steps) n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      have hn_prev : n < steps.length := by omega
      have hvalid_prev := finiteGPSAggregateLateBatchStepAt_valid steps hvalid n hn_prev
      have hvalid_next := finiteGPSAggregateLateBatchStepAt_valid steps hvalid (n + 1) hn
      have hcontiguous_next :=
        hcontiguous.next_start_eq_post steps n hn
      calc
        (finiteGPSAggregateLateBatchStepAt steps (n + 1)).preBatchAggregateWork =
            max ((finiteGPSAggregateLateBatchStepAt steps n).postBatchAggregateWork -
              (finiteGPSAggregateLateBatchStepAt steps (n + 1)).serviceAmount) 0 := by
                rw [hvalid_next.2.1, hcontiguous_next]
        _ = max ((finiteGPSAggregateLateBatchStepAt steps n).preBatchAggregateWork +
              finiteGPSAggregateLateBatchBatch steps n -
              finiteGPSAggregateLateBatchInterBatchService steps n) 0 := by
                rw [FiniteGPSAggregateLateBatchStep.post_eq_pre_add_batch hvalid_prev]
                rfl
        _ = max (lateBatchPreWorkloadFrom
              (finiteGPSAggregateLateBatchInitialPre steps)
              (finiteGPSAggregateLateBatchBatch steps)
              (finiteGPSAggregateLateBatchInterBatchService steps) n +
              finiteGPSAggregateLateBatchBatch steps n -
              finiteGPSAggregateLateBatchInterBatchService steps n) 0 := by
                rw [ih hn_prev]
        _ = lateBatchPreWorkloadFrom
              (finiteGPSAggregateLateBatchInitialPre steps)
              (finiteGPSAggregateLateBatchBatch steps)
              (finiteGPSAggregateLateBatchInterBatchService steps) (n + 1) := by
                rw [← lateBatchPostWorkloadFrom_eq_pre_add_batch]
                rfl

/--
The preceding coordinate theorem specialized to the executable finite GPS
runner.  It is only a deterministic finite-trace statement: `times` are the
literal supplied endpoints, and no terminal default coordinate is a batch.
-/
theorem finiteGPSAggregateLateBatchSteps_pre_eq_lateBatchPreWorkloadFrom
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i)
    (n : Nat)
    (hn : n < (finiteGPSAggregateLateBatchSteps
      capacity weight batchWork currentTime work times).length) :
    (finiteGPSAggregateLateBatchStepAt
      (finiteGPSAggregateLateBatchSteps
        capacity weight batchWork currentTime work times) n).preBatchAggregateWork =
      lateBatchPreWorkloadFrom
        (finiteGPSAggregateLateBatchInitialPre
          (finiteGPSAggregateLateBatchSteps
            capacity weight batchWork currentTime work times))
        (finiteGPSAggregateLateBatchBatch
          (finiteGPSAggregateLateBatchSteps
            capacity weight batchWork currentTime work times))
        (finiteGPSAggregateLateBatchInterBatchService
          (finiteGPSAggregateLateBatchSteps
            capacity weight batchWork currentTime work times)) n := by
  let steps := finiteGPSAggregateLateBatchSteps
    capacity weight batchWork currentTime work times
  have hvalid : ∀ step ∈ steps, step.Valid := by
    simpa [steps] using
      (finiteGPSAggregateLateBatchSteps_all_valid capacity weight work batchWork currentTime
        times hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg)
  have hcontiguous : FiniteGPSAggregateLateBatchStepsContiguous steps := by
    simpa [steps] using
      (finiteGPSAggregateLateBatchSteps_contiguous
        capacity weight batchWork currentTime work times)
  change n < steps.length at hn
  simpa [steps] using
    (finiteGPSAggregateLateBatchStepAt_pre_eq_lateBatchPreWorkloadFrom
      steps hvalid hcontiguous n hn)

/--
A negative finite net-work prefix of a valid contiguous step list forces a
recorded pre-batch aggregate reset.  The conclusion deliberately concerns the
state before an actual endpoint batch; it does not call that endpoint batch
empty and it does not create a terminal source event.
-/
theorem finiteGPSAggregateLateBatchStepAt_exists_pre_reset_of_initial_add_sum_net_neg
    (steps : List FiniteGPSAggregateLateBatchStep)
    (hvalid : ∀ step ∈ steps, step.Valid)
    (hcontiguous : FiniteGPSAggregateLateBatchStepsContiguous steps)
    {N : Nat} (hN : N < steps.length)
    (hneg : finiteGPSAggregateLateBatchInitialPre steps +
      Finset.sum (Finset.range N) (fun n =>
        finiteGPSAggregateLateBatchBatch steps n -
          finiteGPSAggregateLateBatchInterBatchService steps n) < 0) :
    ∃ m, 0 < m ∧ m ≤ N ∧
      (finiteGPSAggregateLateBatchStepAt steps m).preBatchAggregateWork = 0 := by
  have hlength_pos : 0 < steps.length := lt_of_le_of_lt (Nat.zero_le N) hN
  have hvalid_zero :=
    finiteGPSAggregateLateBatchStepAt_valid steps hvalid 0 hlength_pos
  have hinitial : 0 ≤ finiteGPSAggregateLateBatchInitialPre steps := by
    rw [finiteGPSAggregateLateBatchInitialPre, hvalid_zero.2.1]
    exact le_max_right _ _
  rcases exists_lateBatchPreResetFrom_of_initial_add_sum_net_neg
    (initial := finiteGPSAggregateLateBatchInitialPre steps)
    (batch := finiteGPSAggregateLateBatchBatch steps)
    (service := finiteGPSAggregateLateBatchInterBatchService steps)
    (N := N) hinitial hneg with ⟨m, hm_pos, hm_le, hm_reset⟩
  refine ⟨m, hm_pos, hm_le, ?_⟩
  rw [finiteGPSAggregateLateBatchStepAt_pre_eq_lateBatchPreWorkloadFrom
    steps hvalid hcontiguous m (lt_of_le_of_lt hm_le hN)]
  exact hm_reset

/--
The negative-prefix reset witness specialized to an actual finite executable
GPS trace.  It is a scalar pre-batch statement only; a consumer that needs a
vector empty state must separately relate that concrete pre-batch state to
its aggregate.
-/
theorem finiteGPSAggregateLateBatchSteps_exists_pre_reset_of_initial_add_sum_net_neg
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i)
    {N : Nat}
    (hN : N < (finiteGPSAggregateLateBatchSteps
      capacity weight batchWork currentTime work times).length)
    (hneg : finiteGPSAggregateLateBatchInitialPre
      (finiteGPSAggregateLateBatchSteps
        capacity weight batchWork currentTime work times) +
      Finset.sum (Finset.range N) (fun n =>
        finiteGPSAggregateLateBatchBatch
          (finiteGPSAggregateLateBatchSteps
            capacity weight batchWork currentTime work times) n -
          finiteGPSAggregateLateBatchInterBatchService
            (finiteGPSAggregateLateBatchSteps
              capacity weight batchWork currentTime work times) n) < 0) :
    ∃ m, 0 < m ∧ m ≤ N ∧
      (finiteGPSAggregateLateBatchStepAt
        (finiteGPSAggregateLateBatchSteps
          capacity weight batchWork currentTime work times) m).preBatchAggregateWork = 0 := by
  let steps := finiteGPSAggregateLateBatchSteps
    capacity weight batchWork currentTime work times
  have hvalid : ∀ step ∈ steps, step.Valid := by
    simpa [steps] using
      (finiteGPSAggregateLateBatchSteps_all_valid capacity weight work batchWork currentTime
        times hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg)
  have hcontiguous : FiniteGPSAggregateLateBatchStepsContiguous steps := by
    simpa [steps] using
      (finiteGPSAggregateLateBatchSteps_contiguous
        capacity weight batchWork currentTime work times)
  change N < steps.length at hN
  change finiteGPSAggregateLateBatchInitialPre steps +
      Finset.sum (Finset.range N) (fun n =>
        finiteGPSAggregateLateBatchBatch steps n -
          finiteGPSAggregateLateBatchInterBatchService steps n) < 0 at hneg
  simpa [steps] using
    (finiteGPSAggregateLateBatchStepAt_exists_pre_reset_of_initial_add_sum_net_neg
      steps hvalid hcontiguous hN hneg)

end

end AppliedModelingLib.Probability.Queueing
