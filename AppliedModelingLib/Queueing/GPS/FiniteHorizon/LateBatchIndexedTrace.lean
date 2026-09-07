import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchTrace
import Mathlib.Tactic

/-!
# Indexed aggregate steps of a finite GPS batch trace

This module gives a minimal list-indexed view of the actual finite GPS batch
runner.  Each recorded entry is produced by one concrete `finiteGPSRunGap` and
records its aggregate pre-batch and post-batch values.  The main invariant
states that every entry obeys the service-before-arrival scalar update.

There is intentionally no stochastic, Palm, or infinite-trace claim here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Aggregate information from one actual finite GPS gap. -/
structure FiniteGPSAggregateLateBatchStep where
  startTime : Real
  batchTime : Real
  startAggregateWork : Real
  serviceAmount : Real
  batchAggregateWork : Real
  preBatchAggregateWork : Real
  postBatchAggregateWork : Real

/-- The scalar correctness conditions for one recorded late-batch step. -/
def FiniteGPSAggregateLateBatchStep.Valid
    (step : FiniteGPSAggregateLateBatchStep) : Prop :=
  0 ≤ step.serviceAmount ∧
    step.preBatchAggregateWork =
      max (step.startAggregateWork - step.serviceAmount) 0 ∧
    step.postBatchAggregateWork =
      lateBatchUpdate step.startAggregateWork step.serviceAmount step.batchAggregateWork

/--
The canonical list of actual aggregate GPS steps.  The next recursive state is
the class-valued workload returned by the executable gap runner, rather than a
separately assumed scalar recurrence.
-/
def finiteGPSAggregateLateBatchSteps
    (capacity : Real) (weight : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (work : Class -> Real) : List Real ->
      List FiniteGPSAggregateLateBatchStep
  | [] => []
  | batchTime :: times =>
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork batchTime) (batchTime - currentTime)
      { startTime := currentTime
        batchTime := batchTime
        startAggregateWork := finiteGPSAggregateWork work
        serviceAmount := capacity * (batchTime - currentTime)
        batchAggregateWork := finiteGPSAggregateWork (batchWork batchTime)
        preBatchAggregateWork :=
          finiteGPSAggregateWork gap.workload - finiteGPSAggregateWork (batchWork batchTime)
        postBatchAggregateWork := finiteGPSAggregateWork gap.workload } ::
        finiteGPSAggregateLateBatchSteps capacity weight batchWork batchTime gap.workload times

omit [DecidableEq Class] in
/-- Every recorded step is indexed by one of the literal supplied batch times. -/
theorem finiteGPSAggregateLateBatchSteps_mem_batchTime
    (capacity : Real) (weight : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (work : Class -> Real) (times : List Real)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ finiteGPSAggregateLateBatchSteps
      capacity weight batchWork currentTime work times) :
    step.batchTime ∈ times := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSAggregateLateBatchSteps] at hmem
  | cons batchTime times ih =>
      simp only [finiteGPSAggregateLateBatchSteps, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst step
        simp
      · exact List.mem_cons.mpr (Or.inr
          (ih (currentTime := batchTime) (work := _) htail))

omit [DecidableEq Class] in
/-- The stored batch aggregate of every recorded step is its literal batch's aggregate work. -/
theorem finiteGPSAggregateLateBatchSteps_mem_batchAggregateWork
    (capacity : Real) (weight : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (work : Class -> Real) (times : List Real)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ finiteGPSAggregateLateBatchSteps
      capacity weight batchWork currentTime work times) :
    step.batchAggregateWork = finiteGPSAggregateWork (batchWork step.batchTime) := by
  induction times generalizing currentTime work with
  | nil =>
      simp [finiteGPSAggregateLateBatchSteps] at hmem
  | cons batchTime times ih =>
      simp only [finiteGPSAggregateLateBatchSteps, List.mem_cons] at hmem
      rcases hmem with hhead | htail
      · subst step
        rfl
      · exact ih (currentTime := batchTime) (work := _) htail

/--
The head of the canonical actual-step list has the exact reflected aggregate
pre-batch and late-batch post-batch formulas.
-/
theorem finiteGPSAggregateLateBatchSteps_cons
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime batchTime : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hcurrentTime_le_batchTime : currentTime ≤ batchTime) :
    finiteGPSAggregateLateBatchSteps capacity weight batchWork currentTime work
      (batchTime :: times) =
      { startTime := currentTime
        batchTime := batchTime
        startAggregateWork := finiteGPSAggregateWork work
        serviceAmount := capacity * (batchTime - currentTime)
        batchAggregateWork := finiteGPSAggregateWork (batchWork batchTime)
        preBatchAggregateWork :=
          max (finiteGPSAggregateWork work - capacity * (batchTime - currentTime)) 0
        postBatchAggregateWork :=
          lateBatchUpdate (finiteGPSAggregateWork work)
            (capacity * (batchTime - currentTime))
            (finiteGPSAggregateWork (batchWork batchTime)) } ::
        finiteGPSAggregateLateBatchSteps capacity weight batchWork batchTime
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork batchTime)
            (batchTime - currentTime)).workload times := by
  let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
    capacity weight work (batchWork batchTime) (batchTime - currentTime)
  have hpre := finiteGPSRunGap_aggregatePreBatchWork_eq_max_sub_capacity_mul
    capacity (weight := weight) (work := work) (batchWork := batchWork batchTime)
    (batchTime - currentTime) hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    (sub_nonneg.mpr hcurrentTime_le_batchTime)
  have hpost := finiteGPSRunGap_aggregateWork_eq_lateBatchUpdate
    capacity (weight := weight) (work := work) (batchWork := batchWork batchTime)
    (batchTime - currentTime) hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
    (sub_nonneg.mpr hcurrentTime_le_batchTime)
  have hpre' :
      finiteGPSAggregateWork gap.workload - finiteGPSAggregateWork (batchWork batchTime) =
        max (finiteGPSAggregateWork work - capacity * (batchTime - currentTime)) 0 := by
    simpa [gap] using hpre
  have hpost' :
      finiteGPSAggregateWork gap.workload =
        lateBatchUpdate (finiteGPSAggregateWork work)
          (capacity * (batchTime - currentTime))
          (finiteGPSAggregateWork (batchWork batchTime)) := by
    simpa [gap] using hpost
  simp only [finiteGPSAggregateLateBatchSteps]
  rw [hpre', hpost']

/--
Every entry of an actual chronological finite GPS step list satisfies the
service-before-arrival aggregate update.  This is the list-level theorem that
can be consumed by an indexed source/trace adapter.
-/
theorem finiteGPSAggregateLateBatchSteps_all_valid
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i) :
    ∀ step ∈ finiteGPSAggregateLateBatchSteps capacity weight batchWork currentTime work times,
      step.Valid := by
  induction times generalizing currentTime work with
  | nil => simp [finiteGPSAggregateLateBatchSteps]
  | cons batchTime times ih =>
      rcases hchronological with ⟨hcurrentTime_le_batchTime, hchronological_tail⟩
      have hbatch_head : ∀ i, 0 ≤ batchWork batchTime i := by
        intro i
        exact hbatch_nonneg batchTime (by simp) i
      have hbatch_tail : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i := by
        intro t ht i
        exact hbatch_nonneg t (by simp [ht]) i
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
        capacity weight work (batchWork batchTime) (batchTime - currentTime)
      have hgap_nonneg : ∀ i, 0 ≤ gap.workload i := by
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses work).card + 1) capacity weight work
          (batchWork batchTime) (batchTime - currentTime) hwork_nonneg hbatch_head
      have htail := ih (currentTime := batchTime) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      rw [finiteGPSAggregateLateBatchSteps_cons capacity weight work batchWork
        currentTime batchTime times hcapacity hweight_pos htotal_weight_le_one hwork_nonneg
        hcurrentTime_le_batchTime]
      intro step hmem
      rcases List.mem_cons.mp hmem with hhead | htailmem
      · subst step
        constructor
        · exact mul_nonneg hcapacity.le (sub_nonneg.mpr hcurrentTime_le_batchTime)
        constructor <;> rfl
      · simpa [gap] using htail step htailmem

/--
Consecutive canonical entries are contiguous: a later step begins at the
preceding batch time with the preceding post-batch aggregate workload.
-/
def FiniteGPSAggregateLateBatchStepsContiguous :
    List FiniteGPSAggregateLateBatchStep -> Prop
  | [] => True
  | _ :: [] => True
  | first :: second :: rest =>
      second.startTime = first.batchTime ∧
        second.startAggregateWork = first.postBatchAggregateWork ∧
        FiniteGPSAggregateLateBatchStepsContiguous (second :: rest)

omit [DecidableEq Class] in
/-- The canonical actual-step list has the expected adjacent-state continuity. -/
theorem finiteGPSAggregateLateBatchSteps_contiguous
    (capacity : Real) (weight : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (work : Class -> Real) (times : List Real) :
    FiniteGPSAggregateLateBatchStepsContiguous
      (finiteGPSAggregateLateBatchSteps capacity weight batchWork currentTime work times) := by
  induction times generalizing currentTime work with
  | nil => trivial
  | cons batchTime times ih =>
      cases times with
      | nil => simp [finiteGPSAggregateLateBatchSteps,
          FiniteGPSAggregateLateBatchStepsContiguous]
      | cons nextTime times =>
          let gap := finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork batchTime) (batchTime - currentTime)
          have htail := ih (currentTime := batchTime) (work := gap.workload)
          simpa [finiteGPSAggregateLateBatchSteps,
            FiniteGPSAggregateLateBatchStepsContiguous, gap] using htail

/-- A valid pre-batch aggregate is zero exactly when the available service covers the start. -/
theorem FiniteGPSAggregateLateBatchStep.preBatchAggregateWork_eq_zero_iff
    {step : FiniteGPSAggregateLateBatchStep} (hvalid : step.Valid) :
    step.preBatchAggregateWork = 0 ↔ step.startAggregateWork ≤ step.serviceAmount := by
  rw [hvalid.2.1]
  constructor
  · intro hzero
    have hsub : step.startAggregateWork - step.serviceAmount ≤ 0 := by
      calc
        step.startAggregateWork - step.serviceAmount ≤
            max (step.startAggregateWork - step.serviceAmount) 0 := le_max_left _ _
        _ = 0 := hzero
    exact sub_nonpos.mp hsub
  · intro hcover
    exact max_eq_right (sub_nonpos.mpr hcover)

/--
At a valid pre-batch aggregate reset, the post-batch aggregate is exactly the
new batch aggregate, so the scalar post-state has forgotten its earlier
aggregate workload.
-/
theorem FiniteGPSAggregateLateBatchStep.post_eq_batch_of_preBatchAggregateWork_eq_zero
    {step : FiniteGPSAggregateLateBatchStep} (hvalid : step.Valid)
    (hreset : step.preBatchAggregateWork = 0) :
    step.postBatchAggregateWork = step.batchAggregateWork := by
  have hreflected : max (step.startAggregateWork - step.serviceAmount) 0 = 0 := by
    rw [← hvalid.2.1]
    exact hreset
  rw [hvalid.2.2, lateBatchUpdate, hreflected]
  ring

/--
The reusable indexed reset bridge: any recorded step of a physical
chronological trace whose pre-batch aggregate is zero has post aggregate equal
to its own endpoint batch aggregate.
-/
theorem finiteGPSAggregateLateBatchSteps_mem_post_eq_batch_of_pre_reset
    (capacity : Real) (weight work : Class -> Real) (batchWork : Real -> Class -> Real)
    (currentTime : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ i, 0 ≤ work i)
    (hchronological : FiniteGPSChronologicalFrom currentTime times)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i)
    {step : FiniteGPSAggregateLateBatchStep}
    (hmem : step ∈ finiteGPSAggregateLateBatchSteps
      capacity weight batchWork currentTime work times)
    (hreset : step.preBatchAggregateWork = 0) :
    step.postBatchAggregateWork = step.batchAggregateWork := by
  exact step.post_eq_batch_of_preBatchAggregateWork_eq_zero
    (finiteGPSAggregateLateBatchSteps_all_valid capacity weight work batchWork currentTime times
      hcapacity hweight_pos htotal_weight_le_one hwork_nonneg hchronological hbatch_nonneg
      step hmem)
    hreset

end

end AppliedModelingLib.Probability.Queueing
