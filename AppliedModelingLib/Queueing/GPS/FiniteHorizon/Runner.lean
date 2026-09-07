import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchEvent
import Mathlib.Tactic

/-!
# Finite GPS gap runner

This module iterates the executable batch-event kernel through the internal
class-emptying events that can occur before one external arrival batch.  Its
arbitrary-fuel recursion is an intermediate computation; the active-class
descent lemma below is the ingredient needed to prove the eventual finite-fuel
termination bound.

It is deterministic and contains no stochastic or stationary claim.  The SLA
adapter supplies its external batches from the direct admitted Poisson/work
carrier.
-/

namespace AppliedModelingLib.Probability.Queueing

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

omit [DecidableEq Class] in
/-- The concrete next-event duration never exceeds the supplied external
batch delay. -/
theorem finiteGPSNextStepDuration_le_nextBatchDelay
    (capacity : ℝ) (weight work : Class → ℝ) (nextBatchDelay : ℝ) :
    finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤ nextBatchDelay := by
  unfold finiteGPSNextStepDuration
  split
  · exact min_le_left _ _
  · rfl

/-- If the next event is strictly before the external batch, it is a genuine
internal completion event: at least one active class is removed and no inactive
class becomes active.  This is the finite descent fact that bounds the number
of internal events in every external-batch gap. -/
theorem finiteGPSActiveClasses_ssubset_nextEvent_of_internal
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hinternal :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay) :
    finiteGPSActiveClasses
        (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) ⊂
      finiteGPSActiveClasses work := by
  have hbatch_zero : ∀ i,
      finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i = 0 := by
    intro i
    simp [finiteGPSBatchApplied, hinternal]
  have hsubset :
      finiteGPSActiveClasses
          (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay) ⊆
        finiteGPSActiveClasses work := by
    intro i hi
    apply mem_finiteGPSActiveClasses_iff.mpr
    by_contra hinactive
    have hwork_zero : work i = 0 :=
      le_antisymm (le_of_not_gt hinactive) (hwork_nonneg i)
    have hrate_zero : finiteGPSClassRate capacity weight work i = 0 :=
      finiteGPSClassRate_eq_zero_of_not_active hinactive
    have hnext_zero :
        finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i = 0 := by
      unfold finiteGPSNextEventState
      rw [hbatch_zero i]
      simp [finiteGPSRemainingAfter, hwork_zero, hrate_zero]
    have hnext_pos : 0 <
        finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i :=
      mem_finiteGPSActiveClasses_iff.mp hi
    linarith
  apply (Finset.ssubset_iff_of_subset hsubset).mpr
  have hactive_nonempty : (finiteGPSActiveClasses work).Nonempty := by
    by_contra hnone
    apply hinternal
    simp [finiteGPSNextStepDuration, hnone]
  obtain ⟨j, hj, hj_min⟩ :=
    Finset.exists_mem_eq_inf' hactive_nonempty
      (finiteGPSClassEmptyDelay capacity weight work)
  refine ⟨j, hj, ?_⟩
  have hduration_le :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay ≤ nextBatchDelay :=
    finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work nextBatchDelay
  have hduration_lt :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay < nextBatchDelay :=
    lt_of_le_of_ne hduration_le hinternal
  have hearliest_lt :
      finiteGPSEarliestEmptyDelay capacity weight work < nextBatchDelay := by
    have hmin_lt : min nextBatchDelay
        (finiteGPSEarliestEmptyDelay capacity weight work) < nextBatchDelay := by
      simpa [finiteGPSNextStepDuration, hactive_nonempty] using hduration_lt
    rcases min_lt_iff.mp hmin_lt with hbad | hgood
    · exact (lt_irrefl _ hbad).elim
    · exact hgood
  have hduration_eq_earliest :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay =
        finiteGPSEarliestEmptyDelay capacity weight work := by
    simp [finiteGPSNextStepDuration, hactive_nonempty,
      min_eq_right hearliest_lt.le]
  have hduration_eq_empty :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay =
      finiteGPSClassEmptyDelay capacity weight work j :=
    calc
      finiteGPSNextStepDuration capacity weight work nextBatchDelay =
          finiteGPSEarliestEmptyDelay capacity weight work :=
        hduration_eq_earliest
      _ = (finiteGPSActiveClasses work).inf' hactive_nonempty
          (finiteGPSClassEmptyDelay capacity weight work) := by
        simp [finiteGPSEarliestEmptyDelay, hactive_nonempty]
      _ = finiteGPSClassEmptyDelay capacity weight work j := hj_min
  have hrate_pos : 0 < finiteGPSClassRate capacity weight work j :=
    finiteGPSClassRate_pos_of_active hcapacity hweight_pos htotal_weight_le_one
      (mem_finiteGPSActiveClasses_iff.mp hj)
  have hremaining_zero :
      finiteGPSRemainingAfter capacity weight work
          (finiteGPSNextStepDuration capacity weight work nextBatchDelay) j = 0 := by
    rw [finiteGPSRemainingAfter_eq_linear_nextStep hcapacity hweight_pos
      htotal_weight_le_one hwork_nonneg, hduration_eq_empty]
    unfold finiteGPSClassEmptyDelay
    field_simp [hrate_pos.ne']
    ring
  have hnext_zero :
      finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j = 0 := by
    unfold finiteGPSNextEventState
    rw [hbatch_zero j, hremaining_zero]
    norm_num
  rw [mem_finiteGPSActiveClasses_iff]
  simp [hnext_zero]

omit [DecidableEq Class] in
/-- A strictly internal step has no applied external batch, so its computed
next workload is nonnegative independently of the pending batch's values. -/
theorem finiteGPSNextEventState_nonneg_of_internal
    {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    (hinternal :
      finiteGPSNextStepDuration capacity weight work nextBatchDelay ≠ nextBatchDelay) :
    ∀ i, 0 ≤ finiteGPSNextEventState capacity weight work batchWork nextBatchDelay i := by
  intro i
  have hbatch_zero :
      finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i = 0 := by
    simp [finiteGPSBatchApplied, hinternal]
  unfold finiteGPSNextEventState
  rw [hbatch_zero]
  exact add_nonneg (le_max_left _ _) (by simp)

/-- Computed outcome of advancing toward one external batch.  All fields are
data produced by `finiteGPSRunGap`; none are caller-supplied execution
obligations. -/
structure FiniteGPSGapRunResult (Class : Type*) where
  workload : Class → ℝ
  remainingDelay : ℝ
  service : Class → ℝ
  batchApplied : Bool

/-- Execute at most `fuel` event decisions toward an external batch.  An
internal emptying event contributes no batch work and recurs on the residual
time.  When the external batch is reached, the underlying kernel applies the
whole batch, including an exact arrival/departure tie. -/
def finiteGPSRunGap
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) : FiniteGPSGapRunResult Class :=
  match fuel with
  | 0 =>
      { workload := work
        remainingDelay := nextBatchDelay
        service := fun _ => 0
        batchApplied := false }
  | fuel + 1 =>
      let duration := finiteGPSNextStepDuration capacity weight work nextBatchDelay
      let nextWork :=
        finiteGPSNextEventState capacity weight work batchWork nextBatchDelay
      let stepService :=
        finiteGPSServiceIncrement capacity weight work duration
      if duration = nextBatchDelay then
        { workload := nextWork
          remainingDelay := 0
          service := stepService
          batchApplied := true }
      else
        let later := finiteGPSRunGap fuel capacity weight nextWork batchWork
          (nextBatchDelay - duration)
        { workload := later.workload
          remainingDelay := later.remainingDelay
          service := fun i => stepService i + later.service i
          batchApplied := later.batchApplied }

/-- A gap run telescopes every concrete kernel balance.  If the supplied fuel
has not yet reached the external batch, the result correctly records that no
batch has been applied; the termination theorem below rules this case out at
the active-class fuel bound. -/
theorem finiteGPSRunGap_balance
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) (i : Class) :
    (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload i =
      work i +
        (if (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).batchApplied =
            true then batchWork i else 0) -
        (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).service i := by
  induction fuel generalizing work nextBatchDelay with
  | zero => simp [finiteGPSRunGap]
  | succ fuel ih =>
      unfold finiteGPSRunGap
      dsimp only
      split
      · rename_i hbatch
        simpa [hbatch, finiteGPSBatchApplied] using
          (finiteGPSNextEventState_balance capacity weight work batchWork
            nextBatchDelay i)
      · rename_i hbatch
        have hstep := finiteGPSNextEventState_balance capacity weight work
          batchWork nextBatchDelay i
        have hbatch_zero :
            finiteGPSBatchApplied capacity weight work batchWork nextBatchDelay i = 0 := by
          simp [finiteGPSBatchApplied, hbatch]
        have htail := ih
          (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          (nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
        rw [hbatch_zero] at hstep
        rw [htail, hstep]
        ring

omit [DecidableEq Class] in
/-- Starting from a nonnegative delay, an arbitrary-fuel gap computation never
records a negative residual delay.  This does not assert that the external
batch was reached; it only identifies the actual clock position of a stopped
bounded computation. -/
theorem finiteGPSRunGap_remainingDelay_nonneg
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay) :
    0 ≤ (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).remainingDelay := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      simpa [finiteGPSRunGap] using hnextBatchDelay_nonneg
  | succ fuel ih =>
      unfold finiteGPSRunGap
      dsimp only
      split
      · norm_num
      · apply ih
        exact sub_nonneg.mpr
          (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
            nextBatchDelay)

/-- The arbitrary-fuel gap computation preserves nonnegative workload when
the pending external batch is nonnegative.  Internal branches apply no batch;
the one terminating branch applies the stated nonnegative batch. -/
theorem finiteGPSRunGap_workload_nonneg
    (fuel : ℕ) (capacity : ℝ) (weight work batchWork : Class → ℝ)
    (nextBatchDelay : ℝ) (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hbatch_nonneg : ∀ j, 0 ≤ batchWork j) :
    ∀ i, 0 ≤ (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).workload i := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      simpa [finiteGPSRunGap] using hwork_nonneg
  | succ fuel ih =>
      unfold finiteGPSRunGap
      dsimp only
      split
      · intro i
        simpa using
          (finiteGPSNextEventState_nonneg (capacity := capacity) (weight := weight)
            (work := work) (batchWork := batchWork)
            (nextBatchDelay := nextBatchDelay) (i := i) hbatch_nonneg)
      · rename_i hinternal
        exact ih
          (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
          (nextBatchDelay := nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay)
          (finiteGPSNextEventState_nonneg_of_internal (batchWork := batchWork)
            hinternal)

/-- Positive capacity and weights make active-class cardinality plus one
sufficient fuel to reach the pending external batch.  Each recursive branch is
strictly internal, and `finiteGPSActiveClasses_ssubset_nextEvent_of_internal`
decreases the finite cardinality; ties with the batch terminate in the current
step and apply the batch once. -/
theorem finiteGPSRunGap_terminates_of_activeCard_lt
    (fuel : ℕ) {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel) :
    (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).batchApplied = true ∧
      (finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay).remainingDelay = 0 := by
  induction fuel generalizing work nextBatchDelay with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      unfold finiteGPSRunGap
      dsimp only
      split
      · constructor <;> rfl
      · rename_i hinternal
        have hnext_work_nonneg : ∀ j, 0 ≤
            finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j :=
          finiteGPSNextEventState_nonneg_of_internal hinternal
        have hresidual_nonneg : 0 ≤ nextBatchDelay -
            finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
          exact sub_nonneg.mpr
            (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
              nextBatchDelay)
        have hdescent := finiteGPSActiveClasses_ssubset_nextEvent_of_internal
          (batchWork := batchWork) hcapacity hweight_pos htotal_weight_le_one
          hwork_nonneg hinternal
        have hcard :
            (finiteGPSActiveClasses
              (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)).card <
              fuel := by
          exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
            (Nat.lt_succ_iff.mp hfuel)
        have htail := ih hnext_work_nonneg hresidual_nonneg hcard
        simpa [finiteGPSRunGap, hinternal] using htail

/-- Once the event-decision fuel is strictly larger than the active-class
count, the bounded GPS gap result no longer depends on the particular fuel
budget.  This is a pathwise executable fact: the proof follows the actual
internal-emptying recursion and uses its strict active-set descent.  It lets
later finite-dimensional arguments use one uniform `Fintype.card + 1` bound
without changing the scheduler result. -/
theorem finiteGPSRunGap_eq_of_activeCard_lt
    (fuel fuel' : ℕ) {capacity nextBatchDelay : ℝ} {weight work batchWork : Class → ℝ}
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hnextBatchDelay_nonneg : 0 ≤ nextBatchDelay)
    (hfuel : (finiteGPSActiveClasses work).card < fuel)
    (hfuel' : (finiteGPSActiveClasses work).card < fuel') :
    finiteGPSRunGap fuel capacity weight work batchWork nextBatchDelay =
      finiteGPSRunGap fuel' capacity weight work batchWork nextBatchDelay := by
  induction fuel generalizing fuel' work nextBatchDelay with
  | zero =>
      exact (Nat.not_lt_zero _ hfuel).elim
  | succ fuel ih =>
      cases fuel' with
      | zero =>
          exact (Nat.not_lt_zero _ hfuel').elim
      | succ fuel' =>
          by_cases hterminal :
              finiteGPSNextStepDuration capacity weight work nextBatchDelay =
                nextBatchDelay
          · simp [finiteGPSRunGap, hterminal]
          · have hnext_work_nonneg : ∀ j, 0 ≤
                finiteGPSNextEventState capacity weight work batchWork nextBatchDelay j :=
              finiteGPSNextEventState_nonneg_of_internal (batchWork := batchWork)
                hterminal
            have hresidual_nonneg : 0 ≤ nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay := by
              exact sub_nonneg.mpr
                (finiteGPSNextStepDuration_le_nextBatchDelay capacity weight work
                  nextBatchDelay)
            have hdescent := finiteGPSActiveClasses_ssubset_nextEvent_of_internal
              (batchWork := batchWork) hcapacity hweight_pos htotal_weight_le_one
              hwork_nonneg hterminal
            have hnext_card_lt_fuel :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)).card <
                    fuel := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel)
            have hnext_card_lt_fuel' :
                (finiteGPSActiveClasses
                  (finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)).card <
                    fuel' := by
              exact lt_of_lt_of_le (Finset.card_lt_card hdescent)
                (Nat.lt_succ_iff.mp hfuel')
            have htail := ih (fuel' := fuel')
              (work := finiteGPSNextEventState capacity weight work batchWork nextBatchDelay)
              (nextBatchDelay := nextBatchDelay -
                finiteGPSNextStepDuration capacity weight work nextBatchDelay)
              hnext_work_nonneg hresidual_nonneg hnext_card_lt_fuel hnext_card_lt_fuel'
            simp only [finiteGPSRunGap, if_neg hterminal]
            rw [htail]

end

end AppliedModelingLib.Probability.Queueing
