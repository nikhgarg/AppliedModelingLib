import AppliedModelingLib.Queueing.GPS.FiniteHorizon.BatchTrace
import Mathlib.Tactic

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- Execute a finite prefix, then restart the same actual batch runner from
its computed state on a suffix. -/
def finiteGPSRunBatchTraceRestart
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (work : Class → ℝ) (leftTimes rightTimes : List ℝ) :
    FiniteGPSBatchTraceResult Class :=
  let prefixResult := finiteGPSRunBatchTrace capacity weight batchWork
    currentTime work leftTimes
  let suffixResult := finiteGPSRunBatchTrace capacity weight batchWork
    prefixResult.currentTime prefixResult.workload rightTimes
  { workload := suffixResult.workload
    currentTime := suffixResult.currentTime
    service := fun i => prefixResult.service i + suffixResult.service i }

/-- Under the ordinary finite GPS conditions, running a chronological
concatenated trace is exactly equivalent to restarting the actual runner from
the computed prefix state. -/
theorem finiteGPSRunBatchTrace_append_eq_restart
    (capacity : ℝ) (weight work : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (leftTimes rightTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hwork_nonneg : ∀ j, 0 ≤ work j)
    (hchronological : FiniteGPSChronologicalFrom currentTime (leftTimes ++ rightTimes))
    (hbatch_nonneg : ∀ t ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork t j) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime work (leftTimes ++ rightTimes) =
      finiteGPSRunBatchTraceRestart capacity weight batchWork
        currentTime work leftTimes rightTimes := by
  induction leftTimes generalizing currentTime work with
  | nil =>
      simp [finiteGPSRunBatchTraceRestart, finiteGPSRunBatchTrace]
  | cons t leftTimes ih =>
      change
        finiteGPSRunBatchTrace capacity weight batchWork currentTime work
            (t :: (leftTimes ++ rightTimes)) =
          finiteGPSRunBatchTraceRestart capacity weight batchWork
            currentTime work (t :: leftTimes) rightTimes
      rcases hchronological with ⟨hdelay, hchronological_tail⟩
      have hbatch_head : ∀ j, 0 ≤ batchWork t j := by
        intro j
        exact hbatch_nonneg t (by simp) j
      have hbatch_tail : ∀ u ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork u j := by
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
      have htail := ih (currentTime := t) (work := gap.workload)
        hgap_nonneg hchronological_tail hbatch_tail
      have hbatch_applied :
          (finiteGPSRunGap ((finiteGPSActiveClasses work).card + 1)
            capacity weight work (batchWork t) (t - currentTime)).batchApplied = true := by
        simpa [gap] using hgap_terminates.1
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        currentTime work t (leftTimes ++ rightTimes) hbatch_applied]
      simp only [finiteGPSRunBatchTraceRestart]
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        currentTime work t leftTimes hbatch_applied]
      rw [htail]
      rw [FiniteGPSBatchTraceResult.mk.injEq]
      constructor
      · rfl
      constructor
      · rfl
      · funext i
        simp [finiteGPSRunBatchTraceRestart, gap, add_assoc]

/-- The same restart law from an initially empty workload. -/
theorem finiteGPSRunBatchTrace_append_eq_restart_zero
    (capacity : ℝ) (weight : Class → ℝ) (batchWork : ℝ → Class → ℝ)
    (currentTime : ℝ) (leftTimes rightTimes : List ℝ)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ j, 0 < weight j)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hchronological : FiniteGPSChronologicalFrom currentTime (leftTimes ++ rightTimes))
    (hbatch_nonneg : ∀ t ∈ leftTimes ++ rightTimes, ∀ j, 0 ≤ batchWork t j) :
    finiteGPSRunBatchTrace capacity weight batchWork currentTime (fun _ => 0)
        (leftTimes ++ rightTimes) =
      finiteGPSRunBatchTraceRestart capacity weight batchWork
        currentTime (fun _ => 0) leftTimes rightTimes := by
  exact finiteGPSRunBatchTrace_append_eq_restart
    capacity weight (fun _ => 0) batchWork currentTime leftTimes rightTimes
    hcapacity hweight_pos htotal_weight_le_one (by intro j; norm_num)
    hchronological hbatch_nonneg

end

end AppliedModelingLib.Probability.Queueing
