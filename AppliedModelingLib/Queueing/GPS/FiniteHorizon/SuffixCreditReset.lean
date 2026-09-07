import AppliedModelingLib.Queueing.GPS.FiniteHorizon.LateBatchLindleyTrace
import AppliedModelingLib.Queueing.GPS.FiniteHorizon.Reset
import Mathlib.Tactic

/-!
# Suffix-credit resets for finite GPS traces

This module proves a deterministic finite-trace reset criterion.  It uses
the literal chronological batches and a separate computational zero-work
horizon fence.  The hypothesis is a semantic suffix condition: every batch
and all later literal batches fit into the remaining aggregate capacity.
No batch is moved to the endpoint, and the fence is not an external event.

There is no stochastic, Palm, stationary, or source-process assertion here.
-/

namespace AppliedModelingLib.Probability.Queueing

open scoped BigOperators

noncomputable section

variable {Class : Type*} [Fintype Class] [DecidableEq Class]

/-- If every suffix of a finite increment sequence has nonpositive total,
then the empty-start reflected workload is zero at its terminal index. -/
theorem lindleyWorkload_eq_zero_of_all_suffix_sum_nonpos
    (increment : Nat → Real) (N : Nat)
    (hsuffix : ∀ n, n ≤ N →
      (Finset.Ico n N).sum increment ≤ 0) :
    lindleyWorkload increment N = 0 := by
  let potential : Nat → Real := fun n => (Finset.Ico n N).sum increment
  have hstep : ∀ n, n < N → potential n = increment n + potential (n + 1) := by
    intro n hn
    dsimp [potential]
    rw [← Finset.sum_Ico_consecutive increment (Nat.le_succ n) (Nat.succ_le_of_lt hn)]
    simp only [Nat.Ico_succ_singleton, Finset.sum_singleton]
  have hbound : ∀ n, n ≤ N → lindleyWorkload increment n ≤ - potential n := by
    intro n hn
    induction n with
    | zero =>
        change (0 : Real) ≤ - potential 0
        exact neg_nonneg.mpr (by simpa [potential] using hsuffix 0 (Nat.zero_le N))
    | succ n ih =>
        have hnle : n ≤ N := Nat.le_of_succ_le hn
        have hnlt : n < N := Nat.lt_of_succ_le hn
        have hpot_next_nonpos : potential (n + 1) ≤ 0 := by
          simpa [potential] using hsuffix (n + 1) hn
        have hinner : lindleyWorkload increment n + increment n ≤ - potential (n + 1) := by
          calc
            lindleyWorkload increment n + increment n ≤ - potential n + increment n :=
              by simpa [add_comm] using add_le_add_right (ih hnle) (increment n)
            _ = - potential (n + 1) := by
              rw [hstep n hnlt]
              ring
        calc
          lindleyWorkload increment (n + 1) =
              max 0 (lindleyWorkload increment n + increment n) := by rfl
          _ ≤ max 0 (- potential (n + 1)) := max_le_max_left _ hinner
          _ = - potential (n + 1) :=
            max_eq_right (neg_nonneg.mpr hpot_next_nonpos)
  have hle : lindleyWorkload increment N ≤ 0 := by
    simpa [potential] using hbound N (le_refl N)
  exact le_antisymm hle (lindleyWorkload_nonneg increment N)

/-- The actual finite GPS runner drains at its explicit terminal zero-work
fence when every chronological batch suffix fits into the remaining aggregate
capacity.  The suffix condition refers to the literal supplied batch order;
it is not a virtual endpoint-batch comparison. -/
theorem finiteGPSCloseAtHorizon_all_work_eq_zero_of_suffix_credit
    (capacity : Real) (weight initialWork : Class → Real)
    (batchWork : Real → Class → Real) (start horizon : Real) (times : List Real)
    (hcapacity : 0 < capacity) (hweight_pos : ∀ i, 0 < weight i)
    (htotal_weight_le_one : Finset.univ.sum weight ≤ 1)
    (hinit_nonneg : ∀ i, 0 ≤ initialWork i)
    (hchronological : FiniteGPSChronologicalFrom start times)
    (hstart_horizon : start ≤ horizon)
    (htimes_lt_horizon : ∀ t ∈ times, t < horizon)
    (hbatch_nonneg : ∀ t ∈ times, ∀ i, 0 ≤ batchWork t i)
    (hinitial_credit : finiteGPSAggregateWork initialWork +
      (times.map fun t => finiteGPSAggregateWork (batchWork t)).sum ≤
        capacity * (horizon - start))
    (hsuffix_credit : ∀ before t tail,
      times = before ++ t :: tail →
      finiteGPSAggregateWork (batchWork t) +
        (tail.map fun u => finiteGPSAggregateWork (batchWork u)).sum ≤
          capacity * (horizon - t)) :
    ∀ i, (finiteGPSCloseAtHorizon capacity weight
      (finiteGPSRunBatchTrace capacity weight batchWork start initialWork times)
      horizon).workload i = 0 := by
  induction times generalizing start initialWork with
  | nil =>
      simp only [List.map_nil, List.sum_nil, add_zero] at hinitial_credit
      have hrun_nonneg : ∀ i, 0 ≤
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork []).workload i := by
        simpa [finiteGPSRunBatchTrace] using hinit_nonneg
      have htime :
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork []).currentTime ≤ horizon := by
        simpa [finiteGPSRunBatchTrace] using hstart_horizon
      have hagg : finiteGPSAggregateWork
          (finiteGPSRunBatchTrace capacity weight batchWork start initialWork []).workload ≤
          capacity * (horizon -
            (finiteGPSRunBatchTrace capacity weight batchWork start initialWork []).currentTime) := by
        simpa [finiteGPSRunBatchTrace] using hinitial_credit
      exact (finiteGPSCloseAtHorizon_is_reset_of_aggregate_le_capacity_mul
        capacity weight
        (finiteGPSRunBatchTrace capacity weight batchWork start initialWork []) horizon
        hcapacity hweight_pos htotal_weight_le_one hrun_nonneg htime hagg).2
  | cons t tail ih =>
      rcases hchronological with ⟨hstart_t, hchronological_tail⟩
      have ht_horizon : t ≤ horizon := (htimes_lt_horizon t (by simp)).le
      have htail_lt_horizon : ∀ u ∈ tail, u < horizon := by
        intro u hu
        exact htimes_lt_horizon u (by simp [hu])
      have hbatch_head_nonneg : ∀ i, 0 ≤ batchWork t i := by
        intro i
        exact hbatch_nonneg t (by simp) i
      have hbatch_tail_nonneg : ∀ u ∈ tail, ∀ i, 0 ≤ batchWork u i := by
        intro u hu i
        exact hbatch_nonneg u (by simp [hu]) i
      let gap := finiteGPSRunGap ((finiteGPSActiveClasses initialWork).card + 1)
        capacity weight initialWork (batchWork t) (t - start)
      have hgap_nonneg : ∀ i, 0 ≤ gap.workload i := by
        intro i
        exact finiteGPSRunGap_workload_nonneg
          ((finiteGPSActiveClasses initialWork).card + 1) capacity weight initialWork
          (batchWork t) (t - start) hinit_nonneg hbatch_head_nonneg i
      have hgap_terminates : gap.batchApplied = true := by
        exact (finiteGPSRunGap_terminates_of_activeCard_lt
          ((finiteGPSActiveClasses initialWork).card + 1)
          hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
          (sub_nonneg.mpr hstart_t) (Nat.lt_succ_self _)).1
      have hhead_credit := hsuffix_credit [] t tail (by simp)
      have hgap_aggregate : finiteGPSAggregateWork gap.workload =
          max (finiteGPSAggregateWork initialWork - capacity * (t - start)) 0 +
            finiteGPSAggregateWork (batchWork t) := by
        simpa [gap] using
          (finiteGPSRunGap_aggregateWork_eq_max_sub_capacity_mul_add_batch
            capacity (weight := weight) (work := initialWork) (batchWork := batchWork t)
            (t - start) hcapacity hweight_pos htotal_weight_le_one hinit_nonneg
            (sub_nonneg.mpr hstart_t))
      have hpre_le : finiteGPSAggregateWork initialWork - capacity * (t - start) ≤
          capacity * (horizon - t) -
            finiteGPSAggregateWork (batchWork t) -
              (tail.map fun u => finiteGPSAggregateWork (batchWork u)).sum := by
        simp only [List.map_cons, List.sum_cons] at hinitial_credit
        linarith
      have hright_nonneg : 0 ≤ capacity * (horizon - t) -
          finiteGPSAggregateWork (batchWork t) -
            (tail.map fun u => finiteGPSAggregateWork (batchWork u)).sum := by
        linarith [hhead_credit]
      have hgap_credit : finiteGPSAggregateWork gap.workload +
          (tail.map fun u => finiteGPSAggregateWork (batchWork u)).sum ≤
            capacity * (horizon - t) := by
        rw [hgap_aggregate]
        have hmax_le : max (finiteGPSAggregateWork initialWork - capacity * (t - start)) 0 ≤
            capacity * (horizon - t) -
              finiteGPSAggregateWork (batchWork t) -
                (tail.map fun u => finiteGPSAggregateWork (batchWork u)).sum := by
          exact max_le hpre_le hright_nonneg
        linarith
      have hsuffix_credit_tail : ∀ before t' tail',
          tail = before ++ t' :: tail' →
          finiteGPSAggregateWork (batchWork t') +
            (tail'.map fun u => finiteGPSAggregateWork (batchWork u)).sum ≤
              capacity * (horizon - t') := by
        intro before t' tail' hsplit
        apply hsuffix_credit (t :: before) t' tail'
        simp [hsplit]
      have htail := ih (start := t) (initialWork := gap.workload)
        hgap_nonneg hchronological_tail ht_horizon htail_lt_horizon hbatch_tail_nonneg
        hgap_credit hsuffix_credit_tail
      rw [finiteGPSRunBatchTrace_cons_of_batchApplied capacity weight batchWork
        start initialWork t tail (by simpa [gap] using hgap_terminates)]
      simpa [gap] using htail

end

end AppliedModelingLib.Probability.Queueing
