import MendelsonWhang1990PriorityPricing.Definitions
import AppliedModelingLib.Queueing.NonpreemptivePriorityStationaryMeanWorkOccupation
import AppliedModelingLib.Foundations.Math.FiniteRanking
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Paper-Facing Theorems: Optimal Incentive-Compatible Priority Pricing for the M/M/1 Queue

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

During the statement-first phase, each exact paper-facing proposition lives in a
transparent `<name>Spec : Prop` declaration in `PaperInterface.lean`; the paired
theorem/lemma endpoint belongs in `ProofInterface.lean` and has exactly that
type. Add proof implementations here only after those specifications pass v11
raw-source-to-expanded-Spec review and recursive premise provenance audit. Before full closeout, the v11
realization audit independently binds pinned source atoms to the elaborated Spec
and accounts for the complete Lean closure; a proof hole or a declaration name
is never evidence for that correspondence.
-/

namespace MendelsonWhang1990PriorityPricing

noncomputable section

local instance classicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

open MeasureTheory ProbabilityTheory

open AppliedModelingLib.Queueing

/-- Residual work is invariant under a reindexing of finite priority
positions. -/
theorem finitePriorityResidualWork_comp_perm
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) :
    finitePriorityResidualWork (arrivalRate ∘ schedule) (meanService ∘ schedule) =
      finitePriorityResidualWork arrivalRate meanService := by
  unfold finitePriorityResidualWork
  calc
    ∑ j, (arrivalRate ∘ schedule) j * (meanService ∘ schedule) j ^ 2 =
        ∑ j, (fun customer => arrivalRate customer * meanService customer ^ 2) (schedule j) := by
          apply Finset.sum_congr rfl
          intro j _
          rfl
    _ = ∑ customer, arrivalRate customer * meanService customer ^ 2 := by
          simpa using (Equiv.sum_comp schedule
            (fun customer => arrivalRate customer * meanService customer ^ 2))

/-- A reindexing that preserves a strict priority prefix preserves its load. -/
theorem finitePriorityStrictLoad_comp_perm_eq_of_preserves_lt
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) (boundary : Fin n)
    (hpreserves : ∀ position, schedule position < boundary ↔ position < boundary) :
    finitePriorityStrictLoad (meanService ∘ schedule) (arrivalRate ∘ schedule) boundary =
      finitePriorityStrictLoad meanService arrivalRate boundary := by
  unfold finitePriorityStrictLoad
  calc
    ∑ j, (if j < boundary then
        (meanService ∘ schedule) j * (arrivalRate ∘ schedule) j else 0) =
      ∑ j, (fun position =>
        if position < boundary then meanService position * arrivalRate position else 0) (schedule j) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [Function.comp_apply]
          by_cases hj : j < boundary
          · simp [hj, (hpreserves j).mpr hj]
          · have hscheduled : ¬ schedule j < boundary :=
              fun h => hj ((hpreserves j).mp h)
            simp [hj, hscheduled]
    _ = ∑ j, (if j < boundary then meanService j * arrivalRate j else 0) := by
          simpa using (Equiv.sum_comp schedule
            (fun position => if position < boundary then
              meanService position * arrivalRate position else 0))

/-- A reindexing that preserves an inclusive priority prefix preserves its
load. -/
theorem finitePriorityInclusiveLoad_comp_perm_eq_of_preserves_le
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) (boundary : Fin n)
    (hpreserves : ∀ position, schedule position ≤ boundary ↔ position ≤ boundary) :
    finitePriorityInclusiveLoad (meanService ∘ schedule) (arrivalRate ∘ schedule) boundary =
      finitePriorityInclusiveLoad meanService arrivalRate boundary := by
  unfold finitePriorityInclusiveLoad
  calc
    ∑ j, (if j ≤ boundary then
        (meanService ∘ schedule) j * (arrivalRate ∘ schedule) j else 0) =
      ∑ j, (fun position =>
        if position ≤ boundary then meanService position * arrivalRate position else 0) (schedule j) := by
          apply Finset.sum_congr rfl
          intro j _
          simp only [Function.comp_apply]
          by_cases hj : j ≤ boundary
          · simp [hj, (hpreserves j).mpr hj]
          · have hscheduled : ¬ schedule j ≤ boundary :=
              fun h => hj ((hpreserves j).mp h)
            simp [hj, hscheduled]
    _ = ∑ j, (if j ≤ boundary then meanService j * arrivalRate j else 0) := by
          simpa using (Equiv.sum_comp schedule
            (fun position => if position ≤ boundary then
              meanService position * arrivalRate position else 0))

/-- Swapping a neighboring pair preserves every strict prefix ending at or
before its first position. -/
theorem swapAdjacent_preserves_lt_of_le
    {n : ℕ} (position boundary : Fin n) (hposition : position.val + 1 < n)
    (hboundary : boundary ≤ position) (index : Fin n) :
    (Equiv.swap position ⟨position.val + 1, hposition⟩) index < boundary ↔ index < boundary := by
  let successor : Fin n := ⟨position.val + 1, hposition⟩
  have hsuccessorVal : successor.val = position.val + 1 := rfl
  change (Equiv.swap position successor) index < boundary ↔ index < boundary
  by_cases hindex : index = position
  · subst index
    simp only [Equiv.swap_apply_left]
    change successor.val < boundary.val ↔ position.val < boundary.val
    omega
  · by_cases hsuccessor : index = successor
    · subst index
      simp only [Equiv.swap_apply_right]
      change position.val < boundary.val ↔ successor.val < boundary.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hindex hsuccessor]

/-- Swapping a neighboring pair preserves every inclusive prefix strictly
before its first position. -/
theorem swapAdjacent_preserves_le_of_lt
    {n : ℕ} (position boundary : Fin n) (hposition : position.val + 1 < n)
    (hboundary : boundary < position) (index : Fin n) :
    (Equiv.swap position ⟨position.val + 1, hposition⟩) index ≤ boundary ↔ index ≤ boundary := by
  let successor : Fin n := ⟨position.val + 1, hposition⟩
  have hsuccessorVal : successor.val = position.val + 1 := rfl
  change (Equiv.swap position successor) index ≤ boundary ↔ index ≤ boundary
  by_cases hindex : index = position
  · subst index
    simp only [Equiv.swap_apply_left]
    change successor.val ≤ boundary.val ↔ position.val ≤ boundary.val
    omega
  · by_cases hsuccessor : index = successor
    · subst index
      simp only [Equiv.swap_apply_right]
      change position.val ≤ boundary.val ↔ successor.val ≤ boundary.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hindex hsuccessor]

/-- Swapping a neighboring pair preserves every strict prefix strictly after
its second position. -/
theorem swapAdjacent_preserves_lt_of_successor_lt
    {n : ℕ} (position boundary : Fin n) (hposition : position.val + 1 < n)
    (hboundary : ⟨position.val + 1, hposition⟩ < boundary) (index : Fin n) :
    (Equiv.swap position ⟨position.val + 1, hposition⟩) index < boundary ↔ index < boundary := by
  let successor : Fin n := ⟨position.val + 1, hposition⟩
  have hsuccessorVal : successor.val = position.val + 1 := rfl
  change (Equiv.swap position successor) index < boundary ↔ index < boundary
  by_cases hindex : index = position
  · subst index
    simp only [Equiv.swap_apply_left]
    change successor.val < boundary.val ↔ position.val < boundary.val
    omega
  · by_cases hsuccessor : index = successor
    · subst index
      simp only [Equiv.swap_apply_right]
      change position.val < boundary.val ↔ successor.val < boundary.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hindex hsuccessor]

/-- Swapping a neighboring pair preserves every inclusive prefix ending at or
after its second position. -/
theorem swapAdjacent_preserves_le_of_successor_le
    {n : ℕ} (position boundary : Fin n) (hposition : position.val + 1 < n)
    (hboundary : ⟨position.val + 1, hposition⟩ ≤ boundary) (index : Fin n) :
    (Equiv.swap position ⟨position.val + 1, hposition⟩) index ≤ boundary ↔ index ≤ boundary := by
  let successor : Fin n := ⟨position.val + 1, hposition⟩
  have hsuccessorVal : successor.val = position.val + 1 := rfl
  change (Equiv.swap position successor) index ≤ boundary ↔ index ≤ boundary
  by_cases hindex : index = position
  · subst index
    simp only [Equiv.swap_apply_left]
    change successor.val ≤ boundary.val ↔ position.val ≤ boundary.val
    omega
  · by_cases hsuccessor : index = successor
    · subst index
      simp only [Equiv.swap_apply_right]
      change position.val ≤ boundary.val ↔ successor.val ≤ boundary.val
      omega
    · rw [Equiv.swap_apply_of_ne_of_ne hindex hsuccessor]

/-- A strictly inversion-sensitive tie breaker on finite priority
permutations.  It is used only to turn local adjacent-swap improvements into
the global finite scheduling comparison. -/
noncomputable def priorityPermutationPositionMeasure {n : ℕ}
    (schedule : Equiv.Perm (Fin n)) : ℝ :=
  ∑ position, (position.val : ℝ) * ((schedule position).val : ℝ)

/-- Swapping two positions changes the tie breaker by the product of their
position and class-label gaps. -/
theorem priorityPermutationPositionMeasure_swap
    {n : ℕ} (schedule : Equiv.Perm (Fin n)) (first second : Fin n)
    (hfirstsecond : first ≠ second) :
    priorityPermutationPositionMeasure ((Equiv.swap first second).trans schedule) =
      priorityPermutationPositionMeasure schedule +
        ((second.val : ℝ) - first.val) *
          ((schedule first).val - (schedule second).val) := by
  classical
  let f : Fin n → ℝ := fun position =>
    (position.val : ℝ) * (((Equiv.swap first second).trans schedule position).val : ℝ)
  let g : Fin n → ℝ := fun position =>
    (position.val : ℝ) * ((schedule position).val : ℝ)
  have hsecond_mem : second ∈ (Finset.univ : Finset (Fin n)).erase first := by
    simp [hfirstsecond.symm]
  have hrest :
      (∑ position ∈ ((Finset.univ : Finset (Fin n)).erase first).erase second,
          f position) =
        ∑ position ∈ ((Finset.univ : Finset (Fin n)).erase first).erase second,
          g position := by
    apply Finset.sum_congr rfl
    intro position hposition
    have hnesecond : position ≠ second := (Finset.mem_erase.mp hposition).1
    have hnefirst : position ≠ first :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hposition).2).1
    simp only [f, g, Equiv.trans_apply]
    rw [Equiv.swap_apply_of_ne_of_ne hnefirst hnesecond]
  change (∑ position, f position) = (∑ position, g position) + _
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) f (Finset.mem_univ first)]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase first) f hsecond_mem]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) g (Finset.mem_univ first)]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase first) g hsecond_mem]
  rw [hrest]
  simp only [f, g, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right]
  ring

/-- An adjacent-interchange inequality for every inverted neighboring pair
forces the identity priority order to minimize a real-valued objective over
all finite schedules.  The proof selects a minimizing schedule with maximal
position measure, so zero-flow swaps may be weak without losing the global
comparison. -/
theorem priorityPermutation_identity_min_of_adjacent_inversion
    {n : ℕ} (F : Equiv.Perm (Fin n) → ℝ)
    (hswap : ∀ (schedule : Equiv.Perm (Fin n)) (position : Fin n)
      (hposition : position.val + 1 < n),
        schedule ⟨position.val + 1, hposition⟩ < schedule position →
          F ((Equiv.swap position ⟨position.val + 1, hposition⟩).trans schedule) ≤
            F schedule) :
    ∀ schedule, F (Equiv.refl _) ≤ F schedule := by
  classical
  let minimizers : Finset (Equiv.Perm (Fin n)) :=
    Finset.univ.filter fun candidate => ∀ competitor, F candidate ≤ F competitor
  have hminimizers : minimizers.Nonempty := by
    obtain ⟨candidate, _hcandidate, hcandidate⟩ :=
      Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin n))) F (by simp)
    refine ⟨candidate, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro competitor
    exact hcandidate competitor (Finset.mem_univ _)
  obtain ⟨minimalSchedule, hminimalSchedule, hpositionMax⟩ :=
    Finset.exists_max_image minimizers priorityPermutationPositionMeasure hminimizers
  have hminimal : ∀ competitor, F minimalSchedule ≤ F competitor := by
    exact (Finset.mem_filter.mp hminimalSchedule).2
  have hminimal_refl : minimalSchedule = Equiv.refl _ := by
    by_contra hnotrefl
    have hnotmonotone : ¬ Monotone minimalSchedule := by
      intro hmonotone
      apply hnotrefl
      simpa using (Equiv.Perm.monotone_iff minimalSchedule).mp hmonotone
    simp only [Monotone] at hnotmonotone
    push Not at hnotmonotone
    obtain ⟨first, second, hfirstsecond, hreversed⟩ := hnotmonotone
    have hfirstne : first ≠ second := by
      intro heq
      subst second
      exact (lt_irrefl _) hreversed
    have hfirstsecondlt : first.val < second.val := by
      change first.val ≤ second.val at hfirstsecond
      apply lt_of_le_of_ne hfirstsecond
      intro hvalue
      exact hfirstne (Fin.ext hvalue)
    have hvalueReversed :
        ((minimalSchedule second).val : ℝ) ≤ (minimalSchedule first).val := by
      exact_mod_cast hreversed.le
    obtain ⟨position, hposition, hlocalInversion⟩ :=
      AppliedModelingLib.FiniteRanking.exists_adjacent_fin_inversion_of_any_inversion
        (fun index => ((minimalSchedule index).val : ℝ))
        ⟨first, second, hfirstsecondlt, hvalueReversed⟩
    let successor : Fin n := ⟨position.val + 1, hposition⟩
    have hsuccessor_ne : successor ≠ position := by
      intro heq
      have hvalue := congrArg Fin.val heq
      dsimp [successor] at hvalue
      omega
    have hlocalInversionFin : minimalSchedule successor ≤ minimalSchedule position := by
      exact_mod_cast hlocalInversion
    have hlocalStrict : minimalSchedule successor < minimalSchedule position :=
      lt_of_le_of_ne hlocalInversionFin (fun heq =>
        hsuccessor_ne (minimalSchedule.injective heq))
    let correctedSchedule : Equiv.Perm (Fin n) :=
      (Equiv.swap position successor).trans minimalSchedule
    have hcorrected_le : F correctedSchedule ≤ F minimalSchedule := by
      exact hswap minimalSchedule position hposition (by
        simpa [successor] using hlocalStrict)
    have hcorrected_eq : F correctedSchedule = F minimalSchedule :=
      le_antisymm hcorrected_le (hminimal correctedSchedule)
    have hcorrected_mem : correctedSchedule ∈ minimizers := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro competitor
      rw [hcorrected_eq]
      exact hminimal competitor
    have hpositionGap : 0 < ((successor.val : ℝ) - position.val) := by
      dsimp [successor]
      norm_num
    have hvalueGap : 0 < ((minimalSchedule position).val : ℝ) -
        (minimalSchedule successor).val := by
      exact sub_pos.mpr (by exact_mod_cast hlocalStrict)
    have hmeasureIncrease : priorityPermutationPositionMeasure minimalSchedule <
        priorityPermutationPositionMeasure correctedSchedule := by
      rw [priorityPermutationPositionMeasure_swap minimalSchedule position successor
        hsuccessor_ne.symm]
      nlinarith [mul_pos hpositionGap hvalueGap]
    exact (not_lt_of_ge (hpositionMax correctedSchedule hcorrected_mem)) hmeasureIncrease
  intro schedule
  simpa [hminimal_refl] using hminimal schedule

/-- The queue-delay comparison for swapping two adjacent classes.  It is the
algebraic cμ interchange step: if the higher displayed class has weakly larger
delay cost per mean service time, retaining it ahead weakly lowers total
queue-delay cost. -/
theorem adjacentPriorityQueueDelayCost_swap_le
    (residual slackBefore slackHere slackAfter swappedHere
      arrivalHere arrivalAfter meanServiceHere meanServiceAfter
      delayCostHere delayCostAfter : ℝ)
    (hresidual : 0 ≤ residual)
    (hslackBefore : 0 < slackBefore) (hslackHere : 0 < slackHere)
    (hslackAfter : 0 < slackAfter) (hswappedHere : 0 < swappedHere)
    (harrivalHere : 0 ≤ arrivalHere) (harrivalAfter : 0 ≤ arrivalAfter)
    (hpriority : meanServiceHere * delayCostAfter ≤
      meanServiceAfter * delayCostHere)
    (hhere : slackHere = slackBefore - meanServiceHere * arrivalHere)
    (hafter : slackAfter = slackHere - meanServiceAfter * arrivalAfter)
    (hswapped : swappedHere = slackBefore - meanServiceAfter * arrivalAfter) :
    delayCostHere * arrivalHere * residual / (slackBefore * slackHere) +
        delayCostAfter * arrivalAfter * residual / (slackHere * slackAfter) ≤
      delayCostAfter * arrivalAfter * residual / (slackBefore * swappedHere) +
        delayCostHere * arrivalHere * residual / (swappedHere * slackAfter) := by
  have hformula :
      (delayCostHere * arrivalHere * residual / (slackBefore * slackHere) +
          delayCostAfter * arrivalAfter * residual / (slackHere * slackAfter)) -
        (delayCostAfter * arrivalAfter * residual / (slackBefore * swappedHere) +
          delayCostHere * arrivalHere * residual / (swappedHere * slackAfter)) =
      residual * (slackBefore + slackAfter) * arrivalHere * arrivalAfter *
          (delayCostAfter * meanServiceHere - delayCostHere * meanServiceAfter) /
        (slackBefore * slackHere * swappedHere * slackAfter) := by
    field_simp [ne_of_gt hslackBefore, ne_of_gt hslackHere,
      ne_of_gt hslackAfter, ne_of_gt hswappedHere]
    rw [hafter, hswapped, hhere]
    ring
  have hnumerator :
      residual * (slackBefore + slackAfter) * arrivalHere * arrivalAfter *
        (delayCostAfter * meanServiceHere - delayCostHere * meanServiceAfter) ≤ 0 := by
    have hslackSum : 0 ≤ slackBefore + slackAfter :=
      add_nonneg hslackBefore.le hslackAfter.le
    have hgap : delayCostAfter * meanServiceHere - delayCostHere * meanServiceAfter ≤ 0 := by
      nlinarith [hpriority]
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (mul_nonneg hresidual hslackSum) harrivalHere) harrivalAfter)
      hgap
  have hdenominator : 0 < slackBefore * slackHere * swappedHere * slackAfter := by
    positivity
  have hnonpositive : residual * (slackBefore + slackAfter) * arrivalHere * arrivalAfter *
          (delayCostAfter * meanServiceHere - delayCostHere * meanServiceAfter) /
        (slackBefore * slackHere * swappedHere * slackAfter) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg hnumerator hdenominator.le
  linarith

/-- Correcting an adjacent inversion in a scheduled priority queue weakly
lowers its queue-delay cost whenever the source's `v/c` ordering holds. -/
theorem priorityScheduleQueueDelayCost_swapAdjacent_le
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (schedule : Equiv.Perm (Fin n)) (position : Fin n)
    (hposition : position.val + 1 < n)
    (hstable : arrivalRate ∈ stablePriorityFlowDomain meanService)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k ≤ meanService k * delayCost i)
    (hinversion : schedule ⟨position.val + 1, hposition⟩ < schedule position) :
    priorityScheduleQueueDelayCost arrivalRate delayCost meanService
        ((Equiv.swap position ⟨position.val + 1, hposition⟩).trans schedule) ≤
      priorityScheduleQueueDelayCost arrivalRate delayCost meanService schedule := by
  classical
  let successor : Fin n := ⟨position.val + 1, hposition⟩
  let swap : Equiv.Perm (Fin n) := Equiv.swap position successor
  let oldArrival : Fin n → ℝ := arrivalRate ∘ schedule
  let oldMean : Fin n → ℝ := meanService ∘ schedule
  let oldDelay : Fin n → ℝ := delayCost ∘ schedule
  let residual : ℝ := finitePriorityResidualWork oldArrival oldMean
  let oldTerm : Fin n → ℝ := fun index =>
    oldDelay index * oldArrival index * priorityQueueingTime oldArrival oldMean index
  let newTerm : Fin n → ℝ := fun index =>
    (oldDelay ∘ swap) index * (oldArrival ∘ swap) index *
      priorityQueueingTime (oldArrival ∘ swap) (oldMean ∘ swap) index
  have hsuccessor_ne : successor ≠ position := by
    intro heq
    have hvalue := congrArg Fin.val heq
    dsimp [successor] at hvalue
    omega
  have hposition_lt_successor : position < successor := by
    change position.val < position.val + 1
    omega
  have holdStable : oldArrival ∈ stablePriorityFlowDomain oldMean := by
    exact stablePriorityFlowDomain_comp_perm arrivalRate meanService schedule hstable
  have hnewStable : oldArrival ∘ swap ∈ stablePriorityFlowDomain (oldMean ∘ swap) := by
    exact stablePriorityFlowDomain_comp_perm oldArrival oldMean swap holdStable
  rcases holdStable with ⟨holdMeanPos, holdArrivalNonneg, holdTotalStable⟩
  rcases hnewStable with ⟨hnewMeanPos, hnewArrivalNonneg, hnewTotalStable⟩
  have holdLoadNonneg : ∀ index, 0 ≤ oldMean index * oldArrival index := fun index =>
    mul_nonneg (holdMeanPos index).le (holdArrivalNonneg index)
  have hnewLoadNonneg : ∀ index, 0 ≤ (oldMean ∘ swap) index * (oldArrival ∘ swap) index := fun index =>
    mul_nonneg (hnewMeanPos index).le (hnewArrivalNonneg index)
  have hresidualNonneg : 0 ≤ residual := by
    exact finitePriorityResidualWork_nonneg oldArrival oldMean holdArrivalNonneg
  have hresidualSwap :
      finitePriorityResidualWork (oldArrival ∘ swap) (oldMean ∘ swap) = residual := by
    simpa [residual] using finitePriorityResidualWork_comp_perm oldArrival oldMean swap
  have holdStrictPosition : 0 < finitePriorityStrictSlack oldMean oldArrival position := by
    have htotal : ∑ index, oldMean index * oldArrival index < 1 := by
      simpa [mul_comm] using holdTotalStable
    exact finitePriorityStrictSlack_pos_of_totalLoad_lt_one
      oldMean oldArrival holdLoadNonneg htotal position
  have holdInclusivePosition : 0 < finitePriorityInclusiveSlack oldMean oldArrival position := by
    have htotal : ∑ index, oldMean index * oldArrival index < 1 := by
      simpa [mul_comm] using holdTotalStable
    exact finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
      oldMean oldArrival holdLoadNonneg htotal position
  have holdInclusiveSuccessor : 0 < finitePriorityInclusiveSlack oldMean oldArrival successor := by
    have htotal : ∑ index, oldMean index * oldArrival index < 1 := by
      simpa [mul_comm] using holdTotalStable
    exact finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
      oldMean oldArrival holdLoadNonneg htotal successor
  have hnewInclusivePosition : 0 <
      finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) position := by
    have htotal : ∑ index, (oldMean ∘ swap) index * (oldArrival ∘ swap) index < 1 := by
      simpa [mul_comm] using hnewTotalStable
    exact finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
      (oldMean ∘ swap) (oldArrival ∘ swap) hnewLoadNonneg htotal position
  have hstrictPosition :
      finitePriorityStrictSlack (oldMean ∘ swap) (oldArrival ∘ swap) position =
        finitePriorityStrictSlack oldMean oldArrival position := by
    unfold finitePriorityStrictSlack
    rw [finitePriorityStrictLoad_comp_perm_eq_of_preserves_lt oldArrival oldMean swap position]
    intro index
    exact swapAdjacent_preserves_lt_of_le position position hposition le_rfl index
  have hnewInclusiveSuccessor :
      finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) successor =
        finitePriorityInclusiveSlack oldMean oldArrival successor := by
    unfold finitePriorityInclusiveSlack
    rw [finitePriorityInclusiveLoad_comp_perm_eq_of_preserves_le oldArrival oldMean swap successor]
    intro index
    simpa [swap, successor] using
      (swapAdjacent_preserves_le_of_successor_le position successor hposition le_rfl index)
  have holdStrictSuccessor :
      finitePriorityStrictSlack oldMean oldArrival successor =
        finitePriorityInclusiveSlack oldMean oldArrival position := by
    exact finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
      oldMean oldArrival hposition_lt_successor (by
        intro index hleft hright
        change position.val < index.val at hleft
        change index.val < position.val + 1 at hright
        omega)
  have hnewStrictSuccessor :
      finitePriorityStrictSlack (oldMean ∘ swap) (oldArrival ∘ swap) successor =
        finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) position := by
    exact finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
      (oldMean ∘ swap) (oldArrival ∘ swap) hposition_lt_successor (by
        intro index hleft hright
        change position.val < index.val at hleft
        change index.val < position.val + 1 at hright
        omega)
  have hnewInclusivePositionFormula :
      finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) position =
        finitePriorityStrictSlack oldMean oldArrival position -
          oldMean successor * oldArrival successor := by
    have hdecompose := finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
      (oldMean ∘ swap) (oldArrival ∘ swap) position
    have hmeanSwap : (oldMean ∘ swap) position = oldMean successor := by
      simp [swap]
    have harrivalSwap : (oldArrival ∘ swap) position = oldArrival successor := by
      simp [swap]
    rw [hstrictPosition, hmeanSwap, harrivalSwap] at hdecompose
    linarith
  have holdInclusivePositionFormula :
      finitePriorityInclusiveSlack oldMean oldArrival position =
        finitePriorityStrictSlack oldMean oldArrival position -
          oldMean position * oldArrival position := by
    have hdecompose := finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
      oldMean oldArrival position
    linarith
  have holdInclusiveSuccessorFormula :
      finitePriorityInclusiveSlack oldMean oldArrival successor =
        finitePriorityInclusiveSlack oldMean oldArrival position -
          oldMean successor * oldArrival successor := by
    have hdecompose := finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
      oldMean oldArrival successor
    rw [holdStrictSuccessor] at hdecompose
    linarith
  have hafterNewFormula :
      finitePriorityInclusiveSlack oldMean oldArrival successor =
        finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) position -
          oldMean position * oldArrival position := by
    linarith [hnewInclusivePositionFormula, holdInclusivePositionFormula,
      holdInclusiveSuccessorFormula]
  have hpriorityLocal : oldMean successor * oldDelay position ≤
      oldMean position * oldDelay successor := by
    exact hpriority (by simpa [oldMean, oldDelay] using hinversion)
  have hpair : newTerm position + newTerm successor ≤
      oldTerm position + oldTerm successor := by
    unfold newTerm oldTerm priorityQueueingTime
    simp only [Function.comp_apply, swap, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    unfold finiteNonpreemptivePriorityQueueWait
    rw [hresidualSwap, hstrictPosition, hnewStrictSuccessor,
      hnewInclusiveSuccessor, holdStrictSuccessor]
    have hscalar := adjacentPriorityQueueDelayCost_swap_le residual
      (finitePriorityStrictSlack oldMean oldArrival position)
      (finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) position)
      (finitePriorityInclusiveSlack oldMean oldArrival successor)
      (finitePriorityInclusiveSlack oldMean oldArrival position)
      (oldArrival successor) (oldArrival position)
      (oldMean successor) (oldMean position)
      (oldDelay successor) (oldDelay position)
      hresidualNonneg holdStrictPosition hnewInclusivePosition holdInclusiveSuccessor
      holdInclusivePosition (holdArrivalNonneg successor) (holdArrivalNonneg position)
      hpriorityLocal hnewInclusivePositionFormula hafterNewFormula
      holdInclusivePositionFormula
    dsimp [residual] at hscalar
    convert hscalar using 1 <;> ring
  have hrest :
      (∑ index ∈ ((Finset.univ : Finset (Fin n)).erase position).erase successor,
          newTerm index) =
        ∑ index ∈ ((Finset.univ : Finset (Fin n)).erase position).erase successor,
          oldTerm index := by
    apply Finset.sum_congr rfl
    intro index hindex
    have hneSuccessor : index ≠ successor := (Finset.mem_erase.mp hindex).1
    have hnePosition : index ≠ position :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hindex).2).1
    have houtside : index < position ∨ successor < index := by
      by_cases hbefore : index < position
      · exact Or.inl hbefore
      · right
        have hpositionLe : position ≤ index := le_of_not_gt hbefore
        have hpositionLt : position < index := lt_of_le_of_ne hpositionLe (Ne.symm hnePosition)
        have hsuccessorLe : successor ≤ index := by
          change position.val + 1 ≤ index.val
          omega
        exact lt_of_le_of_ne hsuccessorLe (Ne.symm hneSuccessor)
    have hswapIndex : swap index = index := by
      exact Equiv.swap_apply_of_ne_of_ne hnePosition hneSuccessor
    have hstrict :
        finitePriorityStrictSlack (oldMean ∘ swap) (oldArrival ∘ swap) index =
          finitePriorityStrictSlack oldMean oldArrival index := by
      unfold finitePriorityStrictSlack
      rw [finitePriorityStrictLoad_comp_perm_eq_of_preserves_lt oldArrival oldMean swap index]
      intro k
      rcases houtside with hbefore | hafter
      · simpa [swap, successor] using
          (swapAdjacent_preserves_lt_of_le position index hposition hbefore.le k)
      · simpa [swap, successor] using
          (swapAdjacent_preserves_lt_of_successor_lt position index hposition hafter k)
    have hinclusive :
        finitePriorityInclusiveSlack (oldMean ∘ swap) (oldArrival ∘ swap) index =
          finitePriorityInclusiveSlack oldMean oldArrival index := by
      unfold finitePriorityInclusiveSlack
      rw [finitePriorityInclusiveLoad_comp_perm_eq_of_preserves_le oldArrival oldMean swap index]
      intro k
      rcases houtside with hbefore | hafter
      · simpa [swap, successor] using
          (swapAdjacent_preserves_le_of_lt position index hposition hbefore k)
      · simpa [swap, successor] using
          (swapAdjacent_preserves_le_of_successor_le position index hposition hafter.le k)
    unfold newTerm oldTerm priorityQueueingTime
    simp only [Function.comp_apply, hswapIndex]
    unfold finiteNonpreemptivePriorityQueueWait
    rw [hresidualSwap, hstrict, hinclusive]
  change (∑ index, newTerm index) ≤ ∑ index, oldTerm index
  have hsuccessor_mem : successor ∈ (Finset.univ : Finset (Fin n)).erase position := by
    simp [hsuccessor_ne]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) newTerm
    (Finset.mem_univ position)]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase position) newTerm
    hsuccessor_mem]
  rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n)) oldTerm
    (Finset.mem_univ position)]
  rw [← Finset.add_sum_erase ((Finset.univ : Finset (Fin n)).erase position) oldTerm
    hsuccessor_mem]
  rw [hrest]
  linarith

/-- Under the source's weak `v/c` ordering, the displayed priority order
minimizes queue-delay cost among every finite nonpreemptive priority schedule. -/
theorem priorityScheduleQueueDelayCost_refl_le
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (hstable : arrivalRate ∈ stablePriorityFlowDomain meanService)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k ≤ meanService k * delayCost i)
    (schedule : Equiv.Perm (Fin n)) :
    priorityScheduleQueueDelayCost arrivalRate delayCost meanService (Equiv.refl _) ≤
      priorityScheduleQueueDelayCost arrivalRate delayCost meanService schedule := by
  apply priorityPermutation_identity_min_of_adjacent_inversion
    (fun schedule => priorityScheduleQueueDelayCost arrivalRate delayCost meanService schedule)
  intro candidate position hposition hinversion
  exact priorityScheduleQueueDelayCost_swapAdjacent_le
    arrivalRate delayCost meanService candidate position hposition hstable hpriority hinversion

/-- The `v/c` order maximizes source net value jointly over priority schedules
when the arrival vector is held fixed. -/
theorem priorityScheduleNetValue_le_refl
    {n : ℕ} (value : Fin n → ℝ → ℝ) (arrivalRate delayCost meanService : Fin n → ℝ)
    (hstable : arrivalRate ∈ stablePriorityFlowDomain meanService)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k ≤ meanService k * delayCost i)
    (schedule : Equiv.Perm (Fin n)) :
    priorityScheduleNetValue value arrivalRate delayCost meanService schedule ≤
      priorityScheduleNetValue value arrivalRate delayCost meanService (Equiv.refl _) := by
  unfold priorityScheduleNetValue
  rw [priorityScheduleDelayCost_eq_queueDelayCost_add_service,
    priorityScheduleDelayCost_eq_queueDelayCost_add_service]
  have hqueue := priorityScheduleQueueDelayCost_refl_le
    arrivalRate delayCost meanService hstable hpriority schedule
  linarith

/-- A fixed-order welfare maximizer is also a joint maximizer over stable
arrival vectors and all finite nonpreemptive priority schedules when the
displayed order satisfies the source's `v/c` condition. -/
theorem priorityScheduleNetValue_refl_isMaxOn
    {n : ℕ} (value : Fin n → ℝ → ℝ)
    (arrivalRate delayCost meanService : Fin n → ℝ)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k ≤ meanService k * delayCost i)
    (hmax : IsMaxOn
      (fun flow => netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) flow)
      (stablePriorityFlowDomain meanService) arrivalRate) :
    IsMaxOn
      (fun pair : (Fin n → ℝ) × Equiv.Perm (Fin n) =>
        priorityScheduleNetValue value pair.1 delayCost meanService pair.2)
      (Set.prod (stablePriorityFlowDomain meanService) Set.univ)
      (arrivalRate, Equiv.refl _) := by
  rw [isMaxOn_iff]
  intro pair hpair
  rcases hpair with ⟨hstable, _⟩
  calc
    priorityScheduleNetValue value pair.1 delayCost meanService pair.2 ≤
        priorityScheduleNetValue value pair.1 delayCost meanService (Equiv.refl _) :=
      priorityScheduleNetValue_le_refl value pair.1 delayCost meanService
        hstable hpriority pair.2
    _ = netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) pair.1 :=
      priorityScheduleNetValue_refl value pair.1 delayCost meanService
    _ ≤ netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) arrivalRate :=
      (isMaxOn_iff.mp hmax) pair.1 hstable
    _ = priorityScheduleNetValue value arrivalRate delayCost meanService (Equiv.refl _) :=
      (priorityScheduleNetValue_refl value arrivalRate delayCost meanService).symm

/-- The literal stationary marked-Poisson priority queue realizes the
Appendix (A-1) queueing-time expression under the source's positive-rate,
positive-mean, and strict-load assumptions. -/
theorem stationaryPriorityClassTaggedExpectedQueueWait_eq_priorityQueueingTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    (∫ z, AppliedModelingLib.Queueing.stationaryPriorityClassTaggedQueueWait meanService i z ∂
      AppliedModelingLib.Queueing.stationaryPriorityClassTaggedPalmMeasure arrivalRate harrivalRate i) =
      priorityQueueingTime arrivalRate meanService i := by
  simpa only [priorityQueueingTime] using
    (AppliedModelingLib.Queueing.integral_stationaryPriorityClassTaggedQueueWait_eq_finiteNonpreemptivePriorityQueueWait
      arrivalRate meanService harrivalRate hmeanService hstable i)

/-- The literal tagged response in the stationary priority queue realizes the
Appendix (A-1) mean time in system.  The library supplies the response-minus-
service identity and the queue-wait formula supplies its closed form. -/
theorem stationaryPriorityClassTaggedExpectedResponse_eq_prioritySojournTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ k, 0 < arrivalRate k)
    (hmeanService : ∀ k, 0 < meanService k)
    (hstable : ∑ k, arrivalRate k * meanService k < 1)
    (i : Fin n) :
    (∫ z, AppliedModelingLib.Queueing.stationaryPriorityClassTaggedResponseTime
        meanService i z ∂
      AppliedModelingLib.Queueing.stationaryPriorityClassTaggedPalmMeasure
        arrivalRate harrivalRate i) =
      prioritySojournTime arrivalRate meanService i := by
  have hresponse :=
    AppliedModelingLib.Queueing.integrable_stationaryPriorityClassTaggedResponseTime_of_totalStable
      arrivalRate meanService harrivalRate hmeanService hstable i
  have hwait :=
    AppliedModelingLib.Queueing.integral_stationaryPriorityClassTaggedQueueWait_of_response
      arrivalRate meanService harrivalRate hmeanService i hresponse
  have hformula :=
    stationaryPriorityClassTaggedExpectedQueueWait_eq_priorityQueueingTime
      arrivalRate meanService harrivalRate hmeanService hstable i
  change (∫ z, AppliedModelingLib.Queueing.stationaryPriorityClassTaggedQueueWait
      meanService i z ∂
    (AppliedModelingLib.Probability.Palm.targetPassiveTaggedArrivalAtZero
      (AppliedModelingLib.Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate i))
      (AppliedModelingLib.Queueing.multiclassStationaryPoissonWorkRestLaw
        arrivalRate harrivalRate i)).Ptag) =
      priorityQueueingTime arrivalRate meanService i at hformula
  rw [hformula] at hwait
  rw [prioritySojournTime_eq_queueingTime_add_service]
  change (∫ z, AppliedModelingLib.Queueing.stationaryPriorityClassTaggedResponseTime
      meanService i z ∂
    (AppliedModelingLib.Probability.Palm.targetPassiveTaggedArrivalAtZero
      (AppliedModelingLib.Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate i))
      (AppliedModelingLib.Queueing.multiclassStationaryPoissonWorkRestLaw
        arrivalRate harrivalRate i)).Ptag) =
      priorityQueueingTime arrivalRate meanService i + meanService i
  linarith

/--
Theorem 1's first-order pricing identity.  A local optimum along the selected
flow coordinate yields the zero derivative used in the printed proof.  The
bridge from the paper's constrained global program to this interior condition
is developed separately with the queue model.
-/
theorem theoremOneExternalityPricing_impl
    {Class : Type*} [Fintype Class]
    (value : Class → ℝ → ℝ) (delayCost : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (flow : Class → ℝ) (i : Class) (marginalValue : ℝ)
    (partialWaiting : Class → ℝ)
    (hvalue : HasDerivAt (value i) marginalValue (flow i))
    (hwaiting : ∀ j,
      HasDerivAt
        (fun t => waitingTime j (Function.update flow i t))
        (partialWaiting j) (flow i))
    (hmax : IsLocalMax
      (fun t => netValue value delayCost waitingTime
        (Function.update flow i t))
      (flow i)) :
    marginalValue =
      delayCost i * waitingTime i flow +
        externalityPrice delayCost flow partialWaiting := by
  classical
  exact AppliedModelingLib.marginalValue_eq_privateDelay_add_externality_of_isLocalMax
    value delayCost waitingTime flow i marginalValue partialWaiting
    hvalue hwaiting hmax

/-- Theorem 1's marginal-externality identity specialized to the finite
nonpreemptive-priority M/M/1 performance expression used later in the paper.
The source's queueing formula is an explicit differentiable map, and the
stationary marked-Poisson realization of that map is established above. -/
theorem priorityQueueFirstOrderPricing_impl
    {n : ℕ} (value : Fin n → ℝ → ℝ) (delayCost : Fin n → ℝ)
    (arrivalRate meanService : Fin n → ℝ) (i : Fin n) (marginalValue : ℝ)
    (hvalue : HasDerivAt (value i) marginalValue (arrivalRate i))
    (hslack : ∀ k,
      AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k ≠ 0 ∧
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k ≠ 0)
    (hmax : IsLocalMax
      (fun t => netValue value delayCost
        (fun k flow => prioritySojournTime flow meanService k)
        (Function.update arrivalRate i t))
      (arrivalRate i)) :
    marginalValue =
      delayCost i * prioritySojournTime arrivalRate meanService i +
        externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
  apply AppliedModelingLib.marginalValue_eq_privateDelay_add_externality_of_isLocalMax
    value delayCost
      (fun k flow => prioritySojournTime flow meanService k)
      arrivalRate i marginalValue
      (prioritySojournDerivative arrivalRate meanService i)
      hvalue
  · intro k
    exact AppliedModelingLib.Queueing.hasDerivAt_finiteNonpreemptivePrioritySojournTime_update
      arrivalRate meanService i k (hslack k).1 (hslack k).2
  · exact hmax

/-- The global nonnegative-flow program yields Theorem 1's coordinatewise
first-order identity at a strictly positive class flow.  Strict positivity is
the interior-solution condition needed to turn a constrained maximum into an
ordinary local maximum along that coordinate. -/
theorem priorityQueueFirstOrderPricing_of_globalMax
    {n : ℕ} (value : Fin n → ℝ → ℝ) (delayCost : Fin n → ℝ)
    (arrivalRate meanService : Fin n → ℝ) (i : Fin n) (marginalValue : ℝ)
    (harrival : ∀ j, 0 ≤ arrivalRate j)
    (harrival_i : 0 < arrivalRate i)
    (hvalue : HasDerivAt (value i) marginalValue (arrivalRate i))
    (hslack : ∀ k,
      AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k ≠ 0 ∧
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k ≠ 0)
    (hmax : IsMaxOn
      (fun flow => netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) flow)
      (Set.Ici (fun _ => 0)) arrivalRate) :
    marginalValue =
      delayCost i * prioritySojournTime arrivalRate meanService i +
        externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
  apply priorityQueueFirstOrderPricing_impl value delayCost arrivalRate meanService i
    marginalValue hvalue hslack
  have hcoordinateMax : IsMaxOn
      (fun t => netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k)
        (Function.update arrivalRate i t))
      (Set.Ici 0) (arrivalRate i) := by
    rw [isMaxOn_iff]
    intro t ht
    have hupdate : Function.update arrivalRate i t ∈
        Set.Ici (fun _ : Fin n => 0) := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa using ht
      · simpa [hji, Function.update_of_ne hji] using harrival j
    rw [isMaxOn_iff] at hmax
    simpa using hmax (Function.update arrivalRate i t) hupdate
  exact hcoordinateMax.isLocalMax (Ici_mem_nhds harrival_i)

/-- The source stationary welfare program's first-order pricing identity.
Its maximum is taken only over nonnegative flows with total offered work below
one, the domain on which the Appendix (A-1) sojourn-time expression is a
stationary queue quantity.  At a positive, strictly stable flow, a small
one-coordinate perturbation stays in that domain, so the constrained maximum
still supplies the ordinary local maximum used by the derivative argument. -/
theorem priorityQueueFirstOrderPricing_of_globalMax_of_totalStable
    {n : ℕ} (value : Fin n → ℝ → ℝ) (delayCost : Fin n → ℝ)
    (arrivalRate meanService : Fin n → ℝ) (i : Fin n) (marginalValue : ℝ)
    (harrival : ∀ j, 0 ≤ arrivalRate j)
    (hmeanService : ∀ j, 0 < meanService j)
    (htotalStable : ∑ j, arrivalRate j * meanService j < 1)
    (harrival_i : 0 < arrivalRate i)
    (hvalue : HasDerivAt (value i) marginalValue (arrivalRate i))
    (hmax : IsMaxOn
      (fun flow => netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) flow)
      (stablePriorityFlowDomain meanService) arrivalRate) :
    marginalValue =
      delayCost i * prioritySojournTime arrivalRate meanService i +
        externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
  apply priorityQueueFirstOrderPricing_impl value delayCost arrivalRate
    meanService i marginalValue hvalue
  · intro k
    have hload_nonneg : ∀ j, 0 ≤ meanService j * arrivalRate j := fun j =>
      mul_nonneg (hmeanService j).le (harrival j)
    have htotal : ∑ j, meanService j * arrivalRate j < 1 := by
      simpa [mul_comm] using htotalStable
    constructor
    · exact ne_of_gt
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack_pos_of_totalLoad_lt_one
          meanService arrivalRate hload_nonneg htotal k)
    · exact ne_of_gt
        (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
          meanService arrivalRate hload_nonneg htotal k)
  · let upper : ℝ :=
      arrivalRate i + (1 - ∑ j, arrivalRate j * meanService j) / meanService i
    have hupper : arrivalRate i < upper := by
      dsimp [upper]
      have hgap : 0 < 1 - ∑ j, arrivalRate j * meanService j := by
        linarith
      have hquotient : 0 <
          (1 - ∑ j, arrivalRate j * meanService j) / meanService i :=
        div_pos hgap (hmeanService i)
      linarith
    have hcoordinateMax : IsMaxOn
        (fun t => netValue value delayCost
          (fun k rates => prioritySojournTime rates meanService k)
          (Function.update arrivalRate i t))
        (Set.Ioo 0 upper) (arrivalRate i) := by
      rw [isMaxOn_iff]
      intro t ht
      have hupdate_mem : Function.update arrivalRate i t ∈
          stablePriorityFlowDomain meanService := by
        constructor
        · exact hmeanService
        · constructor
          · intro j
            by_cases hji : j = i
            · subst j
              simpa using ht.1.le
            · simpa [Function.update_of_ne hji] using harrival j
          · have hupdate :
                (fun j => Function.update arrivalRate i t j * meanService j) =
                  Function.update (fun j => arrivalRate j * meanService j) i
                    (t * meanService i) := by
                funext j
                by_cases hji : j = i
                · subst j
                  simp
                · simp [Function.update_of_ne hji]
            have hsum_update :
                ∑ j, Function.update arrivalRate i t j * meanService j =
                  t * meanService i +
                    ∑ j ∈ (Finset.univ : Finset (Fin n)) \ {i},
                      arrivalRate j * meanService j := by
              rw [hupdate, Finset.sum_update_of_mem (Finset.mem_univ i)]
            have hsum_arrival :
                ∑ j, arrivalRate j * meanService j =
                  arrivalRate i * meanService i +
                    ∑ j ∈ (Finset.univ : Finset (Fin n)) \ {i},
                      arrivalRate j * meanService j := by
              rw [← Finset.add_sum_erase (Finset.univ : Finset (Fin n))
                (fun j => arrivalRate j * meanService j) (Finset.mem_univ i)]
              simp [Finset.sdiff_singleton_eq_erase]
            have htload : t * meanService i < upper * meanService i :=
              (mul_lt_mul_of_pos_right ht.2 (hmeanService i))
            have hupper_eq : upper * meanService i =
                arrivalRate i * meanService i +
                  (1 - ∑ j, arrivalRate j * meanService j) := by
              dsimp [upper]
              field_simp [ne_of_gt (hmeanService i)]
            rw [hsum_update]
            rw [hupper_eq] at htload
            rw [hsum_arrival] at htotalStable
            linarith
      simpa using hmax hupdate_mem
    exact hcoordinateMax.isLocalMax (Ioo_mem_nhds harrival_i hupper)

/-- The closed-form expected PTD charge in Equations (19)--(21) is the
marginal delay-externality price in Theorem 1.  This is the algebraic
optimality calculation for the heterogeneous-service schedule; the separate
stationary-performance bridge identifies the queueing-time expression with
the M/M/1 model. -/
theorem heterogeneousPriority_expectedPrice_eq_externalityPrice
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) (i : Fin n)
    (hslack : ∀ j,
      AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ≠ 0 ∧
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j ≠ 0) :
    priorityTimeLinearCoefficient arrivalRate delayCost meanService i * meanService i +
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
        meanService i ^ 2 =
      externalityPrice delayCost arrivalRate
        (prioritySojournDerivative arrivalRate meanService i) := by
  classical
  let residual : ℝ :=
    AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService
  let strictSlack : Fin n → ℝ := fun j =>
    AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j
  let inclusiveSlack : Fin n → ℝ := fun j =>
    AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j
  let weight : Fin n → ℝ := fun j => delayCost j * arrivalRate j
  let base : Fin n → ℝ := fun j =>
    weight j / (strictSlack j * inclusiveSlack j)
  let selfTerm : ℝ :=
    weight i * residual / (strictSlack i * inclusiveSlack i ^ 2)
  let suffixTerm : Fin n → ℝ := fun j =>
    (1 / (strictSlack j ^ 2 * inclusiveSlack j) +
      1 / (strictSlack j * inclusiveSlack j ^ 2)) * weight j * residual
  let extraTerm : Fin n → ℝ := fun j =>
    if j = i then selfTerm else if i < j then suffixTerm j else 0
  have hlinear :
      priorityTimeLinearCoefficient arrivalRate delayCost meanService i =
        selfTerm + ∑ j, if i < j then suffixTerm j else 0 := by
    unfold priorityTimeLinearCoefficient priorityLinearNumerator
    dsimp [selfTerm, suffixTerm, weight, residual, strictSlack, inclusiveSlack]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp [hij]
      ring
    · simp [hij]
  have hquadratic :
      priorityTimeQuadraticCoefficient arrivalRate delayCost meanService = ∑ j, base j := by
    unfold priorityTimeQuadraticCoefficient
    apply Finset.sum_congr rfl
    intro j _
    dsimp [base, weight, strictSlack, inclusiveSlack]
  have hsumExtra :
      ∑ j, extraTerm j = selfTerm + ∑ j, if i < j then suffixTerm j else 0 := by
    calc
      ∑ j, extraTerm j =
          ∑ j, ((if j = i then selfTerm else 0) +
            if i < j then suffixTerm j else 0) := by
              apply Finset.sum_congr rfl
              intro j _
              by_cases hji : j = i
              · subst j
                simp [extraTerm]
              · simp [extraTerm, hji]
      _ = selfTerm + ∑ j, if i < j then suffixTerm j else 0 := by
        rw [Finset.sum_add_distrib]
        simp
  have hpoint : ∀ j,
      weight j * prioritySojournDerivative arrivalRate meanService i j =
        meanService i ^ 2 * base j + meanService i * extraTerm j := by
    intro j
    rcases hslack j with ⟨hstrict, hinclusive⟩
    by_cases hji : j = i
    · subst j
      dsimp [weight, base, extraTerm, selfTerm, residual, strictSlack, inclusiveSlack]
      simp [prioritySojournDerivative]
      field_simp
    · by_cases hij : i < j
      · dsimp [weight, base, extraTerm, suffixTerm, residual, strictSlack,
          inclusiveSlack]
        simp [prioritySojournDerivative, hji, hij, hij.le]
        field_simp
        ring
      · have hji' : j < i := lt_of_le_of_ne (le_of_not_gt hij) hji
        dsimp [weight, base, extraTerm, strictSlack, inclusiveSlack]
        simp [prioritySojournDerivative, hji, hij, not_le_of_gt hji']
        field_simp
  calc
    priorityTimeLinearCoefficient arrivalRate delayCost meanService i * meanService i +
        priorityTimeQuadraticCoefficient arrivalRate delayCost meanService *
          meanService i ^ 2 =
        meanService i * (selfTerm + ∑ j, if i < j then suffixTerm j else 0) +
          meanService i ^ 2 * ∑ j, base j := by
          rw [hlinear, hquadratic]
          ring
    _ = ∑ j, (meanService i ^ 2 * base j + meanService i * extraTerm j) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hsumExtra]
          ring
    _ = ∑ j, weight j * prioritySojournDerivative arrivalRate meanService i j := by
          apply Finset.sum_congr rfl
          intro j _
          exact (hpoint j).symm
    _ = externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i) := by
          rfl

/-- Under the exponential service law in Assumption A4, the expected PTD
charge is exactly the Theorem 1 marginal externality price. -/
theorem heterogeneousPriorityTimeDependentPrice_expMeasure_eq_externalityPrice
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 < meanService i) (i : Fin n)
    (hslack : ∀ j,
      AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ≠ 0 ∧
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j ≠ 0) :
    ∫ t, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService i t
      ∂ProbabilityTheory.expMeasure (meanService i)⁻¹ =
      externalityPrice delayCost arrivalRate
        (prioritySojournDerivative arrivalRate meanService i) := by
  rw [integral_heterogeneousPriorityTimeDependentPrice_expMeasure
    arrivalRate delayCost meanService hmeanService i i]
  exact heterogeneousPriority_expectedPrice_eq_externalityPrice
    arrivalRate delayCost meanService i hslack

/-- The stationary marked-Poisson input construction realizes the expected
PTD charge as the marginal externality price for every tagged service mark. -/
theorem heterogeneousPriorityTimeDependentPrice_stationaryWorkRequirement_eq_externalityPrice
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 < arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (i : Fin n) (eventIndex : ℤ)
    (hslack : ∀ j,
      AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ≠ 0 ∧
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j ≠ 0) :
    ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService i
        (AppliedModelingLib.Queueing.stationaryPriorityWorkRequirement meanService i omega eventIndex)
      ∂AppliedModelingLib.Probability.PoissonProcess.multiclassStationaryPoissonWorkMeasure
        arrivalRate =
      externalityPrice delayCost arrivalRate
        (prioritySojournDerivative arrivalRate meanService i) := by
  rw [integral_heterogeneousPriorityTimeDependentPrice_stationaryWorkRequirement
    arrivalRate delayCost meanService harrivalRate hmeanService i eventIndex]
  exact heterogeneousPriority_expectedPrice_eq_externalityPrice
    arrivalRate delayCost meanService i hslack

/-- The adjacent difference of Equation (10)'s prices is the one boundary
term used in the corrected local-optimality argument for Theorem 2. -/
theorem homogeneousPriorityPrice_sub_of_adjacent
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    homogeneousPriorityPrice arrivalRate delayCost i -
      homogeneousPriorityPrice arrivalRate delayCost k =
      (arrivalRate i * delayCost i * homogeneousPriorityQueueingTime arrivalRate i +
        prioritySuccessorOrZero
          (fun j => arrivalRate j * delayCost j *
            homogeneousPriorityQueueingTime arrivalRate j) i) /
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i := by
  let common : ℝ :=
    ∑ j,
      arrivalRate j * delayCost j /
        (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j *
          AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j)
  let suffixTerm : Fin n → ℝ := fun j =>
    (arrivalRate j * delayCost j * homogeneousPriorityQueueingTime arrivalRate j +
      prioritySuccessorOrZero
        (fun l => arrivalRate l * delayCost l *
          homogeneousPriorityQueueingTime arrivalRate l) j) /
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j
  change
    (common + ∑ j, if i ≤ j then suffixTerm j else 0) -
      (common + ∑ j, if k ≤ j then suffixTerm j else 0) = suffixTerm i
  rw [add_sub_add_left_eq_sub]
  exact AppliedModelingLib.Queueing.sum_prioritySuffix_sub_of_adjacent
    suffixTerm hik hnoIntermediate

/-- The preceding adjacent price difference with the source's padded terminal
index resolved to the actual next class. -/
theorem homogeneousPriorityPrice_sub_of_adjacent_explicit
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    homogeneousPriorityPrice arrivalRate delayCost i -
      homogeneousPriorityPrice arrivalRate delayCost k =
      (arrivalRate i * delayCost i * homogeneousPriorityQueueingTime arrivalRate i +
        arrivalRate k * delayCost k * homogeneousPriorityQueueingTime arrivalRate k) /
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i := by
  rw [homogeneousPriorityPrice_sub_of_adjacent arrivalRate delayCost hik hnoIntermediate,
    prioritySuccessorOrZero_eq_of_adjacent _ hik hnoIntermediate]

/-- The adjacent difference of Equation (21)'s linear PTD coefficients.  The
finite strict-suffix cancellation makes the two boundary terms explicit. -/
theorem priorityTimeLinearCoefficient_sub_of_adjacent
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    priorityTimeLinearCoefficient arrivalRate delayCost meanService i -
      priorityTimeLinearCoefficient arrivalRate delayCost meanService k =
      priorityLinearNumerator arrivalRate delayCost meanService i /
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i ^ 2) +
      priorityLinearNumerator arrivalRate delayCost meanService k /
        (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i ^ 2 *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k) := by
  let selfTerm : Fin n → ℝ := fun j =>
    priorityLinearNumerator arrivalRate delayCost meanService j /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j ^ 2)
  let suffixTerm : Fin n → ℝ := fun j =>
    (1 / (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ^ 2 *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j) +
      1 / (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j ^ 2)) *
      priorityLinearNumerator arrivalRate delayCost meanService j
  change (selfTerm i + ∑ j, if i < j then suffixTerm j else 0) -
      (selfTerm k + ∑ j, if k < j then suffixTerm j else 0) = _
  have hsum := AppliedModelingLib.Queueing.sum_priorityStrictSuffix_sub_of_adjacent
    suffixTerm hik hnoIntermediate
  have hslack : AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k =
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i := by
    exact AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
      meanService arrivalRate hik hnoIntermediate
  calc
    (selfTerm i + ∑ j, if i < j then suffixTerm j else 0) -
        (selfTerm k + ∑ j, if k < j then suffixTerm j else 0) =
        selfTerm i + (suffixTerm k - selfTerm k) := by
          linarith
    _ = _ := by
      dsimp [selfTerm, suffixTerm]
      rw [hslack]
      ring

/-- The adjacent PTD cheating penalty factors into the residual-work term,
the neighboring flow, and the delay-cost-per-service ordering gap.  This is
the local calculation used in Theorem 3's incentive-compatibility proof. -/
theorem heterogeneousPriority_adjacentCheatingPenalty
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) {i k : Fin n}
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      meanService arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k =
      AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService *
        arrivalRate k *
          (meanService k * delayCost i - meanService i * delayCost k) /
        (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i ^ 2 *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k) := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k
  have hbefore : strictI = inclusiveI + meanService i * arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        meanService arrivalRate i
  have hstrictK : AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k =
      inclusiveI := by
    simpa [inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
        meanService arrivalRate hik hnoIntermediate
  have hafter' : inclusiveI = inclusiveK + meanService k * arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          meanService arrivalRate k := hstrictK.symm
      _ = inclusiveK + meanService k * arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                meanService arrivalRate k
  have hlinear := priorityTimeLinearCoefficient_sub_of_adjacent
    arrivalRate delayCost meanService hik hnoIntermediate
  have hlinear' :
      priorityTimeLinearCoefficient arrivalRate delayCost meanService i -
        priorityTimeLinearCoefficient arrivalRate delayCost meanService k =
      delayCost i * arrivalRate i * residual / (strictI * inclusiveI ^ 2) +
        delayCost k * arrivalRate k * residual / (inclusiveI ^ 2 * inclusiveK) := by
    simpa [priorityLinearNumerator, residual, strictI, inclusiveI, inclusiveK] using hlinear
  have hqueueI : priorityQueueingTime arrivalRate meanService i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : priorityQueueingTime arrivalRate meanService k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k) = _
    rw [hstrictK]
  unfold priorityCheatingPenalty
  rw [show priorityTimeLinearCoefficient arrivalRate delayCost meanService k -
      priorityTimeLinearCoefficient arrivalRate delayCost meanService i =
      -(priorityTimeLinearCoefficient arrivalRate delayCost meanService i -
        priorityTimeLinearCoefficient arrivalRate delayCost meanService k) by ring,
    hlinear', hqueueI, hqueueK]
  change meanService i *
      (-(delayCost i * arrivalRate i * residual / (strictI * inclusiveI ^ 2) +
        delayCost k * arrivalRate k * residual / (inclusiveI ^ 2 * inclusiveK))) +
      delayCost i * (residual / (inclusiveI * inclusiveK) -
        residual / (strictI * inclusiveI)) =
      residual * arrivalRate k *
        (meanService k * delayCost i - meanService i * delayCost k) /
        (inclusiveI ^ 2 * inclusiveK)
  have hstrictIpos : 0 < strictI := by
    simpa [strictI] using hstrict
  have hinclusiveIpos : 0 < inclusiveI := by
    simpa [inclusiveI] using hinclusive
  have hinclusiveKpos : 0 < inclusiveK := by
    simpa [inclusiveK] using hafter
  field_simp [ne_of_gt hstrictIpos, ne_of_gt hinclusiveIpos, ne_of_gt hinclusiveKpos]
  rw [hbefore, hafter']
  ring

/-- Under the strict `v/c` ordering and positive neighboring flow, moving one
priority level downward has a strictly positive expected-cost penalty. -/
theorem heterogeneousPriority_adjacentCheatingPenalty_pos
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) {i k : Fin n}
    (hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService)
    (harrival : 0 < arrivalRate k)
    (hpriority : meanService i * delayCost k < meanService k * delayCost i)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      meanService arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k := by
  rw [heterogeneousPriority_adjacentCheatingPenalty arrivalRate delayCost meanService
    hstrict hinclusive hafter hik hnoIntermediate]
  apply div_pos
  · exact mul_pos (mul_pos hresidual harrival) (sub_pos.mpr hpriority)
  · exact mul_pos (pow_pos hinclusive 2) hafter

/-- The corresponding adjacent penalty for a lower-priority class which
declares the immediately higher priority. -/
theorem heterogeneousPriority_adjacentCheatingPenalty_reverse
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) {i k : Fin n}
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      meanService arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) k i =
      AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService *
        arrivalRate i *
          (meanService k * delayCost i - meanService i * delayCost k) /
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i *
          AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i ^ 2) := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k
  have hbefore : strictI = inclusiveI + meanService i * arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        meanService arrivalRate i
  have hstrictK : AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k =
      inclusiveI := by
    simpa [inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
        meanService arrivalRate hik hnoIntermediate
  have hafter' : inclusiveI = inclusiveK + meanService k * arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          meanService arrivalRate k := hstrictK.symm
      _ = inclusiveK + meanService k * arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                meanService arrivalRate k
  have hlinear := priorityTimeLinearCoefficient_sub_of_adjacent
    arrivalRate delayCost meanService hik hnoIntermediate
  have hlinear' :
      priorityTimeLinearCoefficient arrivalRate delayCost meanService i -
        priorityTimeLinearCoefficient arrivalRate delayCost meanService k =
      delayCost i * arrivalRate i * residual / (strictI * inclusiveI ^ 2) +
        delayCost k * arrivalRate k * residual / (inclusiveI ^ 2 * inclusiveK) := by
    simpa [priorityLinearNumerator, residual, strictI, inclusiveI, inclusiveK] using hlinear
  have hqueueI : priorityQueueingTime arrivalRate meanService i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : priorityQueueingTime arrivalRate meanService k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k) = _
    rw [hstrictK]
  unfold priorityCheatingPenalty
  rw [hlinear', hqueueI, hqueueK]
  change meanService k *
      (delayCost i * arrivalRate i * residual / (strictI * inclusiveI ^ 2) +
        delayCost k * arrivalRate k * residual / (inclusiveI ^ 2 * inclusiveK)) +
      delayCost k * (residual / (strictI * inclusiveI) -
        residual / (inclusiveI * inclusiveK)) =
      residual * arrivalRate i *
        (meanService k * delayCost i - meanService i * delayCost k) /
        (strictI * inclusiveI ^ 2)
  have hstrictIpos : 0 < strictI := by
    simpa [strictI] using hstrict
  have hinclusiveIpos : 0 < inclusiveI := by
    simpa [inclusiveI] using hinclusive
  have hinclusiveKpos : 0 < inclusiveK := by
    simpa [inclusiveK] using hafter
  field_simp [ne_of_gt hstrictIpos, ne_of_gt hinclusiveIpos, ne_of_gt hinclusiveKpos]
  rw [hbefore, hafter']
  ring

/-- Under the strict `v/c` ordering and positive neighboring flow, moving one
priority level upward has a strictly positive expected-cost penalty. -/
theorem heterogeneousPriority_adjacentCheatingPenalty_reverse_pos
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ) {i k : Fin n}
    (hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService)
    (harrival : 0 < arrivalRate i)
    (hpriority : meanService i * delayCost k < meanService k * delayCost i)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      meanService arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) k i := by
  rw [heterogeneousPriority_adjacentCheatingPenalty_reverse arrivalRate delayCost meanService
    hstrict hinclusive hafter hik hnoIntermediate]
  apply div_pos
  · exact mul_pos (mul_pos hresidual harrival) (sub_pos.mpr hpriority)
  · exact mul_pos hstrict (pow_pos hinclusive 2)

/-- Algebraic one-step comparison of a fixed customer's penalties at two
adjacent declared priority levels, expressed through the middle type's local
penalty. -/
theorem priorityCheatingPenalty_step_downward
    {n : ℕ} (meanService delayCost queueingTime linearCoefficient : Fin n → ℝ)
    (i j k : Fin n) :
    meanService j *
        (priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k -
          priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j) =
      meanService i *
          priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient j k +
        (meanService j * delayCost i - meanService i * delayCost j) *
          (queueingTime k - queueingTime j) := by
  unfold priorityCheatingPenalty
  ring

/-- If a type has a strictly higher delay-cost-per-service ratio than a
middle type, its penalty strictly grows when the declared priority moves one
level below that middle type. -/
theorem priorityCheatingPenalty_step_downward_pos
    {n : ℕ} (meanService delayCost queueingTime linearCoefficient : Fin n → ℝ)
    (i j k : Fin n)
    (hcustomer : 0 < meanService i) (hmiddle : 0 < meanService j)
    (hlocal : 0 < priorityCheatingPenalty meanService delayCost
      queueingTime linearCoefficient j k)
    (hwaiting : 0 < queueingTime k - queueingTime j)
    (hratio : meanService i * delayCost j < meanService j * delayCost i) :
    priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j <
      priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k := by
  have hpositive : 0 < meanService j *
      (priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k -
        priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j) := by
    rw [priorityCheatingPenalty_step_downward]
    exact add_pos (mul_pos hcustomer hlocal)
      (mul_pos (sub_pos.mpr hratio) hwaiting)
  nlinarith [hmiddle]

/-- The symmetric one-step comparison when a type has a lower
delay-cost-per-service ratio than the lower-priority neighboring type. -/
theorem priorityCheatingPenalty_step_upward
    {n : ℕ} (meanService delayCost queueingTime linearCoefficient : Fin n → ℝ)
    (i j k : Fin n) :
    meanService k *
        (priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j -
          priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k) =
      meanService i *
          priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient k j +
        (meanService i * delayCost k - meanService k * delayCost i) *
          (queueingTime k - queueingTime j) := by
  unfold priorityCheatingPenalty
  ring

/-- A lower-ratio type's penalty strictly grows when the declared priority
moves one level above a lower-ratio neighboring type. -/
theorem priorityCheatingPenalty_step_upward_pos
    {n : ℕ} (meanService delayCost queueingTime linearCoefficient : Fin n → ℝ)
    (i j k : Fin n)
    (hcustomer : 0 < meanService i) (hmiddle : 0 < meanService k)
    (hlocal : 0 < priorityCheatingPenalty meanService delayCost
      queueingTime linearCoefficient k j)
    (hwaiting : 0 < queueingTime k - queueingTime j)
    (hratio : meanService k * delayCost i < meanService i * delayCost k) :
    priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k <
      priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j := by
  have hpositive : 0 < meanService k *
      (priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i j -
        priorityCheatingPenalty meanService delayCost queueingTime linearCoefficient i k) := by
    rw [priorityCheatingPenalty_step_upward]
    exact add_pos (mul_pos hcustomer hlocal)
      (mul_pos (sub_pos.mpr hratio) hwaiting)
  nlinarith [hmiddle]

/-- With positive residual work, service means, and adjacent flows, moving to
the immediately lower priority strictly increases queueing time. -/
theorem priorityQueueingTime_lt_of_adjacent
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) {i k : Fin n}
    (hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService)
    (hmeanI : 0 < meanService i) (hmeanK : 0 < meanService k)
    (harrivalI : 0 < arrivalRate i) (harrivalK : 0 < arrivalRate k)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      meanService arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      meanService arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    priorityQueueingTime arrivalRate meanService i <
      priorityQueueingTime arrivalRate meanService k := by
  have hbefore : AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i =
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i +
        meanService i * arrivalRate i := by
    exact AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
      meanService arrivalRate i
  have hstrictK : AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k =
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i := by
    exact AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
      meanService arrivalRate hik hnoIntermediate
  have hafter' : AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i =
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k +
        meanService k * arrivalRate k := by
    calc
      AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i =
          AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k := hstrictK.symm
      _ = AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k +
          meanService k * arrivalRate k :=
        AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
          meanService arrivalRate k
  have hwait := AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentQueueWait_lt
    (AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService)
    (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i)
    (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i)
    (AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k)
    (meanService i * arrivalRate i) (meanService k * arrivalRate k)
    hresidual hstrict hinclusive hafter
    (mul_pos hmeanI harrivalI) (mul_pos hmeanK harrivalK) hbefore hafter'
  change AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate i *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate i) <
    AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate k)
  rw [hstrictK]
  exact hwait

/-- The forward half of the heterogeneous-service incentive argument: under
strict `v/c` ordering, every lower declared priority has a positive cheating
penalty for its assigned class. -/
theorem heterogeneousPriority_assignedCheatingPenalty_pos_of_lt
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ j, 0 < arrivalRate j)
    (hmean : ∀ j, 0 < meanService j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k < meanService k * delayCost i)
    (i k : Fin n) (hik : i < k) :
    0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k := by
  let penalty : Fin n → ℝ := fun declaredPriority =>
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i declaredPriority
  have hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService := by
    exact AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists
      arrivalRate meanService (fun j => (harrival j).le) hmean
      ⟨i, harrival i⟩
  let P : (m : ℕ) → i.1 + 1 ≤ m → Prop := fun m _ =>
    ∀ hmn : m < n, 0 < penalty ⟨m, hmn⟩
  have hstart : i.1 + 1 ≤ k.1 := by
    change i.1 < k.1 at hik
    omega
  have hforward : P k.1 hstart := by
    refine Nat.le_induction (P := P) ?_ ?_ k.1 hstart
    · intro hbound
      let l : Fin n := ⟨i.1 + 1, hbound⟩
      have hil : i < l := by
        change i.1 < i.1 + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, i < a → a < l → False := by
        intro a hia hal
        change i.1 < a.1 at hia
        change a.1 < i.1 + 1 at hal
        omega
      have hlocal := heterogeneousPriority_adjacentCheatingPenalty_pos
        arrivalRate delayCost meanService hresidual (harrival l) (hpriority hil)
        (hslack i).1 (hslack i).2 (hslack l).2 hil hnoIntermediate
      simpa [penalty, l] using hlocal
    · intro m him hIH hbound
      have hboundPrev : m < n := by omega
      let j : Fin n := ⟨m, hboundPrev⟩
      let l : Fin n := ⟨m + 1, hbound⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hij : i < j := by
        change i.1 < m
        omega
      have hfirst : 0 < penalty j := by
        simpa [j] using hIH hboundPrev
      have hlocal : 0 < priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) j l := by
        exact heterogeneousPriority_adjacentCheatingPenalty_pos
          arrivalRate delayCost meanService hresidual (harrival l) (hpriority hjl)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have hwaiting : 0 < priorityQueueingTime arrivalRate meanService l -
          priorityQueueingTime arrivalRate meanService j := by
        exact sub_pos.mpr (priorityQueueingTime_lt_of_adjacent arrivalRate meanService
          hresidual (hmean j) (hmean l) (harrival j) (harrival l)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate)
      have hstep : penalty j < penalty l := by
        simpa [penalty] using priorityCheatingPenalty_step_downward_pos
          meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j l
          (hmean i) (hmean j) hlocal hwaiting (hpriority hij)
      exact hfirst.trans hstep
  simpa [penalty] using hforward k.2

/-- The reverse half of the heterogeneous-service incentive argument: under
strict `v/c` ordering, every higher declared priority has a positive cheating
penalty for its assigned class. -/
theorem heterogeneousPriority_assignedCheatingPenalty_pos_of_gt
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ j, 0 < arrivalRate j)
    (hmean : ∀ j, 0 < meanService j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k < meanService k * delayCost i)
    (i k : Fin n) (hki : k < i) :
    0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k := by
  let penalty : Fin n → ℝ := fun declaredPriority =>
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i declaredPriority
  have hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService := by
    exact AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists
      arrivalRate meanService (fun j => (harrival j).le) hmean ⟨i, harrival i⟩
  have hiPositive : 0 < i.1 := by
    change k.1 < i.1 at hki
    omega
  let P : (m : ℕ) → m ≤ i.1 - 1 → Prop := fun m _ =>
    ∀ hmn : m < n, 0 < penalty ⟨m, hmn⟩
  have htarget : k.1 ≤ i.1 - 1 := by
    change k.1 < i.1 at hki
    omega
  have hbackward : P k.1 htarget := by
    refine Nat.decreasingInduction (motive := P) (n := i.1 - 1) (m := k.1) ?_ ?_ htarget
    · intro m hm hIH hbound
      have hboundNext : m + 1 < n := by omega
      let j : Fin n := ⟨m, hbound⟩
      let l : Fin n := ⟨m + 1, hboundNext⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hli : l < i := by
        change m + 1 < i.1
        omega
      have hfirst : 0 < penalty l := by
        simpa [l] using hIH hboundNext
      have hlocal : 0 < priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) l j := by
        exact heterogeneousPriority_adjacentCheatingPenalty_reverse_pos
          arrivalRate delayCost meanService hresidual (harrival j) (hpriority hjl)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have hwaiting : 0 < priorityQueueingTime arrivalRate meanService l -
          priorityQueueingTime arrivalRate meanService j := by
        exact sub_pos.mpr (priorityQueueingTime_lt_of_adjacent arrivalRate meanService
          hresidual (hmean j) (hmean l) (harrival j) (harrival l)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate)
      have hstep : penalty l < penalty j := by
        simpa [penalty] using priorityCheatingPenalty_step_upward_pos
          meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j l
          (hmean i) (hmean l) hlocal hwaiting (hpriority hli)
      exact hfirst.trans hstep
    · intro hbound
      have htopBound : i.1 - 1 < n := by omega
      let j : Fin n := ⟨i.1 - 1, htopBound⟩
      have hji : j < i := by
        change i.1 - 1 < i.1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < i → False := by
        intro a hja hai
        change i.1 - 1 < a.1 at hja
        change a.1 < i.1 at hai
        omega
      have hlocal := heterogeneousPriority_adjacentCheatingPenalty_reverse_pos
        arrivalRate delayCost meanService hresidual (harrival j) (hpriority hji)
        (hslack j).1 (hslack j).2 (hslack i).2 hji hnoIntermediate
      simpa [penalty, j] using hlocal
  simpa [penalty] using hbackward k.2

/-- The strict incentive conclusion for the heterogeneous-service PTD
schedule: any misreported finite priority yields a positive expected-cost
increment.  The stationary queueing and optimizer bridges are supplied
separately. -/
theorem heterogeneousPriority_incentiveCompatible_strict
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ j, 0 < arrivalRate j)
    (hmean : ∀ j, 0 < meanService j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate j)
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k < meanService k * delayCost i)
    (i selectedPriority : Fin n) (hmisreport : selectedPriority ≠ i) :
    0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i selectedPriority := by
  rcases lt_or_gt_of_ne (Ne.symm hmisreport) with hilower | hihigher
  · exact heterogeneousPriority_assignedCheatingPenalty_pos_of_lt
      arrivalRate delayCost meanService harrival hmean hslack hpriority i selectedPriority hilower
  · exact heterogeneousPriority_assignedCheatingPenalty_pos_of_gt
      arrivalRate delayCost meanService harrival hmean hslack hpriority i selectedPriority hihigher

/-- A penalty increases at every adjacent step farther below the assigned
priority.  This is the local form of Theorem 4's lower-priority chain. -/
theorem heterogeneousPriority_cheatingPenalty_step_below
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ q, 0 < arrivalRate q)
    (hmean : ∀ q, 0 < meanService q)
    (hslack : ∀ q,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate q ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate q)
    (hpriority : ∀ {a b : Fin n}, a < b →
      meanService a * delayCost b < meanService b * delayCost a)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hnoIntermediate : ∀ a : Fin n, j < a → a < k → False) :
    priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j <
      priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k := by
  have hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService := by
    exact AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists
      arrivalRate meanService (fun q => (harrival q).le) hmean ⟨j, harrival j⟩
  have hlocal : 0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) j k := by
    exact heterogeneousPriority_adjacentCheatingPenalty_pos
      arrivalRate delayCost meanService hresidual (harrival k) (hpriority hjk)
      (hslack j).1 (hslack j).2 (hslack k).2 hjk hnoIntermediate
  have hwaiting : 0 < priorityQueueingTime arrivalRate meanService k -
      priorityQueueingTime arrivalRate meanService j := by
    exact sub_pos.mpr (priorityQueueingTime_lt_of_adjacent arrivalRate meanService
      hresidual (hmean j) (hmean k) (harrival j) (harrival k)
      (hslack j).1 (hslack j).2 (hslack k).2 hjk hnoIntermediate)
  exact priorityCheatingPenalty_step_downward_pos meanService delayCost
    (priorityQueueingTime arrivalRate meanService)
    (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j k
    (hmean i) (hmean j) hlocal hwaiting (hpriority hij)

/-- A penalty increases at every adjacent step farther above the assigned
priority.  This is the local form of Theorem 4's higher-priority chain. -/
theorem heterogeneousPriority_cheatingPenalty_step_above
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ q, 0 < arrivalRate q)
    (hmean : ∀ q, 0 < meanService q)
    (hslack : ∀ q,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate q ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate q)
    (hpriority : ∀ {a b : Fin n}, a < b →
      meanService a * delayCost b < meanService b * delayCost a)
    {i j k : Fin n} (hki : k < i) (hjk : j < k)
    (hnoIntermediate : ∀ a : Fin n, j < a → a < k → False) :
    priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k <
      priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j := by
  have hresidual : 0 < AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate meanService := by
    exact AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists
      arrivalRate meanService (fun q => (harrival q).le) hmean ⟨k, harrival k⟩
  have hlocal : 0 < priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) k j := by
    exact heterogeneousPriority_adjacentCheatingPenalty_reverse_pos
      arrivalRate delayCost meanService hresidual (harrival j) (hpriority hjk)
      (hslack j).1 (hslack j).2 (hslack k).2 hjk hnoIntermediate
  have hwaiting : 0 < priorityQueueingTime arrivalRate meanService k -
      priorityQueueingTime arrivalRate meanService j := by
    exact sub_pos.mpr (priorityQueueingTime_lt_of_adjacent arrivalRate meanService
      hresidual (hmean j) (hmean k) (harrival j) (harrival k)
      (hslack j).1 (hslack j).2 (hslack k).2 hjk hnoIntermediate)
  exact priorityCheatingPenalty_step_upward_pos meanService delayCost
    (priorityQueueingTime arrivalRate meanService)
    (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j k
    (hmean i) (hmean k) hlocal hwaiting (hpriority hki)

/-- Below the assigned priority, the cheating penalty strictly increases with
the distance from that priority. -/
theorem heterogeneousPriority_cheatingPenalty_strictMono_below
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ q, 0 < arrivalRate q)
    (hmean : ∀ q, 0 < meanService q)
    (hslack : ∀ q,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate q ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate q)
    (hpriority : ∀ {a b : Fin n}, a < b →
      meanService a * delayCost b < meanService b * delayCost a)
    {i j k : Fin n} (hij : i < j) (hjk : j < k) :
    priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j <
      priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k := by
  let penalty : Fin n → ℝ := fun declaredPriority =>
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i declaredPriority
  let P : (m : ℕ) → j.1 + 1 ≤ m → Prop := fun m _ =>
    ∀ hmn : m < n, penalty j < penalty ⟨m, hmn⟩
  have hstart : j.1 + 1 ≤ k.1 := by
    change j.1 < k.1 at hjk
    omega
  have hforward : P k.1 hstart := by
    refine Nat.le_induction (P := P) ?_ ?_ k.1 hstart
    · intro hbound
      let l : Fin n := ⟨j.1 + 1, hbound⟩
      have hjl : j < l := by
        change j.1 < j.1 + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change j.1 < a.1 at hja
        change a.1 < j.1 + 1 at hal
        omega
      have hlocal := heterogeneousPriority_cheatingPenalty_step_below
        arrivalRate delayCost meanService harrival hmean hslack hpriority hij hjl hnoIntermediate
      simpa [penalty, l] using hlocal
    · intro m hm hIH hbound
      have hboundPrev : m < n := by omega
      let q : Fin n := ⟨m, hboundPrev⟩
      let l : Fin n := ⟨m + 1, hbound⟩
      have hql : q < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, q < a → a < l → False := by
        intro a hqa hal
        change m < a.1 at hqa
        change a.1 < m + 1 at hal
        omega
      have hiq : i < q := by
        change i.1 < m
        change i.1 < j.1 at hij
        omega
      have hfirst : penalty j < penalty q := by
        simpa [q] using hIH hboundPrev
      have hstep : penalty q < penalty l := by
        simpa [penalty] using heterogeneousPriority_cheatingPenalty_step_below
          arrivalRate delayCost meanService harrival hmean hslack hpriority hiq hql hnoIntermediate
      exact hfirst.trans hstep
  simpa [penalty] using hforward k.2

/-- Above the assigned priority, the cheating penalty strictly increases with
the distance from that priority. -/
theorem heterogeneousPriority_cheatingPenalty_strictMono_above
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrival : ∀ q, 0 < arrivalRate q)
    (hmean : ∀ q, 0 < meanService q)
    (hslack : ∀ q,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack meanService arrivalRate q ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack meanService arrivalRate q)
    (hpriority : ∀ {a b : Fin n}, a < b →
      meanService a * delayCost b < meanService b * delayCost a)
    {i j k : Fin n} (hki : k < i) (hjk : j < k) :
    priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k <
      priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j := by
  let penalty : Fin n → ℝ := fun declaredPriority =>
    priorityCheatingPenalty meanService delayCost
      (priorityQueueingTime arrivalRate meanService)
      (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i declaredPriority
  have hkPositive : 0 < k.1 := by
    change j.1 < k.1 at hjk
    omega
  let P : (m : ℕ) → m ≤ k.1 - 1 → Prop := fun m _ =>
    ∀ hmn : m < n, penalty k < penalty ⟨m, hmn⟩
  have htarget : j.1 ≤ k.1 - 1 := by
    change j.1 < k.1 at hjk
    omega
  have hbackward : P j.1 htarget := by
    refine Nat.decreasingInduction (motive := P) (n := k.1 - 1) (m := j.1) ?_ ?_ htarget
    · intro m hm hIH hbound
      have hboundNext : m + 1 < n := by omega
      let q : Fin n := ⟨m, hbound⟩
      let l : Fin n := ⟨m + 1, hboundNext⟩
      have hql : q < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, q < a → a < l → False := by
        intro a hqa hal
        change m < a.1 at hqa
        change a.1 < m + 1 at hal
        omega
      have hli : l < i := by
        change m + 1 < i.1
        change k.1 < i.1 at hki
        omega
      have hfirst : penalty k < penalty l := by
        simpa [l] using hIH hboundNext
      have hstep : penalty l < penalty q := by
        simpa [penalty] using heterogeneousPriority_cheatingPenalty_step_above
          arrivalRate delayCost meanService harrival hmean hslack hpriority hli hql hnoIntermediate
      exact hfirst.trans hstep
    · intro hbound
      have htopBound : k.1 - 1 < n := by omega
      let q : Fin n := ⟨k.1 - 1, htopBound⟩
      have hqk : q < k := by
        change k.1 - 1 < k.1
        omega
      have hnoIntermediate : ∀ a : Fin n, q < a → a < k → False := by
        intro a hqa hak
        change k.1 - 1 < a.1 at hqa
        change a.1 < k.1 at hak
        omega
      have hlocal := heterogeneousPriority_cheatingPenalty_step_above
        arrivalRate delayCost meanService harrival hmean hslack hpriority hki hqk hnoIntermediate
      simpa [penalty, q] using hlocal
  simpa [penalty] using hbackward j.2

/-- The weak adjacent local-optimality comparison behind Theorem 2.  It is
valid at zero-flow boundaries, where the source's displayed strict comparison
can become an equality. -/
theorem homogeneousPriority_adjacentCost_le
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False)
    (hdelayCost : delayCost k ≤ delayCost i) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i ≤
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate (fun _ => 1)
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
  have hbefore : strictI = inclusiveI + arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        (fun _ => 1) arrivalRate i
  have hafter' : inclusiveI = inclusiveK + arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          (fun _ => 1) arrivalRate k := by
            simpa [inclusiveI] using
              (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
                (fun _ => 1) arrivalRate hik hnoIntermediate).symm
      _ = inclusiveK + arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                (fun _ => 1) arrivalRate k
  have hcomparison :=
    AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentPriceGap_le_delayGap
      residual strictI inclusiveI inclusiveK (arrivalRate i) (arrivalRate k)
      (delayCost i) (delayCost k)
      (by
        simpa [residual] using
          (AppliedModelingLib.Queueing.finitePriorityResidualWork_nonneg arrivalRate
            (fun _ => 1) harrivalRate))
      (by simpa [strictI] using hstrict)
      (by simpa [inclusiveI] using hinclusive)
      (by simpa [inclusiveK] using hafter)
      (harrivalRate k) hdelayCost hbefore hafter'
  have hqueueI : homogeneousPriorityQueueingTime arrivalRate i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : homogeneousPriorityQueueingTime arrivalRate k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k) = _
    rw [← show inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate k by
      simpa [inclusiveI] using
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
          (fun _ => 1) arrivalRate hik hnoIntermediate).symm]
  have hprice := homogeneousPriorityPrice_sub_of_adjacent_explicit
    arrivalRate delayCost hik hnoIntermediate
  have hgap : homogeneousPriorityPrice arrivalRate delayCost i -
      homogeneousPriorityPrice arrivalRate delayCost k ≤
      delayCost i *
        (homogeneousPriorityQueueingTime arrivalRate k -
          homogeneousPriorityQueueingTime arrivalRate i) := by
    rw [hprice, hqueueI, hqueueK]
    exact hcomparison
  change homogeneousPriorityPrice arrivalRate delayCost i +
      delayCost i * (homogeneousPriorityQueueingTime arrivalRate i + 1) ≤
    homogeneousPriorityPrice arrivalRate delayCost k +
      delayCost i * (homogeneousPriorityQueueingTime arrivalRate k + 1)
  linarith

/-- The corrected strict adjacent comparison in Theorem 2.  Strict selection
requires positive equilibrium flow; without that hypothesis the immediately
preceding weak theorem is the valid boundary statement. -/
theorem homogeneousPriority_adjacentCost_lt
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False)
    (hdelayCost : delayCost k < delayCost i) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i <
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate (fun _ => 1)
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
  have hresidual : 0 < residual := by
    simpa [residual] using
      AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists arrivalRate (fun _ => 1)
        (fun j => (harrivalRate j).le) (fun _ => by norm_num) ⟨i, harrivalRate i⟩
  have hbefore : strictI = inclusiveI + arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        (fun _ => 1) arrivalRate i
  have hafter' : inclusiveI = inclusiveK + arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          (fun _ => 1) arrivalRate k := by
            simpa [inclusiveI] using
              (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
                (fun _ => 1) arrivalRate hik hnoIntermediate).symm
      _ = inclusiveK + arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                (fun _ => 1) arrivalRate k
  have hcomparison :=
    AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentPriceGap_lt_delayGap
      residual strictI inclusiveI inclusiveK (arrivalRate i) (arrivalRate k)
      (delayCost i) (delayCost k) hresidual
      (by simpa [strictI] using hstrict)
      (by simpa [inclusiveI] using hinclusive)
      (by simpa [inclusiveK] using hafter)
      (harrivalRate k) hdelayCost hbefore hafter'
  have hqueueI : homogeneousPriorityQueueingTime arrivalRate i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : homogeneousPriorityQueueingTime arrivalRate k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k) = _
    rw [← show inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate k by
      simpa [inclusiveI] using
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
          (fun _ => 1) arrivalRate hik hnoIntermediate).symm]
  have hprice := homogeneousPriorityPrice_sub_of_adjacent_explicit
    arrivalRate delayCost hik hnoIntermediate
  have hgap : homogeneousPriorityPrice arrivalRate delayCost i -
      homogeneousPriorityPrice arrivalRate delayCost k <
      delayCost i *
        (homogeneousPriorityQueueingTime arrivalRate k -
          homogeneousPriorityQueueingTime arrivalRate i) := by
    rw [hprice, hqueueI, hqueueK]
    exact hcomparison
  change homogeneousPriorityPrice arrivalRate delayCost i +
      delayCost i * (homogeneousPriorityQueueingTime arrivalRate i + 1) <
    homogeneousPriorityPrice arrivalRate delayCost k +
      delayCost i * (homogeneousPriorityQueueingTime arrivalRate k + 1)
  linarith

/-- The complementary weak adjacent comparison: the lower-priority class also
weakly prefers its assigned level.  This is the second local inequality needed
for the source proof's transitivity argument. -/
theorem homogeneousPriority_adjacentCost_le_reverse
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False)
    (hdelayCost : delayCost k ≤ delayCost i) :
    homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost k * homogeneousPrioritySojournTime arrivalRate k ≤
      homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost k * homogeneousPrioritySojournTime arrivalRate i := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate (fun _ => 1)
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
  have hbefore : strictI = inclusiveI + arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        (fun _ => 1) arrivalRate i
  have hafter' : inclusiveI = inclusiveK + arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          (fun _ => 1) arrivalRate k := by
            simpa [inclusiveI] using
              (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
                (fun _ => 1) arrivalRate hik hnoIntermediate).symm
      _ = inclusiveK + arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                (fun _ => 1) arrivalRate k
  have hcomparison :=
    AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentDelayGap_le_priceGap
      residual strictI inclusiveI inclusiveK (arrivalRate i) (arrivalRate k)
      (delayCost i) (delayCost k)
      (by
        simpa [residual] using
          (AppliedModelingLib.Queueing.finitePriorityResidualWork_nonneg arrivalRate
            (fun _ => 1) harrivalRate))
      (by simpa [strictI] using hstrict)
      (by simpa [inclusiveI] using hinclusive)
      (by simpa [inclusiveK] using hafter)
      (harrivalRate i) hdelayCost hbefore hafter'
  have hqueueI : homogeneousPriorityQueueingTime arrivalRate i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : homogeneousPriorityQueueingTime arrivalRate k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k) = _
    rw [← show inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate k by
      simpa [inclusiveI] using
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
          (fun _ => 1) arrivalRate hik hnoIntermediate).symm]
  have hprice := homogeneousPriorityPrice_sub_of_adjacent_explicit
    arrivalRate delayCost hik hnoIntermediate
  have hgap : delayCost k *
      (homogeneousPriorityQueueingTime arrivalRate k -
        homogeneousPriorityQueueingTime arrivalRate i) ≤
      homogeneousPriorityPrice arrivalRate delayCost i -
        homogeneousPriorityPrice arrivalRate delayCost k := by
    rw [hprice, hqueueI, hqueueK]
    exact hcomparison
  change homogeneousPriorityPrice arrivalRate delayCost k +
      delayCost k * (homogeneousPriorityQueueingTime arrivalRate k + 1) ≤
    homogeneousPriorityPrice arrivalRate delayCost i +
      delayCost k * (homogeneousPriorityQueueingTime arrivalRate i + 1)
  linarith

/-- The corrected strict adjacent comparison for a class considering the next
higher priority.  As on the other side of the boundary, strictness follows
from positive equilibrium flow and strictly ordered delay costs. -/
theorem homogeneousPriority_adjacentCost_lt_reverse
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ) {i k : Fin n}
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False)
    (hdelayCost : delayCost k < delayCost i) :
    homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost k * homogeneousPrioritySojournTime arrivalRate k <
      homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost k * homogeneousPrioritySojournTime arrivalRate i := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate (fun _ => 1)
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
  have hresidual : 0 < residual := by
    simpa [residual] using
      AppliedModelingLib.Queueing.finitePriorityResidualWork_pos_of_exists arrivalRate (fun _ => 1)
        (fun j => (harrivalRate j).le) (fun _ => by norm_num) ⟨i, harrivalRate i⟩
  have hbefore : strictI = inclusiveI + arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        (fun _ => 1) arrivalRate i
  have hafter' : inclusiveI = inclusiveK + arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          (fun _ => 1) arrivalRate k := by
            simpa [inclusiveI] using
              (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
                (fun _ => 1) arrivalRate hik hnoIntermediate).symm
      _ = inclusiveK + arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                (fun _ => 1) arrivalRate k
  have hcomparison :=
    AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentDelayGap_lt_priceGap
      residual strictI inclusiveI inclusiveK (arrivalRate i) (arrivalRate k)
      (delayCost i) (delayCost k) hresidual
      (by simpa [strictI] using hstrict)
      (by simpa [inclusiveI] using hinclusive)
      (by simpa [inclusiveK] using hafter)
      (harrivalRate i) hdelayCost hbefore hafter'
  have hqueueI : homogeneousPriorityQueueingTime arrivalRate i =
      residual / (strictI * inclusiveI) := by
    rfl
  have hqueueK : homogeneousPriorityQueueingTime arrivalRate k =
      residual / (inclusiveI * inclusiveK) := by
    change residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k) = _
    rw [← show inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate k by
      simpa [inclusiveI] using
        (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
          (fun _ => 1) arrivalRate hik hnoIntermediate).symm]
  have hprice := homogeneousPriorityPrice_sub_of_adjacent_explicit
    arrivalRate delayCost hik hnoIntermediate
  have hgap : delayCost k *
      (homogeneousPriorityQueueingTime arrivalRate k -
        homogeneousPriorityQueueingTime arrivalRate i) <
      homogeneousPriorityPrice arrivalRate delayCost i -
        homogeneousPriorityPrice arrivalRate delayCost k := by
    rw [hprice, hqueueI, hqueueK]
    exact hcomparison
  change homogeneousPriorityPrice arrivalRate delayCost k +
      delayCost k * (homogeneousPriorityQueueingTime arrivalRate k + 1) <
    homogeneousPriorityPrice arrivalRate delayCost i +
      delayCost k * (homogeneousPriorityQueueingTime arrivalRate i + 1)
  linarith

/-- Adjacent homogeneous-service sojourn times are ordered by priority.  The
statement is separated from pricing because the single-crossing propagation
uses this performance ordering at every intervening level. -/
theorem homogeneousPriority_adjacentSojournTime_le
    {n : ℕ} (arrivalRate : Fin n → ℝ) {i k : Fin n}
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hstrict : 0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack
      (fun _ => 1) arrivalRate i)
    (hinclusive : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate i)
    (hafter : 0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack
      (fun _ => 1) arrivalRate k)
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    homogeneousPrioritySojournTime arrivalRate i ≤
      homogeneousPrioritySojournTime arrivalRate k := by
  let residual := AppliedModelingLib.Queueing.finitePriorityResidualWork arrivalRate (fun _ => 1)
  let strictI := AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate i
  let inclusiveI := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate i
  let inclusiveK := AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k
  have hbefore : strictI = inclusiveI + arrivalRate i := by
    simpa [strictI, inclusiveI] using
      AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
        (fun _ => 1) arrivalRate i
  have hafter' : inclusiveI = inclusiveK + arrivalRate k := by
    calc
      inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
          (fun _ => 1) arrivalRate k := by
            simpa [inclusiveI] using
              (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
                (fun _ => 1) arrivalRate hik hnoIntermediate).symm
      _ = inclusiveK + arrivalRate k := by
            simpa [inclusiveK] using
              AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
                (fun _ => 1) arrivalRate k
  have hqueue := AppliedModelingLib.Queueing.nonpreemptivePriority_adjacentQueueWait_le
    residual strictI inclusiveI inclusiveK (arrivalRate i) (arrivalRate k)
    (by
      simpa [residual] using
        (AppliedModelingLib.Queueing.finitePriorityResidualWork_nonneg arrivalRate
          (fun _ => 1) harrivalRate))
    (by simpa [inclusiveI] using hinclusive)
    (by simpa [inclusiveK] using hafter)
    (harrivalRate i) (harrivalRate k) hbefore hafter'
  change homogeneousPriorityQueueingTime arrivalRate i + 1 ≤
    homogeneousPriorityQueueingTime arrivalRate k + 1
  change residual / (strictI * inclusiveI) + 1 ≤
    residual /
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate k *
        AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate k) + 1
  rw [← show inclusiveI = AppliedModelingLib.Queueing.finitePriorityStrictSlack
    (fun _ => 1) arrivalRate k by
    simpa [inclusiveI] using
      (AppliedModelingLib.Queueing.finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
        (fun _ => 1) arrivalRate hik hnoIntermediate).symm]
  linarith

/-- Starting from a class's assigned priority, its total price plus delay cost
cannot decrease along any finite sequence of lower-priority levels.  This is
the forward half of the source proof's single-crossing argument. -/
theorem homogeneousPriority_assignedCost_le_of_le
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i ≤ k → delayCost k ≤ delayCost i)
    (i k : Fin n) (hik : i ≤ k) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i ≤
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let cost : Fin n → Fin n → ℝ := fun customer priority =>
    homogeneousPriorityPrice arrivalRate delayCost priority +
      delayCost customer * homogeneousPrioritySojournTime arrivalRate priority
  let P : (m : ℕ) → i.1 ≤ m → Prop := fun m _ =>
    ∀ hmn : m < n, cost i i ≤ cost i ⟨m, hmn⟩
  have hforward : P k.1 hik := by
    refine Nat.le_induction (P := P) ?_ ?_ k.1 hik
    · intro hbound
      have heq : (⟨i.1, hbound⟩ : Fin n) = i := Fin.ext rfl
      simpa [heq]
    · intro m him hIH hbound
      have hboundPrev : m < n := by omega
      let j : Fin n := ⟨m, hboundPrev⟩
      let l : Fin n := ⟨m + 1, hbound⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hij : i ≤ j := by
        change i.1 ≤ m
        exact him
      have hfirst : cost i i ≤ cost i j := by
        simpa [j] using hIH hboundPrev
      have hsecond : cost j j ≤ cost j l := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_le arrivalRate delayCost harrivalRate
            (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
            (hdelayCost (le_of_lt hjl))
      have hwaiting : homogeneousPrioritySojournTime arrivalRate j ≤
          homogeneousPrioritySojournTime arrivalRate l :=
        homogeneousPriority_adjacentSojournTime_le arrivalRate harrivalRate
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have htrans := AppliedModelingLib.Queueing.priorityCost_transitive_towardLowerPriority
        (homogeneousPriorityPrice arrivalRate delayCost i)
        (homogeneousPriorityPrice arrivalRate delayCost j)
        (homogeneousPriorityPrice arrivalRate delayCost l)
        (delayCost i) (delayCost j)
        (homogeneousPrioritySojournTime arrivalRate i)
        (homogeneousPrioritySojournTime arrivalRate j)
        (homogeneousPrioritySojournTime arrivalRate l)
        (hdelayCost hij) hwaiting hfirst hsecond
      simpa [cost, j, l] using htrans
  simpa [cost] using hforward k.2

/-- The strict lower-priority half of the corrected Theorem 2.  The proof
starts from the strict adjacent comparison and preserves strictness through
the source's single-crossing transitivity argument. -/
theorem homogeneousPriority_assignedCost_lt_of_lt
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i < k → delayCost k < delayCost i)
    (i k : Fin n) (hik : i < k) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i <
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let cost : Fin n → Fin n → ℝ := fun customer priority =>
    homogeneousPriorityPrice arrivalRate delayCost priority +
      delayCost customer * homogeneousPrioritySojournTime arrivalRate priority
  let P : (m : ℕ) → i.1 + 1 ≤ m → Prop := fun m _ =>
    ∀ hmn : m < n, cost i i < cost i ⟨m, hmn⟩
  have hstart : i.1 + 1 ≤ k.1 := by
    change i.1 < k.1 at hik
    omega
  have hforward : P k.1 hstart := by
    refine Nat.le_induction (P := P) ?_ ?_ k.1 hstart
    · intro hbound
      let l : Fin n := ⟨i.1 + 1, hbound⟩
      have hil : i < l := by
        change i.1 < i.1 + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, i < a → a < l → False := by
        intro a hia hal
        change i.1 < a.1 at hia
        change a.1 < i.1 + 1 at hal
        omega
      have hlocal : cost i i < cost i l := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_lt arrivalRate delayCost harrivalRate
            (hslack i).1 (hslack i).2 (hslack l).2 hil hnoIntermediate
            (hdelayCost hil)
      simpa [l] using hlocal
    · intro m him hIH hbound
      have hboundPrev : m < n := by omega
      let j : Fin n := ⟨m, hboundPrev⟩
      let l : Fin n := ⟨m + 1, hbound⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hij : i < j := by
        change i.1 < m
        omega
      have hfirst : cost i i < cost i j := by
        simpa [j] using hIH hboundPrev
      have hsecond : cost j j ≤ cost j l := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_le arrivalRate delayCost
            (fun q => (harrivalRate q).le)
            (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
            (hdelayCost hjl).le
      have hwaiting : homogeneousPrioritySojournTime arrivalRate j ≤
          homogeneousPrioritySojournTime arrivalRate l :=
        homogeneousPriority_adjacentSojournTime_le arrivalRate
          (fun q => (harrivalRate q).le)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have htrans := AppliedModelingLib.Queueing.priorityCost_transitive_towardLowerPriority_lt
        (homogeneousPriorityPrice arrivalRate delayCost i)
        (homogeneousPriorityPrice arrivalRate delayCost j)
        (homogeneousPriorityPrice arrivalRate delayCost l)
        (delayCost i) (delayCost j)
        (homogeneousPrioritySojournTime arrivalRate i)
        (homogeneousPrioritySojournTime arrivalRate j)
        (homogeneousPrioritySojournTime arrivalRate l)
        (hdelayCost hij).le hwaiting hfirst hsecond
      simpa [cost, j, l] using htrans
  simpa [cost] using hforward k.2

/-- Starting from a class's assigned priority, its total price plus delay cost
cannot decrease along any finite sequence of higher-priority levels.  This is
the reverse half of the source proof's single-crossing argument. -/
theorem homogeneousPriority_assignedCost_le_of_ge
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i ≤ k → delayCost k ≤ delayCost i)
    (i k : Fin n) (hki : k ≤ i) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i ≤
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let cost : Fin n → Fin n → ℝ := fun customer priority =>
    homogeneousPriorityPrice arrivalRate delayCost priority +
      delayCost customer * homogeneousPrioritySojournTime arrivalRate priority
  let P : (m : ℕ) → m ≤ i.1 → Prop := fun m _ =>
    ∀ hmn : m < n, cost i i ≤ cost i ⟨m, hmn⟩
  have hbackward : P k.1 hki := by
    refine Nat.decreasingInduction (motive := P) (n := i.1) (m := k.1) ?_ ?_ hki
    · intro m hm hIH hbound
      have hboundNext : m + 1 < n := by omega
      let j : Fin n := ⟨m, hbound⟩
      let l : Fin n := ⟨m + 1, hboundNext⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hli : l ≤ i := by
        change m + 1 ≤ i.1
        omega
      have hfirst : cost i i ≤ cost i l := by
        simpa [l] using hIH hboundNext
      have hsecond : cost l l ≤ cost l j := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_le_reverse arrivalRate delayCost harrivalRate
            (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
            (hdelayCost (le_of_lt hjl))
      have hwaiting : homogeneousPrioritySojournTime arrivalRate j ≤
          homogeneousPrioritySojournTime arrivalRate l :=
        homogeneousPriority_adjacentSojournTime_le arrivalRate harrivalRate
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have htrans := AppliedModelingLib.Queueing.priorityCost_transitive_towardHigherPriority
        (homogeneousPriorityPrice arrivalRate delayCost i)
        (homogeneousPriorityPrice arrivalRate delayCost l)
        (homogeneousPriorityPrice arrivalRate delayCost j)
        (delayCost i) (delayCost l)
        (homogeneousPrioritySojournTime arrivalRate i)
        (homogeneousPrioritySojournTime arrivalRate l)
        (homogeneousPrioritySojournTime arrivalRate j)
        (hdelayCost hli) hwaiting hfirst hsecond
      simpa [cost, j, l] using htrans
    · intro hbound
      have heq : (⟨i.1, hbound⟩ : Fin n) = i := Fin.ext rfl
      simpa [heq]
  simpa [cost] using hbackward k.2

/-- The strict higher-priority half of the corrected Theorem 2. -/
theorem homogeneousPriority_assignedCost_lt_of_gt
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i < k → delayCost k < delayCost i)
    (i k : Fin n) (hki : k < i) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i <
      homogeneousPriorityPrice arrivalRate delayCost k +
        delayCost i * homogeneousPrioritySojournTime arrivalRate k := by
  let cost : Fin n → Fin n → ℝ := fun customer priority =>
    homogeneousPriorityPrice arrivalRate delayCost priority +
      delayCost customer * homogeneousPrioritySojournTime arrivalRate priority
  have hiPositive : 0 < i.1 := by
    change k.1 < i.1 at hki
    omega
  let P : (m : ℕ) → m ≤ i.1 - 1 → Prop := fun m _ =>
    ∀ hmn : m < n, cost i i < cost i ⟨m, hmn⟩
  have htarget : k.1 ≤ i.1 - 1 := by
    change k.1 < i.1 at hki
    omega
  have hbackward : P k.1 htarget := by
    refine Nat.decreasingInduction (motive := P) (n := i.1 - 1) (m := k.1) ?_ ?_ htarget
    · intro m hm hIH hbound
      have hboundNext : m + 1 < n := by
        omega
      let j : Fin n := ⟨m, hbound⟩
      let l : Fin n := ⟨m + 1, hboundNext⟩
      have hjl : j < l := by
        change m < m + 1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < l → False := by
        intro a hja hal
        change m < a.1 at hja
        change a.1 < m + 1 at hal
        omega
      have hli : l < i := by
        change m + 1 < i.1
        omega
      have hfirst : cost i i < cost i l := by
        simpa [l] using hIH hboundNext
      have hsecond : cost l l ≤ cost l j := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_le_reverse arrivalRate delayCost
            (fun q => (harrivalRate q).le)
            (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
            (hdelayCost hjl).le
      have hwaiting : homogeneousPrioritySojournTime arrivalRate j ≤
          homogeneousPrioritySojournTime arrivalRate l :=
        homogeneousPriority_adjacentSojournTime_le arrivalRate
          (fun q => (harrivalRate q).le)
          (hslack j).1 (hslack j).2 (hslack l).2 hjl hnoIntermediate
      have htrans := AppliedModelingLib.Queueing.priorityCost_transitive_towardHigherPriority_lt
        (homogeneousPriorityPrice arrivalRate delayCost i)
        (homogeneousPriorityPrice arrivalRate delayCost l)
        (homogeneousPriorityPrice arrivalRate delayCost j)
        (delayCost i) (delayCost l)
        (homogeneousPrioritySojournTime arrivalRate i)
        (homogeneousPrioritySojournTime arrivalRate l)
        (homogeneousPrioritySojournTime arrivalRate j)
        (hdelayCost hli).le hwaiting hfirst hsecond
      simpa [cost, j, l] using htrans
    · intro hbound
      have htopBound : i.1 - 1 < n := by omega
      let j : Fin n := ⟨i.1 - 1, htopBound⟩
      have hji : j < i := by
        change i.1 - 1 < i.1
        omega
      have hnoIntermediate : ∀ a : Fin n, j < a → a < i → False := by
        intro a hja hai
        change i.1 - 1 < a.1 at hja
        change a.1 < i.1 at hai
        omega
      have hlocal : cost i i < cost i j := by
        simpa [cost] using
          homogeneousPriority_adjacentCost_lt_reverse arrivalRate delayCost harrivalRate
            (hslack j).1 (hslack j).2 (hslack i).2 hji hnoIntermediate
            (hdelayCost hji)
      simpa [j] using hlocal
  simpa [cost] using hbackward k.2

/-- Section 2's incentive-compatibility conclusion for the homogeneous-service
priority price: every class weakly minimizes price plus its delay cost at its
assigned priority.  The weak form is valid even when an adjacent class has
zero equilibrium flow; strict selection requires the additional positivity
conditions recorded in the paper notes. -/
theorem homogeneousPriority_incentiveCompatible
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 ≤ arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i ≤ k → delayCost k ≤ delayCost i)
    (i selectedPriority : Fin n) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i ≤
      homogeneousPriorityPrice arrivalRate delayCost selectedPriority +
        delayCost i * homogeneousPrioritySojournTime arrivalRate selectedPriority := by
  rcases le_total i selectedPriority with hle | hge
  · exact homogeneousPriority_assignedCost_le_of_le arrivalRate delayCost
      harrivalRate hslack hdelayCost i selectedPriority hle
  · exact homogeneousPriority_assignedCost_le_of_ge arrivalRate delayCost
      harrivalRate hslack hdelayCost i selectedPriority hge

/-- Corrected strict form of Theorem 2: with positive equilibrium flows,
positive slacks, and strictly ordered delay costs, every misreported priority
has strictly higher expected private cost. -/
theorem homogeneousPriority_incentiveCompatible_strict
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (hslack : ∀ j,
      0 < AppliedModelingLib.Queueing.finitePriorityStrictSlack (fun _ => 1) arrivalRate j ∧
        0 < AppliedModelingLib.Queueing.finitePriorityInclusiveSlack (fun _ => 1) arrivalRate j)
    (hdelayCost : ∀ {i k : Fin n}, i < k → delayCost k < delayCost i)
    (i selectedPriority : Fin n) (hmisreport : selectedPriority ≠ i) :
    homogeneousPriorityPrice arrivalRate delayCost i +
        delayCost i * homogeneousPrioritySojournTime arrivalRate i <
      homogeneousPriorityPrice arrivalRate delayCost selectedPriority +
        delayCost i * homogeneousPrioritySojournTime arrivalRate selectedPriority := by
  rcases lt_or_gt_of_ne (Ne.symm hmisreport) with hilower | hihigher
  · exact homogeneousPriority_assignedCost_lt_of_lt arrivalRate delayCost
      harrivalRate hslack hdelayCost i selectedPriority hilower
  · exact homogeneousPriority_assignedCost_lt_of_gt arrivalRate delayCost
      harrivalRate hslack hdelayCost i selectedPriority hihigher

end

end MendelsonWhang1990PriorityPricing
