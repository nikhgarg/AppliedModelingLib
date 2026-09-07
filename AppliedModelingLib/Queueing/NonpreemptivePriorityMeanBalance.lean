import AppliedModelingLib.Queueing.NonpreemptivePriority

/-!
# Mean-wait balance for finite nonpreemptive-priority queues

The standard finite priority waiting-time expression is characterized here as
the unique solution of a linear mean-wait balance equation.  A stationary
queue construction can therefore establish the performance formula by proving
the balance from its Palm and workload identities.
-/

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-- The slack after the load of all classes whose priority index is smaller
than a finite boundary.  Boundary zero has slack one, and the two boundaries
around a class are its strict and inclusive priority slacks. -/
noncomputable def finitePriorityBoundarySlack
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (k : Fin (n + 1)) : ℝ :=
  1 - ∑ j : Fin n, if j.val < k.val then meanService j * arrivalRate j else 0

/-- The zero priority boundary has full unit slack. -/
theorem finitePriorityBoundarySlack_zero
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) :
    finitePriorityBoundarySlack meanService arrivalRate 0 = 1 := by
  simp [finitePriorityBoundarySlack]

/-- The boundary immediately before a class is its strict priority slack. -/
theorem finitePriorityBoundarySlack_castSucc
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) :
    finitePriorityBoundarySlack meanService arrivalRate i.castSucc =
      finitePriorityStrictSlack meanService arrivalRate i := by
  simp [finitePriorityBoundarySlack, finitePriorityStrictSlack,
    finitePriorityStrictLoad]

/-- The boundary immediately after a class is its inclusive priority slack. -/
theorem finitePriorityBoundarySlack_succ
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) :
    finitePriorityBoundarySlack meanService arrivalRate i.succ =
      finitePriorityInclusiveSlack meanService arrivalRate i := by
  unfold finitePriorityBoundarySlack finitePriorityInclusiveSlack finitePriorityInclusiveLoad
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j ≤ i
  · have hj : j.val < i.val + 1 := by omega
    simp [hji, hj]
  · have hj : ¬ j.val < i.val + 1 := by omega
    simp [hji, hj]

/-- Convert a sum written with a priority-index condition into a finite
initial-segment sum. -/
theorem sum_ite_le_eq_sum_Iic
    {n : ℕ} (i : Fin n) (f : Fin n → ℝ) :
    (∑ j, if j ≤ i then f j else 0) = ∑ j ∈ Finset.Iic i, f j := by
  classical
  symm
  change (∑ j ∈ Finset.Iic i, f j) =
    ∑ j ∈ Finset.univ, if j ≤ i then f j else 0
  calc
    (∑ j ∈ Finset.Iic i, f j) =
        ∑ j ∈ Finset.Iic i, if j ≤ i then f j else 0 := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Finset.mem_Iic] at hj
          simp [hj]
    _ = ∑ j ∈ Finset.univ, if j ≤ i then f j else 0 := by
          apply Finset.sum_subset
          · intro j _
            exact Finset.mem_univ _
          · intro j _ hj
            simp only [Finset.mem_Iic] at hj
            simp [hj]

/-- The finite mean-wait balance for a nonpreemptive priority queue.  The
right side comprises residual work plus the work associated with all classes
at least as urgent as the tagged class. -/
def finiteNonpreemptivePriorityMeanWaitBalance
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ) : Prop :=
  ∀ i,
    finitePriorityStrictSlack meanService arrivalRate i * meanWait i =
      finitePriorityResidualWork arrivalRate meanService +
        ∑ j, if j ≤ i then
          meanService j * arrivalRate j * meanWait j else 0

/-- The closed-form nonpreemptive-priority queue-wait expression satisfies
the finite mean-wait balance whenever its priority slacks are nonzero. -/
theorem finiteNonpreemptivePriorityQueueWait_satisfiesMeanWaitBalance
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hstrict : ∀ i, finitePriorityStrictSlack meanService arrivalRate i ≠ 0)
    (hinclusive : ∀ i, finitePriorityInclusiveSlack meanService arrivalRate i ≠ 0) :
    finiteNonpreemptivePriorityMeanWaitBalance arrivalRate meanService
      (finiteNonpreemptivePriorityQueueWait arrivalRate meanService) := by
  intro i
  classical
  let boundary : Fin (n + 1) → ℝ :=
    finitePriorityBoundarySlack meanService arrivalRate
  let reciprocal : Fin (n + 1) → ℝ := fun k => (boundary k)⁻¹
  have hreciprocal_zero : reciprocal 0 = 1 := by
    dsimp [reciprocal, boundary]
    rw [finitePriorityBoundarySlack_zero]
    simp
  have hterm : ∀ j : Fin n,
      meanService j * arrivalRate j *
          finiteNonpreemptivePriorityQueueWait arrivalRate meanService j =
        finitePriorityResidualWork arrivalRate meanService *
          (reciprocal j.succ - reciprocal j.castSucc) := by
    intro j
    dsimp [reciprocal, boundary]
    rw [finitePriorityBoundarySlack_succ, finitePriorityBoundarySlack_castSucc]
    unfold finiteNonpreemptivePriorityQueueWait
    have hslack := finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
      meanService arrivalRate j
    field_simp [hstrict j, hinclusive j]
    rw [hslack]
    ring
  have hsum :
      (∑ j, if j ≤ i then
          meanService j * arrivalRate j *
            finiteNonpreemptivePriorityQueueWait arrivalRate meanService j
        else 0) =
        finitePriorityResidualWork arrivalRate meanService *
          (reciprocal i.succ - reciprocal 0) := by
    calc
      (∑ j, if j ≤ i then
          meanService j * arrivalRate j *
            finiteNonpreemptivePriorityQueueWait arrivalRate meanService j
        else 0) =
          ∑ j ∈ Finset.Iic i,
            meanService j * arrivalRate j *
              finiteNonpreemptivePriorityQueueWait arrivalRate meanService j :=
            sum_ite_le_eq_sum_Iic i _
      _ = ∑ j ∈ Finset.Iic i,
          (finitePriorityResidualWork arrivalRate meanService *
            (reciprocal j.succ - reciprocal j.castSucc)) := by
            apply Finset.sum_congr rfl
            intro j _
            exact hterm j
      _ = finitePriorityResidualWork arrivalRate meanService *
          ∑ j ∈ Finset.Iic i,
            (reciprocal j.succ - reciprocal j.castSucc) := by
            rw [Finset.mul_sum]
      _ = finitePriorityResidualWork arrivalRate meanService *
          (reciprocal i.succ - reciprocal 0) := by
            rw [Fin.sum_Iic_sub]
  rw [hsum, hreciprocal_zero]
  have hreciprocal_succ :
      reciprocal i.succ =
        (finitePriorityInclusiveSlack meanService arrivalRate i)⁻¹ := by
    dsimp [reciprocal, boundary]
    rw [finitePriorityBoundarySlack_succ]
  rw [hreciprocal_succ]
  unfold finiteNonpreemptivePriorityQueueWait
  field_simp [hstrict i, hinclusive i]
  ring

/-- Any finite mean-wait vector satisfying the nonpreemptive-priority balance
is the standard closed-form queue-wait vector.  Thus a stationary construction
need only establish the balance equation to identify its mean waiting times. -/
theorem finiteNonpreemptivePriorityMeanWaitBalance_eq_queueWait
    {n : ℕ} (arrivalRate meanService meanWait : Fin n → ℝ)
    (hstrict : ∀ i, finitePriorityStrictSlack meanService arrivalRate i ≠ 0)
    (hinclusive : ∀ i, finitePriorityInclusiveSlack meanService arrivalRate i ≠ 0)
    (hbalance : finiteNonpreemptivePriorityMeanWaitBalance
      arrivalRate meanService meanWait) (i : Fin n) :
    meanWait i = finiteNonpreemptivePriorityQueueWait arrivalRate meanService i := by
  classical
  have hformula := finiteNonpreemptivePriorityQueueWait_satisfiesMeanWaitBalance
    arrivalRate meanService hstrict hinclusive
  have hforall : ∀ k (hk : k < n),
      meanWait ⟨k, hk⟩ =
        finiteNonpreemptivePriorityQueueWait arrivalRate meanService ⟨k, hk⟩ := by
    intro k hk
    induction k using Nat.strong_induction_on with
    | h k ih =>
        let current : Fin n := ⟨k, hk⟩
        have hsum :
            (∑ j, if j ≤ current then
                meanService j * arrivalRate j * meanWait j else 0) =
              (∑ j, if j ≤ current then
                meanService j * arrivalRate j *
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService j else 0) +
                meanService current * arrivalRate current *
                  (meanWait current -
                    finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) := by
          calc
            (∑ j, if j ≤ current then
                meanService j * arrivalRate j * meanWait j else 0) =
                ∑ j ∈ Finset.Iic current,
                  meanService j * arrivalRate j * meanWait j :=
              sum_ite_le_eq_sum_Iic current _
            _ = ∑ j ∈ Finset.Iic current,
                (meanService j * arrivalRate j *
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService j +
                  if j = current then
                    meanService current * arrivalRate current *
                      (meanWait current -
                        finiteNonpreemptivePriorityQueueWait arrivalRate meanService current)
                  else 0) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp only [Finset.mem_Iic] at hj
                    by_cases hjcurrent : j = current
                    · subst j
                      simp
                      ring
                    · have hjlt : j < current := lt_of_le_of_ne hj hjcurrent
                      have hjvalue := ih j.val (by simpa using hjlt)
                      rw [hjvalue]
                      simp [hjcurrent]
            _ = (∑ j ∈ Finset.Iic current,
                meanService j * arrivalRate j *
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService j) +
                ∑ j ∈ Finset.Iic current, if j = current then
                  meanService current * arrivalRate current *
                    (meanWait current -
                      finiteNonpreemptivePriorityQueueWait arrivalRate meanService current)
                else 0 := by
                  rw [Finset.sum_add_distrib]
            _ = (∑ j, if j ≤ current then
                meanService j * arrivalRate j *
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService j else 0) +
                meanService current * arrivalRate current *
                  (meanWait current -
                    finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) := by
                  rw [← sum_ite_le_eq_sum_Iic]
                  simp
        have hcurrent := hbalance current
        have hformulaCurrent := hformula current
        rw [hsum] at hcurrent
        have hcurrent' :
            finitePriorityStrictSlack meanService arrivalRate current * meanWait current =
              finitePriorityStrictSlack meanService arrivalRate current *
                finiteNonpreemptivePriorityQueueWait arrivalRate meanService current +
              meanService current * arrivalRate current *
                (meanWait current -
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) := by
          calc
            finitePriorityStrictSlack meanService arrivalRate current * meanWait current =
                finitePriorityResidualWork arrivalRate meanService +
                  ((∑ j, if j ≤ current then
                    meanService j * arrivalRate j *
                      finiteNonpreemptivePriorityQueueWait arrivalRate meanService j else 0) +
                    meanService current * arrivalRate current *
                      (meanWait current -
                        finiteNonpreemptivePriorityQueueWait arrivalRate meanService current)) := hcurrent
            _ = (finitePriorityResidualWork arrivalRate meanService +
                  ∑ j, if j ≤ current then
                    meanService j * arrivalRate j *
                      finiteNonpreemptivePriorityQueueWait arrivalRate meanService j else 0) +
                  meanService current * arrivalRate current *
                    (meanWait current -
                      finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) := by ring
            _ = finitePriorityStrictSlack meanService arrivalRate current *
                  finiteNonpreemptivePriorityQueueWait arrivalRate meanService current +
                meanService current * arrivalRate current *
                  (meanWait current -
                    finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) := by
                  rw [← hformulaCurrent]
        have hslack := finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
          meanService arrivalRate current
        have hzero :
            finitePriorityInclusiveSlack meanService arrivalRate current *
              (meanWait current -
                finiteNonpreemptivePriorityQueueWait arrivalRate meanService current) = 0 := by
          rw [hslack] at hcurrent'
          nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left (hinclusive current))
  exact hforall i.val i.isLt

end Queueing
end AppliedModelingLib
