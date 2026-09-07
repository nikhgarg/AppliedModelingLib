import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AppliedModelingLib
namespace Queueing

open scoped BigOperators

/-!
# Finite nonpreemptive-priority queueing expressions

This module gives the finite-class load, residual-work, and waiting-time
expressions used by standard nonpreemptive-priority M/G/1 and M/M/1 formulas.
The declarations are algebraic: a stochastic queue construction can prove that
its stationary performance equals these expressions without making the
construction part of this reusable API.
-/

/-- Load contributed by priority classes at least as urgent as `i`, when lower
`Fin` indices represent higher priority. -/
noncomputable def finitePriorityInclusiveLoad
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, if j ≤ i then meanService j * arrivalRate j else 0

/-- Load contributed by classes strictly more urgent than `i`. -/
noncomputable def finitePriorityStrictLoad
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, if j < i then meanService j * arrivalRate j else 0

/-- Directional derivative of inclusive priority load when a single arrival
rate is varied. -/
theorem hasDerivAt_finitePriorityInclusiveLoad_update
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i k : Fin n) :
    HasDerivAt
      (fun t => finitePriorityInclusiveLoad meanService
        (Function.update arrivalRate i t) k)
      (if i ≤ k then meanService i else 0)
      (arrivalRate i) := by
  classical
  have hterm : ∀ j : Fin n,
      HasDerivAt
        (fun t => if j ≤ k then
          meanService j * Function.update arrivalRate i t j else 0)
        (if j ≤ k then
          meanService j * (if j = i then 1 else 0) else 0)
        (arrivalRate i) := by
    intro j
    by_cases hjk : j ≤ k
    · simp only [hjk, ↓reduceIte]
      by_cases hji : j = i
      · subst j
        simpa using (hasDerivAt_id (x := arrivalRate i)).const_mul (meanService i)
      · simpa [hji, Function.update_of_ne hji] using
          (hasDerivAt_const (x := arrivalRate i)
            (c := meanService j * arrivalRate j))
    · simpa [hjk] using
        (hasDerivAt_const (x := arrivalRate i) (c := (0 : ℝ)))
  have hsum :
      (∑ j : Fin n, if j ≤ k then
        meanService j * (if j = i then 1 else 0) else 0) =
        (if i ≤ k then meanService i else 0) := by
    by_cases hik : i ≤ k
    · calc
        _ = ∑ j : Fin n, if j = i then meanService i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [hik]
          · simp [hji]
        _ = meanService i := by simp
        _ = if i ≤ k then meanService i else 0 := by simp [hik]
    · calc
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          by_cases hji : j = i
          · subst j
            simp [hik]
          · simp [hji]
        _ = if i ≤ k then meanService i else 0 := by simp [hik]
  change HasDerivAt
    (fun t => ∑ j : Fin n,
      if j ≤ k then meanService j * Function.update arrivalRate i t j else 0)
    _ (arrivalRate i)
  convert (HasDerivAt.sum (u := Finset.univ) fun j _ => hterm j) using 1
  · ext t
    simp only [Finset.sum_apply]
  · exact hsum.symm

/-- Directional derivative of strict priority load when a single arrival rate
is varied. -/
theorem hasDerivAt_finitePriorityStrictLoad_update
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i k : Fin n) :
    HasDerivAt
      (fun t => finitePriorityStrictLoad meanService
        (Function.update arrivalRate i t) k)
      (if i < k then meanService i else 0)
      (arrivalRate i) := by
  classical
  have hterm : ∀ j : Fin n,
      HasDerivAt
        (fun t => if j < k then
          meanService j * Function.update arrivalRate i t j else 0)
        (if j < k then
          meanService j * (if j = i then 1 else 0) else 0)
        (arrivalRate i) := by
    intro j
    by_cases hjk : j < k
    · simp only [hjk, ↓reduceIte]
      by_cases hji : j = i
      · subst j
        simpa using (hasDerivAt_id (x := arrivalRate i)).const_mul (meanService i)
      · simpa [hji, Function.update_of_ne hji] using
          (hasDerivAt_const (x := arrivalRate i)
            (c := meanService j * arrivalRate j))
    · simpa [hjk] using
        (hasDerivAt_const (x := arrivalRate i) (c := (0 : ℝ)))
  have hsum :
      (∑ j : Fin n, if j < k then
        meanService j * (if j = i then 1 else 0) else 0) =
        (if i < k then meanService i else 0) := by
    by_cases hik : i < k
    · calc
        _ = ∑ j : Fin n, if j = i then meanService i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [hik]
          · simp [hji]
        _ = meanService i := by simp
        _ = if i < k then meanService i else 0 := by simp [hik]
    · calc
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          by_cases hji : j = i
          · subst j
            simp [hik]
          · simp [hji]
        _ = if i < k then meanService i else 0 := by simp [hik]
  change HasDerivAt
    (fun t => ∑ j : Fin n,
      if j < k then meanService j * Function.update arrivalRate i t j else 0)
    _ (arrivalRate i)
  convert (HasDerivAt.sum (u := Finset.univ) fun j _ => hterm j) using 1
  · ext t
    simp only [Finset.sum_apply]
  · exact hsum.symm

/-- Inclusive load is strict load plus the contribution of the class at the
priority boundary. -/
theorem finitePriorityInclusiveLoad_eq_strictLoad_add_self
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) :
    finitePriorityInclusiveLoad meanService arrivalRate i =
      finitePriorityStrictLoad meanService arrivalRate i +
        meanService i * arrivalRate i := by
  classical
  unfold finitePriorityInclusiveLoad finitePriorityStrictLoad
  calc
    (∑ j : Fin n, if j ≤ i then meanService j * arrivalRate j else 0) =
        (∑ j : Fin n, if j < i then meanService j * arrivalRate j else 0) +
          ∑ j : Fin n, if j = i then meanService i * arrivalRate i else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · by_cases hji' : j < i
        · simp [hji', hji, hji'.le]
        · have hnotle : ¬ j ≤ i := by
            intro hle
            exact hji' (lt_of_le_of_ne hle hji)
          simp [hji, hji', hnotle]
    _ = (∑ j : Fin n, if j < i then meanService j * arrivalRate j else 0) +
        meanService i * arrivalRate i := by simp
    _ = finitePriorityStrictLoad meanService arrivalRate i +
        meanService i * arrivalRate i := by rfl

/-- The residual-work numerator `Σᵢ λᵢ E[Sᵢ²]/2`.  For exponential service
with mean `cᵢ`, this is `Σᵢ λᵢ cᵢ²`. -/
noncomputable def finitePriorityResidualWork
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) : ℝ :=
  ∑ j, arrivalRate j * meanService j ^ 2

/-- Nonnegative arrival rates give a nonnegative residual-work numerator. -/
theorem finitePriorityResidualWork_nonneg
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i) :
    0 ≤ finitePriorityResidualWork arrivalRate meanService := by
  unfold finitePriorityResidualWork
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (harrivalRate i) (sq_nonneg (meanService i))

/-- Positive arrival work in any class makes the finite residual-work numerator
strictly positive. -/
theorem finitePriorityResidualWork_pos_of_exists
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (hpositiveArrival : ∃ i, 0 < arrivalRate i) :
    0 < finitePriorityResidualWork arrivalRate meanService := by
  rcases hpositiveArrival with ⟨i, hi⟩
  have hterm : 0 < arrivalRate i * meanService i ^ 2 :=
    mul_pos hi (sq_pos_of_pos (hmeanService i))
  have hle : arrivalRate i * meanService i ^ 2 ≤
      ∑ j, arrivalRate j * meanService j ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ => mul_nonneg (harrivalRate j) (sq_nonneg (meanService j)))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le hterm (by simpa [finitePriorityResidualWork] using hle)

/-- Directional derivative of the exponential-service residual-work numerator
when one arrival rate is varied. -/
theorem hasDerivAt_finitePriorityResidualWork_update
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) :
    HasDerivAt
      (fun t => finitePriorityResidualWork
        (Function.update arrivalRate i t) meanService)
      (meanService i ^ 2) (arrivalRate i) := by
  classical
  have hterm : ∀ j : Fin n,
      HasDerivAt
        (fun t => Function.update arrivalRate i t j * meanService j ^ 2)
        ((if j = i then 1 else 0) * meanService j ^ 2)
        (arrivalRate i) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa using (hasDerivAt_id (x := arrivalRate i)).mul_const
        (meanService i ^ 2)
    · simpa [hji, Function.update_of_ne hji] using
        (hasDerivAt_const (x := arrivalRate i)
          (c := arrivalRate j * meanService j ^ 2))
  have hsum :
      (∑ j : Fin n, (if j = i then 1 else 0) * meanService j ^ 2) =
        meanService i ^ 2 := by
    calc
      _ = ∑ j : Fin n, if j = i then meanService i ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
      _ = meanService i ^ 2 := by simp
  change HasDerivAt
    (fun t => ∑ j : Fin n,
      Function.update arrivalRate i t j * meanService j ^ 2)
    _ (arrivalRate i)
  convert (HasDerivAt.sum (u := Finset.univ) fun j _ => hterm j) using 1
  · ext t
    simp only [Finset.sum_apply]
  · exact hsum.symm

/-- Slack after the load of all classes at least as urgent as `i`. -/
noncomputable def finitePriorityInclusiveSlack
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 - finitePriorityInclusiveLoad meanService arrivalRate i

/-- Slack after the load of all classes strictly more urgent than `i`. -/
noncomputable def finitePriorityStrictSlack
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) : ℝ :=
  1 - finitePriorityStrictLoad meanService arrivalRate i

/-- Directional derivative of inclusive priority slack. -/
theorem hasDerivAt_finitePriorityInclusiveSlack_update
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i k : Fin n) :
    HasDerivAt
      (fun t => finitePriorityInclusiveSlack meanService
        (Function.update arrivalRate i t) k)
      (-(if i ≤ k then meanService i else 0))
      (arrivalRate i) := by
  unfold finitePriorityInclusiveSlack
  simpa using
    (hasDerivAt_const (x := arrivalRate i) (c := (1 : ℝ))).sub
      (hasDerivAt_finitePriorityInclusiveLoad_update meanService arrivalRate i k)

/-- Directional derivative of strict priority slack. -/
theorem hasDerivAt_finitePriorityStrictSlack_update
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i k : Fin n) :
    HasDerivAt
      (fun t => finitePriorityStrictSlack meanService
        (Function.update arrivalRate i t) k)
      (-(if i < k then meanService i else 0))
      (arrivalRate i) := by
  unfold finitePriorityStrictSlack
  simpa using
    (hasDerivAt_const (x := arrivalRate i) (c := (1 : ℝ))).sub
      (hasDerivAt_finitePriorityStrictLoad_update meanService arrivalRate i k)

/-- The strict slack before a priority level equals the inclusive slack after
that level plus its load contribution. -/
theorem finitePriorityStrictSlack_eq_inclusiveSlack_add_selfLoad
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) (i : Fin n) :
    finitePriorityStrictSlack meanService arrivalRate i =
      finitePriorityInclusiveSlack meanService arrivalRate i +
        meanService i * arrivalRate i := by
  unfold finitePriorityStrictSlack finitePriorityInclusiveSlack
  rw [finitePriorityInclusiveLoad_eq_strictLoad_add_self]
  ring

/-- The load through a priority boundary is bounded by the total load when
every class has nonnegative work arrival rate. -/
theorem finitePriorityInclusiveLoad_le_totalLoad
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ)
    (hload_nonneg : ∀ j, 0 ≤ meanService j * arrivalRate j)
    (i : Fin n) :
    finitePriorityInclusiveLoad meanService arrivalRate i ≤
      ∑ j, meanService j * arrivalRate j := by
  unfold finitePriorityInclusiveLoad
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j ≤ i
  · simp [hji]
  · simp [hji, hload_nonneg j]

/-- The strict-higher-priority load is bounded by total load under the same
nonnegativity condition. -/
theorem finitePriorityStrictLoad_le_totalLoad
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ)
    (hload_nonneg : ∀ j, 0 ≤ meanService j * arrivalRate j)
    (i : Fin n) :
    finitePriorityStrictLoad meanService arrivalRate i ≤
      ∑ j, meanService j * arrivalRate j := by
  unfold finitePriorityStrictLoad
  apply Finset.sum_le_sum
  intro j _
  by_cases hji : j < i
  · simp [hji]
  · simp [hji, hload_nonneg j]

/-- Strict total load below one makes every inclusive priority slack positive. -/
theorem finitePriorityInclusiveSlack_pos_of_totalLoad_lt_one
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ)
    (hload_nonneg : ∀ j, 0 ≤ meanService j * arrivalRate j)
    (htotal : ∑ j, meanService j * arrivalRate j < 1)
    (i : Fin n) :
    0 < finitePriorityInclusiveSlack meanService arrivalRate i := by
  unfold finitePriorityInclusiveSlack
  linarith [finitePriorityInclusiveLoad_le_totalLoad
    meanService arrivalRate hload_nonneg i]

/-- Strict total load below one makes every strict priority slack positive. -/
theorem finitePriorityStrictSlack_pos_of_totalLoad_lt_one
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ)
    (hload_nonneg : ∀ j, 0 ≤ meanService j * arrivalRate j)
    (htotal : ∑ j, meanService j * arrivalRate j < 1)
    (i : Fin n) :
    0 < finitePriorityStrictSlack meanService arrivalRate i := by
  unfold finitePriorityStrictSlack
  linarith [finitePriorityStrictLoad_le_totalLoad
    meanService arrivalRate hload_nonneg i]

/-- If `k` is the priority level immediately below `i`, the strict load before
`k` is the inclusive load through `i`. -/
theorem finitePriorityStrictLoad_eq_inclusiveLoad_of_adjacent
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    finitePriorityStrictLoad meanService arrivalRate k =
      finitePriorityInclusiveLoad meanService arrivalRate i := by
  unfold finitePriorityStrictLoad finitePriorityInclusiveLoad
  apply Finset.sum_congr rfl
  intro j _
  have hiff : j < k ↔ j ≤ i := by
    constructor
    · intro hjk
      by_contra hnot
      exact hnoIntermediate j (lt_of_not_ge hnot) hjk
    · intro hji
      exact lt_of_le_of_lt hji hik
  simp only [hiff]

/-- The corresponding immediate-adjacent priority slacks agree. -/
theorem finitePriorityStrictSlack_eq_inclusiveSlack_of_adjacent
    {n : ℕ} (meanService arrivalRate : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    finitePriorityStrictSlack meanService arrivalRate k =
      finitePriorityInclusiveSlack meanService arrivalRate i := by
  unfold finitePriorityStrictSlack finitePriorityInclusiveSlack
  rw [finitePriorityStrictLoad_eq_inclusiveLoad_of_adjacent
    meanService arrivalRate hik hnoIntermediate]

/-- Two priority suffix sums differ by exactly their boundary term when their
indices are adjacent. -/
theorem sum_prioritySuffix_sub_of_adjacent
    {n : ℕ} (f : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    ((∑ j, if i ≤ j then f j else 0) -
      (∑ j, if k ≤ j then f j else 0)) = f i := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin n, ((if i ≤ j then f j else 0) -
        (if k ≤ j then f j else 0))) =
        (∑ j : Fin n, if j = i then f i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp [not_le_of_gt hik]
      · have hiff : i ≤ j ↔ k ≤ j := by
          constructor
          · intro hij
            have hij' : i < j := lt_of_le_of_ne hij (fun h => hji h.symm)
            by_contra hnot
            exact hnoIntermediate j hij' (lt_of_not_ge hnot)
          · intro hkj
            exact hik.le.trans hkj
        simp [hji, hiff]
    _ = f i := by simp

/-- Strict and weak priority suffixes differ by their first included term.
For adjacent priority levels, the strict suffix above the higher level is the
weak suffix beginning at the next lower level. -/
theorem sum_priorityStrictSuffix_sub_of_adjacent
    {n : ℕ} (f : Fin n → ℝ) {i k : Fin n}
    (hik : i < k)
    (hnoIntermediate : ∀ j : Fin n, i < j → j < k → False) :
    ((∑ j, if i < j then f j else 0) -
      (∑ j, if k < j then f j else 0)) = f k := by
  have hrewrite : ∀ j : Fin n, i < j ↔ k ≤ j := by
    intro j
    constructor
    · intro hij
      by_contra hnot
      exact hnoIntermediate j hij (lt_of_not_ge hnot)
    · intro hkj
      exact lt_of_lt_of_le hik hkj
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j : Fin n, ((if i < j then f j else 0) -
        (if k < j then f j else 0))) =
        (∑ j : Fin n, if j = k then f k else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hjk : j = k
      · subst j
        simp [hik]
      · have hiff : k ≤ j ↔ k < j := by
          constructor
          · intro h
            exact lt_of_le_of_ne h (fun hEq => hjk hEq.symm)
          · intro h
            exact h.le
        simp [hjk, hrewrite j, hiff]
    _ = f k := by simp

/-- Standard nonpreemptive-priority mean waiting time in queue, expressed in
terms of the residual-work numerator and the two priority-load slacks. -/
noncomputable def finiteNonpreemptivePriorityQueueWait
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  finitePriorityResidualWork arrivalRate meanService /
    (finitePriorityStrictSlack meanService arrivalRate i *
      finitePriorityInclusiveSlack meanService arrivalRate i)

/-- Directional derivative of the finite nonpreemptive-priority queueing-time
expression.  The two nonzero-slack hypotheses are exactly the algebraic
regularity conditions for differentiating the displayed quotient. -/
theorem hasDerivAt_finiteNonpreemptivePriorityQueueWait_update
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i k : Fin n)
    (hstrict : finitePriorityStrictSlack meanService arrivalRate k ≠ 0)
    (hinclusive : finitePriorityInclusiveSlack meanService arrivalRate k ≠ 0) :
    HasDerivAt
      (fun t => finiteNonpreemptivePriorityQueueWait
        (Function.update arrivalRate i t) meanService k)
      ((meanService i ^ 2 *
          (finitePriorityStrictSlack meanService arrivalRate k *
            finitePriorityInclusiveSlack meanService arrivalRate k) -
        finitePriorityResidualWork arrivalRate meanService *
          ((-(if i < k then meanService i else 0)) *
              finitePriorityInclusiveSlack meanService arrivalRate k +
            finitePriorityStrictSlack meanService arrivalRate k *
              (-(if i ≤ k then meanService i else 0)))) /
        (finitePriorityStrictSlack meanService arrivalRate k *
          finitePriorityInclusiveSlack meanService arrivalRate k) ^ 2)
      (arrivalRate i) := by
  have hresidual :=
    hasDerivAt_finitePriorityResidualWork_update arrivalRate meanService i
  have hstrict' :=
    hasDerivAt_finitePriorityStrictSlack_update meanService arrivalRate i k
  have hinclusive' :=
    hasDerivAt_finitePriorityInclusiveSlack_update meanService arrivalRate i k
  have hstrictAt :
      (fun t => finitePriorityStrictSlack meanService
        (Function.update arrivalRate i t) k) (arrivalRate i) ≠ 0 := by
    simpa using hstrict
  have hinclusiveAt :
      (fun t => finitePriorityInclusiveSlack meanService
        (Function.update arrivalRate i t) k) (arrivalRate i) ≠ 0 := by
    simpa using hinclusive
  unfold finiteNonpreemptivePriorityQueueWait
  simpa using hresidual.div (hstrict'.mul hinclusive')
    (mul_ne_zero hstrictAt hinclusiveAt)

/-- Standard nonpreemptive-priority mean sojourn time: queueing time plus the
class's own mean service time. -/
noncomputable def finiteNonpreemptivePrioritySojournTime
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) : ℝ :=
  finiteNonpreemptivePriorityQueueWait arrivalRate meanService i + meanService i

/-- Directional derivative of the finite nonpreemptive-priority total-time
expression.  Service time is constant under a change in an arrival-rate
coordinate, so this agrees with the queueing-time derivative. -/
theorem hasDerivAt_finiteNonpreemptivePrioritySojournTime_update
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i k : Fin n)
    (hstrict : finitePriorityStrictSlack meanService arrivalRate k ≠ 0)
    (hinclusive : finitePriorityInclusiveSlack meanService arrivalRate k ≠ 0) :
    HasDerivAt
      (fun t => finiteNonpreemptivePrioritySojournTime
        (Function.update arrivalRate i t) meanService k)
      ((meanService i ^ 2 *
          (finitePriorityStrictSlack meanService arrivalRate k *
            finitePriorityInclusiveSlack meanService arrivalRate k) -
        finitePriorityResidualWork arrivalRate meanService *
          ((-(if i < k then meanService i else 0)) *
              finitePriorityInclusiveSlack meanService arrivalRate k +
            finitePriorityStrictSlack meanService arrivalRate k *
              (-(if i ≤ k then meanService i else 0)))) /
        (finitePriorityStrictSlack meanService arrivalRate k *
          finitePriorityInclusiveSlack meanService arrivalRate k) ^ 2)
      (arrivalRate i) := by
  unfold finiteNonpreemptivePrioritySojournTime
  simpa using
    (hasDerivAt_finiteNonpreemptivePriorityQueueWait_update
      arrivalRate meanService i k hstrict hinclusive).add_const (meanService k)

/-- With unit mean service times, the residual-work numerator is total arrival
rate. -/
theorem finitePriorityResidualWork_one
    {n : ℕ} (arrivalRate : Fin n → ℝ) :
    finitePriorityResidualWork arrivalRate (fun _ => 1) = ∑ j, arrivalRate j := by
  simp [finitePriorityResidualWork]

/-- The sojourn-time expression decomposes into its queueing and service
components by definition. -/
theorem finiteNonpreemptivePrioritySojournTime_eq_queueWait_add_service
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ) (i : Fin n) :
    finiteNonpreemptivePrioritySojournTime arrivalRate meanService i =
      finiteNonpreemptivePriorityQueueWait arrivalRate meanService i + meanService i := rfl

/-- Exact adjacent-level accounting identity: the delay-cost increase from
dropping one priority level minus the direct-price saving has a factored form.
The sign consequences are stated separately below. -/
theorem nonpreemptivePriority_adjacentDelayGap_sub_priceGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hslackBefore : slackBefore ≠ 0) (hslackHere : slackHere ≠ 0)
    (hslackAfter : slackAfter ≠ 0)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    delayCostHere *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) -
      (arrivalHere * delayCostHere *
          (residual / (slackBefore * slackHere)) +
        arrivalAfter * delayCostAfter *
          (residual / (slackHere * slackAfter))) / slackHere =
      residual * arrivalAfter * (delayCostHere - delayCostAfter) /
        (slackHere ^ 2 * slackAfter) := by
  field_simp
  rw [hbefore, hafter]
  ring

/-- Strict adjacent-level single crossing for a nonpreemptive-priority queue.
When the two neighboring arrival rates are positive and the higher-priority
type has strictly larger delay cost, the direct-price saving from dropping one
priority level is strictly smaller than the resulting delay-cost increase. -/
theorem nonpreemptivePriority_adjacentPriceGap_lt_delayGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hresidual : 0 < residual) (hslackBefore : 0 < slackBefore)
    (hslackHere : 0 < slackHere) (hslackAfter : 0 < slackAfter)
    (harrivalAfter : 0 < arrivalAfter)
    (hdelayCost : delayCostAfter < delayCostHere)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    (arrivalHere * delayCostHere *
        (residual / (slackBefore * slackHere)) +
      arrivalAfter * delayCostAfter *
        (residual / (slackHere * slackAfter))) / slackHere <
      delayCostHere *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) := by
  have hbefore0 : slackBefore ≠ 0 := ne_of_gt hslackBefore
  have hhere0 : slackHere ≠ 0 := ne_of_gt hslackHere
  have hafter0 : slackAfter ≠ 0 := ne_of_gt hslackAfter
  have hgap :
      delayCostHere *
          (residual / (slackHere * slackAfter) -
            residual / (slackBefore * slackHere)) -
        (arrivalHere * delayCostHere *
            (residual / (slackBefore * slackHere)) +
          arrivalAfter * delayCostAfter *
            (residual / (slackHere * slackAfter))) / slackHere =
        residual * arrivalAfter * (delayCostHere - delayCostAfter) /
          (slackHere ^ 2 * slackAfter) := by
    exact nonpreemptivePriority_adjacentDelayGap_sub_priceGap
      residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter hbefore0 hhere0 hafter0 hbefore hafter
  have hpositive :
      0 < residual * arrivalAfter * (delayCostHere - delayCostAfter) /
        (slackHere ^ 2 * slackAfter) := by
    apply div_pos
    · exact mul_pos (mul_pos hresidual harrivalAfter) (sub_pos.mpr hdelayCost)
    · exact mul_pos (sq_pos_of_pos hslackHere) hslackAfter
  linarith

/-- Weak adjacent-level single crossing.  Unlike the strict version, this
allows a zero neighboring arrival rate and is the appropriate statement at
that boundary. -/
theorem nonpreemptivePriority_adjacentPriceGap_le_delayGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hresidual : 0 ≤ residual) (hslackBefore : 0 < slackBefore)
    (hslackHere : 0 < slackHere) (hslackAfter : 0 < slackAfter)
    (harrivalAfter : 0 ≤ arrivalAfter)
    (hdelayCost : delayCostAfter ≤ delayCostHere)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    (arrivalHere * delayCostHere *
        (residual / (slackBefore * slackHere)) +
      arrivalAfter * delayCostAfter *
        (residual / (slackHere * slackAfter))) / slackHere ≤
      delayCostHere *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) := by
  have hgap := nonpreemptivePriority_adjacentDelayGap_sub_priceGap
    residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
    delayCostHere delayCostAfter (ne_of_gt hslackBefore) (ne_of_gt hslackHere)
    (ne_of_gt hslackAfter) hbefore hafter
  have hnonnegative :
      0 ≤ residual * arrivalAfter * (delayCostHere - delayCostAfter) /
        (slackHere ^ 2 * slackAfter) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hresidual harrivalAfter) (sub_nonneg.mpr hdelayCost)
    · exact mul_nonneg (sq_nonneg slackHere) (le_of_lt hslackAfter)
  linarith

/-- The complementary adjacent single-crossing identity.  Relative to the
lower-priority class's delay cost, the price gap exceeds the delay gap by a
nonnegative term when the higher-priority class has weakly larger delay cost.
Together with `nonpreemptivePriority_adjacentDelayGap_sub_priceGap`, this
gives the two local comparisons used to propagate incentive compatibility
along a priority ordering. -/
theorem nonpreemptivePriority_adjacentPriceGap_sub_lowerDelayGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hslackBefore : slackBefore ≠ 0) (hslackHere : slackHere ≠ 0)
    (hslackAfter : slackAfter ≠ 0)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    (arrivalHere * delayCostHere *
        (residual / (slackBefore * slackHere)) +
      arrivalAfter * delayCostAfter *
        (residual / (slackHere * slackAfter))) / slackHere -
      delayCostAfter *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) =
      residual * arrivalHere * (delayCostHere - delayCostAfter) /
        (slackBefore * slackHere ^ 2) := by
  field_simp
  rw [hbefore, hafter]
  ring

/-- The lower-priority class's adjacent single-crossing inequality.  It is
weak at zero-flow or zero-residual boundaries, and becomes strict under the
corresponding positive hypotheses. -/
theorem nonpreemptivePriority_adjacentDelayGap_le_priceGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hresidual : 0 ≤ residual) (hslackBefore : 0 < slackBefore)
    (hslackHere : 0 < slackHere) (hslackAfter : 0 < slackAfter)
    (harrivalHere : 0 ≤ arrivalHere)
    (hdelayCost : delayCostAfter ≤ delayCostHere)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    delayCostAfter *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) ≤
      (arrivalHere * delayCostHere *
          (residual / (slackBefore * slackHere)) +
        arrivalAfter * delayCostAfter *
          (residual / (slackHere * slackAfter))) / slackHere := by
  have hgap := nonpreemptivePriority_adjacentPriceGap_sub_lowerDelayGap
    residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
    delayCostHere delayCostAfter (ne_of_gt hslackBefore) (ne_of_gt hslackHere)
    (ne_of_gt hslackAfter) hbefore hafter
  have hnonnegative :
      0 ≤ residual * arrivalHere * (delayCostHere - delayCostAfter) /
        (slackBefore * slackHere ^ 2) := by
    apply div_nonneg
    · exact mul_nonneg (mul_nonneg hresidual harrivalHere) (sub_nonneg.mpr hdelayCost)
    · exact mul_nonneg (le_of_lt hslackBefore) (sq_nonneg slackHere)
  linarith

/-- Strict lower-priority single crossing.  When the residual work, the
higher-priority neighboring flow, and the delay-cost gap are positive, the
lower-priority class strictly prefers its own adjacent level. -/
theorem nonpreemptivePriority_adjacentDelayGap_lt_priceGap
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hresidual : 0 < residual) (hslackBefore : 0 < slackBefore)
    (hslackHere : 0 < slackHere) (hslackAfter : 0 < slackAfter)
    (harrivalHere : 0 < arrivalHere)
    (hdelayCost : delayCostAfter < delayCostHere)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    delayCostAfter *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) <
      (arrivalHere * delayCostHere *
          (residual / (slackBefore * slackHere)) +
        arrivalAfter * delayCostAfter *
          (residual / (slackHere * slackAfter))) / slackHere := by
  have hgap := nonpreemptivePriority_adjacentPriceGap_sub_lowerDelayGap
    residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
    delayCostHere delayCostAfter (ne_of_gt hslackBefore) (ne_of_gt hslackHere)
    (ne_of_gt hslackAfter) hbefore hafter
  have hpositive :
      0 < residual * arrivalHere * (delayCostHere - delayCostAfter) /
        (slackBefore * slackHere ^ 2) := by
    apply div_pos
    · exact mul_pos (mul_pos hresidual harrivalHere) (sub_pos.mpr hdelayCost)
    · exact mul_pos hslackBefore (sq_pos_of_pos hslackHere)
  linarith

/-- At a zero neighboring arrival rate, the adjacent comparison in
`nonpreemptivePriority_adjacentPriceGap_lt_delayGap` becomes an equality.
This records the boundary case separately from the strict single-crossing
result. -/
theorem nonpreemptivePriority_adjacentPriceGap_eq_delayGap_of_zeroArrival
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter
      delayCostHere delayCostAfter : ℝ)
    (hslackBefore : slackBefore ≠ 0) (hslackHere : slackHere ≠ 0)
    (hslackAfter : slackAfter ≠ 0)
    (harrivalAfter : arrivalAfter = 0)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    (arrivalHere * delayCostHere *
        (residual / (slackBefore * slackHere)) +
      arrivalAfter * delayCostAfter *
        (residual / (slackHere * slackAfter))) / slackHere =
      delayCostHere *
        (residual / (slackHere * slackAfter) -
          residual / (slackBefore * slackHere)) := by
  subst arrivalAfter
  simp only [add_zero] at hafter ⊢
  field_simp
  rw [hbefore, hafter]
  ring

/-- Queueing time weakly increases when moving one level toward lower
priority, under nonnegative adjacent loads and positive slacks. -/
theorem nonpreemptivePriority_adjacentQueueWait_le
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter : ℝ)
    (hresidual : 0 ≤ residual) (hslackHere : 0 < slackHere)
    (hslackAfter : 0 < slackAfter)
    (harrivalHere : 0 ≤ arrivalHere) (harrivalAfter : 0 ≤ arrivalAfter)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    residual / (slackBefore * slackHere) ≤
      residual / (slackHere * slackAfter) := by
  have hbefore_ge : slackHere ≤ slackBefore := by
    rw [hbefore]
    linarith
  have hafter_ge : slackAfter ≤ slackHere := by
    rw [hafter]
    linarith
  have hdenominator : slackHere * slackAfter ≤ slackBefore * slackHere := by
    calc
      slackHere * slackAfter ≤ slackHere * slackHere :=
        mul_le_mul_of_nonneg_left hafter_ge hslackHere.le
      _ ≤ slackBefore * slackHere :=
        mul_le_mul_of_nonneg_right hbefore_ge hslackHere.le
  exact div_le_div_of_nonneg_left hresidual
    (mul_pos hslackHere hslackAfter) hdenominator

/-- Queueing time strictly increases across adjacent priority levels when
residual work and both adjacent loads are positive. -/
theorem nonpreemptivePriority_adjacentQueueWait_lt
    (residual slackBefore slackHere slackAfter arrivalHere arrivalAfter : ℝ)
    (hresidual : 0 < residual) (hslackBefore : 0 < slackBefore)
    (hslackHere : 0 < slackHere) (hslackAfter : 0 < slackAfter)
    (harrivalHere : 0 < arrivalHere) (harrivalAfter : 0 < arrivalAfter)
    (hbefore : slackBefore = slackHere + arrivalHere)
    (hafter : slackHere = slackAfter + arrivalAfter) :
    residual / (slackBefore * slackHere) <
      residual / (slackHere * slackAfter) := by
  have hgap :
      residual / (slackHere * slackAfter) -
        residual / (slackBefore * slackHere) =
      residual * (arrivalHere + arrivalAfter) /
        (slackBefore * slackHere * slackAfter) := by
    field_simp [ne_of_gt hslackBefore, ne_of_gt hslackHere, ne_of_gt hslackAfter]
    rw [hbefore, hafter]
    ring
  have hpositive : 0 <
      residual * (arrivalHere + arrivalAfter) /
        (slackBefore * slackHere * slackAfter) := by
    apply div_pos
    · exact mul_pos hresidual (add_pos harrivalHere harrivalAfter)
    · exact mul_pos (mul_pos hslackBefore hslackHere) hslackAfter
  linarith

/-- A one-step single-crossing transitivity rule when moving toward higher
priority levels: a lower-delay-cost type inherits a middle type's preference
between two faster classes. -/
theorem priorityCost_transitive_towardHigherPriority
    (priceI priceJ priceK delayCostI delayCostJ
      waitI waitJ waitK : ℝ)
    (hdelayCost : delayCostI ≤ delayCostJ)
    (hwaiting : waitK ≤ waitJ)
    (hfirst : priceI + delayCostI * waitI ≤ priceJ + delayCostI * waitJ)
    (hsecond : priceJ + delayCostJ * waitJ ≤ priceK + delayCostJ * waitK) :
    priceI + delayCostI * waitI ≤ priceK + delayCostI * waitK := by
  have hproduct : 0 ≤ (delayCostJ - delayCostI) * (waitJ - waitK) :=
    mul_nonneg (sub_nonneg.mpr hdelayCost) (sub_nonneg.mpr hwaiting)
  have hmiddle : priceJ + delayCostI * waitJ ≤
      priceK + delayCostI * waitK := by
    nlinarith
  exact hfirst.trans hmiddle

/-- Strict one-step single-crossing transitivity toward higher priority. -/
theorem priorityCost_transitive_towardHigherPriority_lt
    (priceI priceJ priceK delayCostI delayCostJ
      waitI waitJ waitK : ℝ)
    (hdelayCost : delayCostI ≤ delayCostJ)
    (hwaiting : waitK ≤ waitJ)
    (hfirst : priceI + delayCostI * waitI < priceJ + delayCostI * waitJ)
    (hsecond : priceJ + delayCostJ * waitJ ≤ priceK + delayCostJ * waitK) :
    priceI + delayCostI * waitI < priceK + delayCostI * waitK := by
  have hproduct : 0 ≤ (delayCostJ - delayCostI) * (waitJ - waitK) :=
    mul_nonneg (sub_nonneg.mpr hdelayCost) (sub_nonneg.mpr hwaiting)
  have hmiddle : priceJ + delayCostI * waitJ ≤
      priceK + delayCostI * waitK := by
    nlinarith
  exact hfirst.trans_le hmiddle

/-- The symmetric one-step single-crossing transitivity rule when moving
toward lower priority levels. -/
theorem priorityCost_transitive_towardLowerPriority
    (priceI priceJ priceK delayCostI delayCostJ
      waitI waitJ waitK : ℝ)
    (hdelayCost : delayCostJ ≤ delayCostI)
    (hwaiting : waitJ ≤ waitK)
    (hfirst : priceI + delayCostI * waitI ≤ priceJ + delayCostI * waitJ)
    (hsecond : priceJ + delayCostJ * waitJ ≤ priceK + delayCostJ * waitK) :
    priceI + delayCostI * waitI ≤ priceK + delayCostI * waitK := by
  have hproduct : 0 ≤ (delayCostI - delayCostJ) * (waitK - waitJ) :=
    mul_nonneg (sub_nonneg.mpr hdelayCost) (sub_nonneg.mpr hwaiting)
  have hmiddle : priceJ + delayCostI * waitJ ≤
      priceK + delayCostI * waitK := by
    nlinarith
  exact hfirst.trans hmiddle

/-- Strict one-step single-crossing transitivity toward lower priority. -/
theorem priorityCost_transitive_towardLowerPriority_lt
    (priceI priceJ priceK delayCostI delayCostJ
      waitI waitJ waitK : ℝ)
    (hdelayCost : delayCostJ ≤ delayCostI)
    (hwaiting : waitJ ≤ waitK)
    (hfirst : priceI + delayCostI * waitI < priceJ + delayCostI * waitJ)
    (hsecond : priceJ + delayCostJ * waitJ ≤ priceK + delayCostJ * waitK) :
    priceI + delayCostI * waitI < priceK + delayCostI * waitK := by
  have hproduct : 0 ≤ (delayCostI - delayCostJ) * (waitK - waitJ) :=
    mul_nonneg (sub_nonneg.mpr hdelayCost) (sub_nonneg.mpr hwaiting)
  have hmiddle : priceJ + delayCostI * waitJ ≤
      priceK + delayCostI * waitK := by
    nlinarith
  exact hfirst.trans_le hmiddle

end Queueing
end AppliedModelingLib
