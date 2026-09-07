import AppliedModelingLib.Queueing.NonpreemptivePriorityClassDependentUniformization

/-!
# Second-moment increments for class-dependent priority queues

This module records the bounded-increment calculation needed to strengthen
the finite-start busy-period estimates for an exponential multiclass priority
queue.  It is entirely about the literal uniformized transition and does not
assume a stationary distribution.
-/

namespace AppliedModelingLib.Queueing

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- A uniform upper bound on the absolute change in weighted mean work at one
class-dependent arrival-or-potential-completion event. -/
noncomputable def classDependentNonpreemptivePriorityMeanWorkStepBound
    {n : ℕ} (meanService : Fin n → ℝ) : ℝ :=
  ∑ i, meanService i

/-- A positive class-mean vector makes its total a nonnegative one-event work
bound. -/
theorem classDependentNonpreemptivePriorityMeanWorkStepBound_nonneg
    {n : ℕ} (meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 ≤ meanService i) :
    0 ≤ classDependentNonpreemptivePriorityMeanWorkStepBound meanService := by
  unfold classDependentNonpreemptivePriorityMeanWorkStepBound
  exact Finset.sum_nonneg fun i _ => hmeanService i

/-- Every individual class mean is bounded by the finite total used for a
single transition. -/
theorem meanService_le_classDependentNonpreemptivePriorityMeanWorkStepBound
    {n : ℕ} (meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 ≤ meanService i) (i : Fin n) :
    meanService i ≤ classDependentNonpreemptivePriorityMeanWorkStepBound meanService := by
  unfold classDependentNonpreemptivePriorityMeanWorkStepBound
  exact Finset.univ.single_le_sum (fun j _ => hmeanService j) (Finset.mem_univ i)

/-- The weighted mean work changes by no more than the sum of class means at
one uniformized event.  An inactive potential-completion clock is a self-loop,
which is why the same bound covers both event kinds. -/
theorem abs_nonpreemptivePriorityMeanWork_stepClassDependent_sub_le
    {n : ℕ} (meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 ≤ meanService i)
    (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    |nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event) -
      nonpreemptivePriorityMeanWork meanService state| ≤
      classDependentNonpreemptivePriorityMeanWorkStepBound meanService := by
  cases event with
  | inl i =>
      rw [nonpreemptivePriorityMeanWork_stepClassDependent_arrival]
      simp only [add_sub_cancel_left, abs_of_nonneg (hmeanService i)]
      exact meanService_le_classDependentNonpreemptivePriorityMeanWorkStepBound
        meanService hmeanService i
  | inr i =>
      by_cases hactive : state.active = some i
      · have hcompletion :=
          nonpreemptivePriorityMeanWork_stepClassDependent_completion_of_active
            meanService state i hactive
        have hchange : nonpreemptivePriorityMeanWork meanService
            (stepClassDependentNonpreemptivePriority state (.inr i)) -
            nonpreemptivePriorityMeanWork meanService state = - meanService i := by
          linarith
        rw [hchange, abs_neg, abs_of_nonneg (hmeanService i)]
        exact meanService_le_classDependentNonpreemptivePriorityMeanWorkStepBound
          meanService hmeanService i
      · rw [stepClassDependentNonpreemptivePriority_completion_of_inactive
          state i hactive]
        simp [classDependentNonpreemptivePriorityMeanWorkStepBound_nonneg
          meanService hmeanService]

/-- Squaring the preceding bounded increment gives a uniform quadratic
one-event remainder bound. -/
theorem sq_nonpreemptivePriorityMeanWork_stepClassDependent_sub_le
    {n : ℕ} (meanService : Fin n → ℝ)
    (hmeanService : ∀ i, 0 ≤ meanService i)
    (state : NonpreemptivePriorityState n)
    (event : ClassDependentNonpreemptivePriorityEvent n) :
    (nonpreemptivePriorityMeanWork meanService
        (stepClassDependentNonpreemptivePriority state event) -
      nonpreemptivePriorityMeanWork meanService state) ^ 2 ≤
      (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 := by
  rw [sq_le_sq]
  simpa [abs_of_nonneg
    (classDependentNonpreemptivePriorityMeanWorkStepBound_nonneg meanService hmeanService)] using
    (abs_nonpreemptivePriorityMeanWork_stepClassDependent_sub_le
      meanService hmeanService state event)

/-- In a busy state, the one-step quadratic mean-work drift is controlled by
twice the usual linear drift plus the squared bounded-increment remainder.
This is the finite-state calculation behind a second-moment busy-period
Lyapunov estimate. -/
theorem pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sq_sub_le
    {n : ℕ} (arrivalRate meanService : Fin n → ℝ)
    (hn : 0 < n) (harrivalRate : ∀ i, 0 ≤ arrivalRate i)
    (hmeanService : ∀ i, 0 < meanService i)
    (state : NonpreemptivePriorityState n) :
    let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
      (exponentialServiceRate meanService) hn harrivalRate
      (exponentialServiceRate_pos meanService hmeanService)
    let V := nonpreemptivePriorityMeanWork meanService
    pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event) ^ 2) -
      V state ^ 2 ≤
      2 * V state *
        (classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state /
          ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)) +
        (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 := by
  dsimp only
  let law := classDependentNonpreemptivePriorityEventPMF arrivalRate
    (exponentialServiceRate meanService) hn harrivalRate
    (exponentialServiceRate_pos meanService hmeanService)
  let V := nonpreemptivePriorityMeanWork meanService
  let delta : ClassDependentNonpreemptivePriorityEvent n → ℝ :=
    fun event => V (stepClassDependentNonpreemptivePriority state event) - V state
  have hpoint : ∀ event, V (stepClassDependentNonpreemptivePriority state event) ^ 2 =
      2 * V state * delta event + delta event ^ 2 + V state ^ 2 := by
    intro event
    dsimp [delta]
    ring
  have hquadratic : pmfExp law (fun event => delta event ^ 2) ≤
      (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 := by
    calc
      pmfExp law (fun event => delta event ^ 2) ≤
          pmfExp law (fun _ =>
            (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2) := by
              apply pmfExp_le_pmfExp_of_forall_le
              intro event
              exact sq_nonpreemptivePriorityMeanWork_stepClassDependent_sub_le
                meanService (fun i => (hmeanService i).le) state event
      _ = (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 := by
        simp
  have hlinear : pmfExp law delta =
      classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state /
        ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i) := by
    change pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event) -
      V state) = _
    rw [pmfExp_sub, pmfExp_const]
    exact pmfExp_classDependentNonpreemptivePriorityEvent_meanWork_sub_eq_rateDrift_div
      arrivalRate meanService hn harrivalRate hmeanService state
  calc
    pmfExp law (fun event => V (stepClassDependentNonpreemptivePriority state event) ^ 2) -
        V state ^ 2 =
        pmfExp law (fun event =>
          2 * V state * delta event + delta event ^ 2 + V state ^ 2) - V state ^ 2 := by
          congr 2
          funext event
          exact hpoint event
    _ = 2 * V state * pmfExp law delta + pmfExp law (fun event => delta event ^ 2) := by
          rw [pmfExp_add, pmfExp_add, pmfExp_const_mul, pmfExp_const]
          ring
    _ ≤ 2 * V state *
          (classDependentNonpreemptivePriorityMeanWorkRateDrift arrivalRate meanService state /
            ((∑ i, arrivalRate i) + ∑ i, exponentialServiceRate meanService i)) +
          (classDependentNonpreemptivePriorityMeanWorkStepBound meanService) ^ 2 := by
          rw [hlinear]
          linarith

end

end AppliedModelingLib.Queueing
