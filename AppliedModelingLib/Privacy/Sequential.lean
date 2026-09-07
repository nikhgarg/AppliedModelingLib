import AppliedModelingLib.Privacy.KL

/-!
# Adaptive sequential stability

A finite state may encode the complete interaction transcript.  Thus a
state-dependent transition kernel covers adaptively selected queries without
requiring an independence assumption between rounds.
-/

namespace AppliedModelingLib.Privacy

section Sequential

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- The law after repeatedly applying a state-dependent finite transition
kernel.  Taking `State` to be a transcript carrier models adaptive rounds. -/
noncomputable def sequentialLaw (initial : PMF State) (transition : State → PMF State) :
    ℕ → PMF State
  | 0 => initial
  | steps + 1 => (sequentialLaw initial transition steps).bind transition

@[simp] theorem sequentialLaw_zero (initial : PMF State) (transition : State → PMF State) :
    sequentialLaw initial transition 0 = initial := rfl

@[simp] theorem sequentialLaw_succ (initial : PMF State) (transition : State → PMF State)
    (steps : ℕ) :
    sequentialLaw initial transition (steps + 1) =
      (sequentialLaw initial transition steps).bind transition := rfl

/-- If every state-dependent transition is TV-close, then applying a close
input law and changing the transition costs the sum of the two TV budgets. -/
theorem TVClose.bind_of_pointwise
    {epsilonInput epsilonKernel : ℝ} {first second : PMF State}
    (hinput : TVClose epsilonInput first second)
    (firstKernel secondKernel : State → PMF State)
    (hkernel : ∀ state, TVClose epsilonKernel (firstKernel state) (secondKernel state)) :
    TVClose (epsilonInput + epsilonKernel)
      (first.bind firstKernel) (second.bind secondKernel) := by
  apply (hinput.bind firstKernel).triangle
  have hjoint := TVClose.kernelJoint second firstKernel secondKernel hkernel
  have hmarginal := hjoint.map Prod.snd
  change TVClose epsilonKernel
    (pmfKernelSignalMarginal second firstKernel)
    (pmfKernelSignalMarginal second secondKernel) at hmarginal
  rw [pmfKernelSignalMarginal_eq_bind, pmfKernelSignalMarginal_eq_bind] at hmarginal
  exact hmarginal

/-- TV stability composes linearly for state-dependent (hence adaptive)
finite transitions. -/
theorem sequentialLaw_tvClose
    (initial : PMF State) (firstTransition secondTransition : State → PMF State)
    (epsilon : ℝ)
    (htransition : ∀ state, TVClose epsilon (firstTransition state) (secondTransition state)) :
    ∀ steps : ℕ,
      TVClose ((steps : ℝ) * epsilon)
        (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) := by
  intro steps
  induction steps with
  | zero =>
      intro event
      simp [sequentialLaw]
  | succ steps ih =>
      rw [sequentialLaw_succ, sequentialLaw_succ]
      have hstep := ih.bind_of_pointwise firstTransition secondTransition htransition
      convert hstep using 1
      push_cast
      ring

/-- Absolute continuity propagates through a finite adaptive sequence. -/
theorem sequentialLaw_absoluteContinuous
    (initial : PMF State) (firstTransition secondTransition : State → PMF State)
    (htransition : ∀ state,
      PMFAbsoluteContinuous (firstTransition state) (secondTransition state)) :
    ∀ steps : ℕ,
      PMFAbsoluteContinuous (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) := by
  intro steps
  induction steps with
  | zero =>
      intro state hstate
      exact hstate
  | succ steps ih =>
      rw [sequentialLaw_succ, sequentialLaw_succ]
      exact ih.bind_of_pointwise firstTransition secondTransition htransition

/-- KL stability composes with the square-root parameter: the KL budgets add
along an adaptive transcript, and the source's `2 ε²` convention converts
that additive budget to `ε √k`. -/
theorem sequentialLaw_klClose
    (initial : PMF State) (firstTransition secondTransition : State → PMF State)
    (epsilon : ℝ)
    (htransition : ∀ state, KLClose epsilon (firstTransition state) (secondTransition state)) :
    ∀ steps : ℕ,
      KLClose (epsilon * Real.sqrt (steps : ℝ))
        (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) := by
  intro steps
  have hac : ∀ steps : ℕ,
      PMFAbsoluteContinuous (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) :=
    sequentialLaw_absoluteContinuous initial firstTransition secondTransition
      (fun state => (htransition state).1)
  have hbound : ∀ steps : ℕ,
      finiteKLDivergence
        (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) ≤
        2 * epsilon ^ 2 * (steps : ℝ) := by
    intro steps
    induction steps with
    | zero =>
        simp [sequentialLaw]
    | succ steps ih =>
        rw [sequentialLaw_succ, sequentialLaw_succ]
        calc
          finiteKLDivergence
              ((sequentialLaw initial firstTransition steps).bind firstTransition)
              ((sequentialLaw initial secondTransition steps).bind secondTransition) ≤
              finiteKLDivergence
                (sequentialLaw initial firstTransition steps)
                (sequentialLaw initial secondTransition steps) +
                pmfExp (sequentialLaw initial firstTransition steps) (fun state =>
                  finiteKLDivergence (firstTransition state) (secondTransition state)) :=
            finiteKLDivergence_bind_le_add_expected
              (sequentialLaw initial firstTransition steps)
              (sequentialLaw initial secondTransition steps) (hac steps)
              firstTransition secondTransition (fun state => (htransition state).1)
          _ ≤ 2 * epsilon ^ 2 * (steps : ℝ) + 2 * epsilon ^ 2 := by
            refine add_le_add ih ?_
            calc
              pmfExp (sequentialLaw initial firstTransition steps) (fun state =>
                  finiteKLDivergence (firstTransition state) (secondTransition state)) ≤
                  pmfExp (sequentialLaw initial firstTransition steps)
                    (fun _ => 2 * epsilon ^ 2) :=
                pmfExp_le_pmfExp_of_forall_le _ _ _ (fun state => (htransition state).2)
              _ = 2 * epsilon ^ 2 := pmfExp_const _ _
          _ = 2 * epsilon ^ 2 * ((steps + 1 : ℕ) : ℝ) := by
            push_cast
            ring
  refine ⟨hac steps, ?_⟩
  calc
    finiteKLDivergence (sequentialLaw initial firstTransition steps)
        (sequentialLaw initial secondTransition steps) ≤
        2 * epsilon ^ 2 * (steps : ℝ) := hbound steps
    _ = 2 * (epsilon * Real.sqrt (steps : ℝ)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (steps : ℝ))]
      ring

end Sequential

end AppliedModelingLib.Privacy
