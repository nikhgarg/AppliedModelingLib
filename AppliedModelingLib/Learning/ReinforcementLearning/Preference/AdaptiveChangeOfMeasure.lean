import AppliedModelingLib.Learning.ReinforcementLearning.Preference.RewardAgnostic
import Mathlib.Tactic

/-!
# Finite adaptive change of measure

Finite-state adaptive executions can be represented by a time-indexed kernel
on their complete current state.  This module propagates atomwise density
bounds through that execution, without imposing independence between stages.
-/

namespace AppliedModelingLib

namespace PreferenceRL

open scoped BigOperators

/-- The finite-state law of an execution whose next-state kernel may depend on
the complete current state and the absolute step. -/
noncomputable def adaptiveTransitionStateLaw
    {State : Type*} [Fintype State] [DecidableEq State]
    (initial : PMF State) (transition : ℕ → State → PMF State) : ℕ → PMF State
  | 0 => initial
  | step + 1 =>
      (adaptiveTransitionStateLaw initial transition step).bind (transition step)

/--
Atomwise density bounds on an input law and its next-state kernel multiply
through one finite PMF bind.
-/
theorem pmfBind_apply_toReal_le_mul_of_atomBounds
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (targetInput referenceInput : PMF Input)
    (targetKernel referenceKernel : Input → PMF Output)
    (inputDensity kernelDensity : ℝ)
    (hinput : ∀ input,
      (targetInput input).toReal ≤ inputDensity * (referenceInput input).toReal)
    (hkernel : ∀ input output,
      (targetKernel input output).toReal ≤
        kernelDensity * (referenceKernel input output).toReal)
    (hinputDensity : 0 ≤ inputDensity)
    (output : Output) :
    ((targetInput.bind targetKernel) output).toReal ≤
      (inputDensity * kernelDensity) *
        ((referenceInput.bind referenceKernel) output).toReal := by
  classical
  rw [pmfBind_apply_toReal, pmfBind_apply_toReal]
  calc
    (∑ input : Input,
        (targetInput input).toReal * (targetKernel input output).toReal) ≤
        ∑ input : Input,
          (inputDensity * (referenceInput input).toReal) *
            (kernelDensity * (referenceKernel input output).toReal) := by
          apply Finset.sum_le_sum
          intro input _
          calc
            (targetInput input).toReal * (targetKernel input output).toReal ≤
                (inputDensity * (referenceInput input).toReal) *
                  (targetKernel input output).toReal := by
                    exact mul_le_mul_of_nonneg_right (hinput input)
                      ENNReal.toReal_nonneg
            _ ≤ (inputDensity * (referenceInput input).toReal) *
                  (kernelDensity * (referenceKernel input output).toReal) := by
                    exact mul_le_mul_of_nonneg_left (hkernel input output)
                      (mul_nonneg hinputDensity ENNReal.toReal_nonneg)
    _ = ∑ input : Input,
          (inputDensity * kernelDensity) *
            ((referenceInput input).toReal *
              (referenceKernel input output).toReal) := by
          apply Finset.sum_congr rfl
          intro input _
          ring
    _ = (inputDensity * kernelDensity) *
          ∑ input : Input,
            (referenceInput input).toReal * (referenceKernel input output).toReal := by
          rw [Finset.mul_sum]

/-- Atomwise density bounds are preserved by a deterministic state update. -/
theorem pmfMap_apply_toReal_le_mul_of_atomBounds
    {Input Output : Type*} [Fintype Input] [DecidableEq Input]
    [Fintype Output] [DecidableEq Output]
    (targetInput referenceInput : PMF Input) (update : Input → Output)
    (density : ℝ)
    (hatom : ∀ input,
      (targetInput input).toReal ≤ density * (referenceInput input).toReal)
    (hdensity : 0 ≤ density) (output : Output) :
    ((targetInput.map update) output).toReal ≤
      density * ((referenceInput.map update) output).toReal := by
  change ((targetInput.bind (PMF.pure ∘ update)) output).toReal ≤
    density * ((referenceInput.bind (PMF.pure ∘ update)) output).toReal
  simpa [Function.comp_def] using
    (pmfBind_apply_toReal_le_mul_of_atomBounds
      targetInput referenceInput (PMF.pure ∘ update) (PMF.pure ∘ update)
      density 1 hatom (by
        intro input nextState
        simp) hdensity output)

/--
For a finite adaptive execution, stagewise atomwise density bounds multiply
over the execution length.  A state may encode the complete prior history, so
this makes no independence assumption between adaptively chosen stages.
-/
theorem adaptiveTransitionStateLaw_atomBound
    {State : Type*} [Fintype State] [DecidableEq State]
    (targetInitial referenceInitial : PMF State)
    (targetTransition referenceTransition : ℕ → State → PMF State)
    (stageDensity : ℕ → ℝ)
    (hinitial : ∀ state,
      (targetInitial state).toReal ≤ (referenceInitial state).toReal)
    (htransition : ∀ step state nextState,
      (targetTransition step state nextState).toReal ≤
        stageDensity step * (referenceTransition step state nextState).toReal)
    (hdensity : ∀ step, 0 ≤ stageDensity step) :
    ∀ steps state,
      (adaptiveTransitionStateLaw targetInitial targetTransition steps state).toReal ≤
        (∏ step ∈ Finset.range steps, stageDensity step) *
          (adaptiveTransitionStateLaw referenceInitial referenceTransition steps state).toReal := by
  intro steps
  induction steps with
  | zero =>
      intro state
      simpa [adaptiveTransitionStateLaw] using hinitial state
  | succ steps ih =>
      intro state
      have hprefixNonneg : 0 ≤ ∏ step ∈ Finset.range steps, stageDensity step :=
        Finset.prod_nonneg (fun step hstep => hdensity step)
      calc
        (adaptiveTransitionStateLaw targetInitial targetTransition (steps + 1) state).toReal =
            ((adaptiveTransitionStateLaw targetInitial targetTransition steps).bind
              (targetTransition steps) state).toReal := by
                rfl
        _ ≤ ((∏ step ∈ Finset.range steps, stageDensity step) * stageDensity steps) *
              ((adaptiveTransitionStateLaw referenceInitial referenceTransition steps).bind
                (referenceTransition steps) state).toReal := by
              exact pmfBind_apply_toReal_le_mul_of_atomBounds
                (adaptiveTransitionStateLaw targetInitial targetTransition steps)
                (adaptiveTransitionStateLaw referenceInitial referenceTransition steps)
                (targetTransition steps) (referenceTransition steps)
                (∏ step ∈ Finset.range steps, stageDensity step) (stageDensity steps)
                ih (htransition steps) hprefixNonneg state
        _ = (∏ step ∈ Finset.range (steps + 1), stageDensity step) *
              (adaptiveTransitionStateLaw referenceInitial referenceTransition
                (steps + 1) state).toReal := by
              rw [Finset.prod_range_succ]
              rfl

end PreferenceRL

end AppliedModelingLib
