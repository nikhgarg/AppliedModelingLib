/-!
# Ordered recursions driven by common noise

This module gives the deterministic induction principle behind pathwise
couplings of discrete-time processes.  Two recursions exposed to the same
noise path remain ordered when their one-step updates preserve the relevant
cross-state order.  The result is independent of probability laws; a later
kernel construction supplies the common noise and its law.
-/

namespace AppliedModelingLib.Probability

/-- The trajectory generated from an initial state by a time-homogeneous
update map and a prescribed noise path. -/
def drivenRecursion {α ξ : Type*} (update : α → ξ → α) (initial : α)
    (noise : ℕ → ξ) : ℕ → α
  | 0 => initial
  | index + 1 => update (drivenRecursion update initial noise index) (noise index)

/-- The driven recursion starts from its supplied initial state. -/
@[simp]
theorem drivenRecursion_zero {α ξ : Type*} (update : α → ξ → α) (initial : α)
    (noise : ℕ → ξ) :
    drivenRecursion update initial noise 0 = initial :=
  rfl

/-- The driven recursion advances by one application of its update map. -/
@[simp]
theorem drivenRecursion_succ {α ξ : Type*} (update : α → ξ → α) (initial : α)
    (noise : ℕ → ξ) (index : ℕ) :
    drivenRecursion update initial noise (index + 1) =
      update (drivenRecursion update initial noise index) (noise index) :=
  rfl

/-- A fixed update map that is monotone in its state coordinate preserves the
order of two trajectories driven by the same noise path. -/
theorem drivenRecursion_le_of_monotone
    {α ξ : Type*} [Preorder α] (update : α → ξ → α)
    (hupdate : ∀ noiseValue : ξ, Monotone (fun state : α => update state noiseValue))
    {lowerInitial upperInitial : α} (hinitial : lowerInitial ≤ upperInitial)
    (noise : ℕ → ξ) (index : ℕ) :
    drivenRecursion update lowerInitial noise index ≤
      drivenRecursion update upperInitial noise index := by
  induction index with
  | zero => simpa using hinitial
  | succ index inductionHypothesis =>
      rw [drivenRecursion_succ, drivenRecursion_succ]
      exact hupdate (noise index) inductionHypothesis

/-- Two update maps preserve a pathwise order under common noise when every
lower update at a lower state is below the corresponding upper update at an
upper state. -/
theorem drivenRecursion_le_of_cross_monotone
    {α ξ : Type*} [Preorder α]
    (lowerUpdate upperUpdate : α → ξ → α)
    (hupdate : ∀ stateLower stateUpper : α, ∀ noiseValue : ξ,
      stateLower ≤ stateUpper →
        lowerUpdate stateLower noiseValue ≤ upperUpdate stateUpper noiseValue)
    {lowerInitial upperInitial : α} (hinitial : lowerInitial ≤ upperInitial)
    (noise : ℕ → ξ) (index : ℕ) :
    drivenRecursion lowerUpdate lowerInitial noise index ≤
      drivenRecursion upperUpdate upperInitial noise index := by
  induction index with
  | zero => simpa using hinitial
  | succ index inductionHypothesis =>
      rw [drivenRecursion_succ, drivenRecursion_succ]
      exact hupdate _ _ (noise index) inductionHypothesis

end AppliedModelingLib.Probability
