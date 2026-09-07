import LG24ServiceLevelAgreements.SLA2026TaggedAdmittedGPSDiagonalResponse
import Mathlib.Tactic

/-!
# Eventual geometry of the diagonal GPS windows

The literal tagged GPS replays use the deterministic windows `[-N, N + 1)`.
This small adapter records their only asymptotic property needed by the
stationary tail construction: any fixed finite left boundary and deadline are
both contained in every sufficiently large diagonal window.  It carries no
queueing, source, or measurability claim.
-/

namespace LG24ServiceLevelAgreements

open Filter

noncomputable section

namespace SLA2026BoroughQueueingInput

/-- Every fixed finite time is eventually to the right of the diagonal left
endpoint. -/
theorem eventually_taggedAdmittedGPSDiagonalStart_le (time : ℝ) :
    ∀ᶠ N : ℕ in atTop, taggedAdmittedGPSDiagonalStart N ≤ time := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge (-time)
  refine Filter.eventually_atTop.2 ⟨threshold, ?_⟩
  intro N hN
  have hcast : (threshold : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have htime : -time ≤ (N : ℝ) := hthreshold.trans hcast
  dsimp [taggedAdmittedGPSDiagonalStart]
  linarith

/-- Every fixed finite time is eventually no later than the diagonal right
endpoint. -/
theorem eventually_le_taggedAdmittedGPSDiagonalHorizon (time : ℝ) :
    ∀ᶠ N : ℕ in atTop, time ≤ taggedAdmittedGPSDiagonalHorizon N := by
  obtain ⟨threshold, hthreshold⟩ := exists_nat_ge time
  refine Filter.eventually_atTop.2 ⟨threshold, ?_⟩
  intro N hN
  have hcast : (threshold : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have htime : time ≤ (N : ℝ) := hthreshold.trans hcast
  dsimp [taggedAdmittedGPSDiagonalHorizon]
  linarith

/-- Any prescribed reset boundary and comparator deadline lie in all
sufficiently large diagonal windows. -/
theorem eventually_taggedAdmittedGPSDiagonal_contains
    (resetTime deadline : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      taggedAdmittedGPSDiagonalStart N ≤ resetTime ∧
        deadline ≤ taggedAdmittedGPSDiagonalHorizon N := by
  filter_upwards [eventually_taggedAdmittedGPSDiagonalStart_le resetTime,
    eventually_le_taggedAdmittedGPSDiagonalHorizon deadline] with N hstart hhorizon
  exact ⟨hstart, hhorizon⟩

end SLA2026BoroughQueueingInput

end

end LG24ServiceLevelAgreements
