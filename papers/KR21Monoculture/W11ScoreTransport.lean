import KR21Monoculture.Basic
import AppliedModelingLib.SocialChoice.Ranking.Score

open AppliedModelingLib
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Positive score scaling for the corrected Theorem 5 route

The paper's scaled-noise scores
`value i + noise i / theta` and the additive score-space representation
`theta * value i + noise i` differ by multiplication by the positive scalar
`theta`.  This module proves that this preserves `rankByScore` exactly,
including the deterministic lower-index tie breaking built into `Tuple.sort`.
It makes no probability-law or change-of-variables assertion.
-/

/-- Positive rescaling leaves the canonical score ranking unchanged, including ties. -/
theorem rankByScore_pos_scale
    {n : ℕ} (score : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    rankByScore (fun i => theta * score i) = rankByScore score := by
  classical
  let pi : Ranking n := rankByScore score
  have hpi : pi = Tuple.sort (fun i : Candidate n => -score i) := by
    rfl
  have hsorted :
      Monotone ((fun i : Candidate n => -score i) ∘ pi) := by
    simpa [pi] using Tuple.monotone_sort (fun i : Candidate n => -score i)
  have htied :
      ∀ i j : Candidate n, i < j →
        ((fun c : Candidate n => -score c) ∘ pi) i =
            ((fun c : Candidate n => -score c) ∘ pi) j →
          pi i < pi j := by
    intro i j hij heq
    exact
      (Tuple.eq_sort_iff (f := fun c : Candidate n => -score c) (σ := pi)).mp hpi |>.2
        i j hij heq
  have hscale :
      ∀ i : Candidate n, -(theta * score i) = theta * (-score i) := by
    intro i
    ring
  have hpi_scaled : pi = Tuple.sort (fun i : Candidate n => -(theta * score i)) := by
    apply (Tuple.eq_sort_iff (f := fun i : Candidate n => -(theta * score i)
      ) (σ := pi)).mpr
    constructor
    · intro i j hij
      rw [Function.comp_apply, Function.comp_apply, hscale, hscale]
      exact mul_le_mul_of_nonneg_left (hsorted hij) (le_of_lt htheta)
    · intro i j hij heq
      apply htied i j hij
      change -score (pi i) = -score (pi j)
      rw [hscale (pi i), hscale (pi j)] at heq
      exact (mul_left_cancel₀ (ne_of_gt htheta) heq)
  simpa [pi, rankByScore] using hpi_scaled.symm

/-- At a positive accuracy, scaled-noise and additive score-space rankings coincide exactly. -/
theorem rankByScore_scaledNoise_eq_additiveScore
    {n : ℕ} (value noise : Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta) :
    rankByScore (fun i => value i + noise i / theta) =
      rankByScore (fun i => theta * value i + noise i) := by
  have hscore :
      (fun i : Candidate n => theta * (value i + noise i / theta)) =
        fun i => theta * value i + noise i := by
    funext i
    field_simp [ne_of_gt htheta]
  rw [← hscore]
  exact (rankByScore_pos_scale (fun i => value i + noise i / theta) htheta).symm

/-- The corresponding fixed ranking cells have exactly the same preimage at positive accuracy. -/
theorem scaledNoiseRankingCell_preimage_eq_additiveScore
    {n : ℕ} {Omega : Type*} (value : Candidate n → ℝ)
    (noise : Omega → Candidate n → ℝ) {theta : ℝ} (htheta : 0 < theta)
    (pi : Ranking n) :
    {omega | rankByScore (fun i => value i + noise omega i / theta) = pi} =
      {omega | rankByScore (fun i => theta * value i + noise omega i) = pi} := by
  ext omega
  change
    rankByScore (fun i => value i + noise omega i / theta) = pi ↔
      rankByScore (fun i => theta * value i + noise omega i) = pi
  rw [rankByScore_scaledNoise_eq_additiveScore value (noise omega) htheta]

end KR21Monoculture
