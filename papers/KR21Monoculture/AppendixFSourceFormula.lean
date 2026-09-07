import KR21Monoculture.MainTheorems

open scoped BigOperators
open AppliedModelingLib
open AppliedModelingLib.SocialChoice.Ranking

namespace KR21Monoculture

/-!
# Appendix F source parameter formulas

The source writes the Mallows parameter as `phi > 1`, whereas the local
finite Mallows development uses `q = phi⁻¹`.  These endpoints expose the
probability formulas themselves at the source parameter surface, rather than
only the unnormalised weight algebra used to prove them.
-/

/-- The source Mallows parameterization: the local inverse parameter is
`phi⁻¹`. -/
def SourceMallowsParameter {n : ℕ} (M : MallowsSpec n) (phi : ℝ) : Prop :=
  1 < phi /\ M.q = phi⁻¹

/-- Equation (F.1): for a center-ordered pair `c,d`, the source probability
of selecting `c` then `d` is `phi` times the reverse top-two probability. -/
theorem source_equationF1_mallows_top_two_probability
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi : M.q = phi⁻¹) {c d : Candidate n}
    (hcd : rankOf M.center c < rankOf M.center d) :
    M.firstSecondChoiceProb c d =
      phi * M.firstSecondChoiceProb d c := by
  have hweight :
      M.firstSecondWeight d c = M.q * M.firstSecondWeight c d :=
    MallowsComparison.paper_lemma5_mallows_top_two_swap_ratio M hcd
  have hprob :
      M.firstSecondChoiceProb d c =
        M.q * M.firstSecondChoiceProb c d := by
    rw [M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition,
      M.firstSecondChoiceProb_eq_firstSecondWeight_div_partition, hweight]
    ring
  have hphi_ne : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hphi
    simp at hphi
    exact (ne_of_gt M.q_pos) hphi
  have hphi_q : phi * M.q = 1 := by
    rw [hphi]
    field_simp
  calc
    M.firstSecondChoiceProb c d =
        (phi * M.q) * M.firstSecondChoiceProb c d := by
          rw [hphi_q]
          ring
    _ = phi * (M.q * M.firstSecondChoiceProb c d) := by ring
    _ = phi * M.firstSecondChoiceProb d c := by rw [hprob]

/-- Equation (F.2) before expanding the finite geometric denominator: the
first-choice probability is the source rank power `phi^{-(i-1)}` normalized
over all source ranks.  In the library `rankOf` starts at zero and the source
candidate count is `n + 2`. -/
theorem source_equationF2_mallows_first_choice_rank_power
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hphi : M.q = phi⁻¹) (c : Candidate n) :
    firstChoiceProb M.law c =
      phi⁻¹ ^ (rankOf M.center c : ℕ) /
        candidateRankPowerSum n phi⁻¹ := by
  rw [M.firstChoiceProb_eq_firstWeight_div_partition]
  have h := MallowsComparison.paper_lemma6_mallows_first_choice_prob_eq_rank_power M c
  rw [hphi] at h
  exact h

/-- Equation (F.2) in the exact source closed form.  The source's one-based
rank `i - 1` is `rankOf` in Lean, and its candidate count is `n + 2` for the
library carrier `Candidate n`. -/
theorem source_equationF2_mallows_first_choice_closed_form
    {n : ℕ} (M : MallowsSpec n) (phi : ℝ)
    (hparameter : SourceMallowsParameter M phi) (c : Candidate n) :
    firstChoiceProb M.law c =
      (1 - phi⁻¹) /
        (phi ^ (rankOf M.center c : ℕ) *
          (1 - phi⁻¹ ^ (n + 2))) := by
  rcases hparameter with ⟨hphi_gt, hq⟩
  let r : ℕ := rankOf M.center c
  let S : ℝ := candidateRankPowerSum n M.q
  have hq_lt_one : M.q < 1 := by
    rw [hq]
    exact inv_lt_one_of_one_lt₀ hphi_gt
  have hSpos : 0 < S := by
    dsimp [S]
    exact candidateRankPowerSum_pos n M.q_pos
  have hpow_lt : M.q ^ (n + 2) < 1 := by
    apply pow_lt_one₀ (le_of_lt M.q_pos) hq_lt_one
    omega
  have hgeom : S * (1 - M.q) = 1 - M.q ^ (n + 2) := by
    dsimp [S]
    exact candidateRankPowerSum_mul_one_sub n M.q
  have hphi_ne : phi ≠ 0 := by
    intro hzero
    rw [hzero] at hq
    simp at hq
    exact (ne_of_gt M.q_pos) hq
  have hphi_q : phi * M.q = 1 := by
    rw [hq]
    field_simp
  have hpow : phi ^ r * M.q ^ r = 1 := by
    rw [← mul_pow, hphi_q]
    simp
  have hprob : firstChoiceProb M.law c = M.q ^ r / S := by
    rw [M.firstChoiceProb_eq_firstWeight_div_partition]
    simpa [r, S] using
      (MallowsComparison.paper_lemma6_mallows_first_choice_prob_eq_rank_power M c)
  rw [hprob, ← hq]
  field_simp [ne_of_gt hSpos, ne_of_gt (sub_pos.mpr hpow_lt), hphi_ne]
  nlinarith [hgeom, hpow]

end KR21Monoculture
