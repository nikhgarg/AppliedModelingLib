import KR21Monoculture.FirstChoice

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
The second-mover utility gain from facing the weaker/noisier competition
`μWorse` rather than the stronger/more accurate competition `μBetter`, while the
second mover's own ranking is drawn from `μWorse`.
-/
noncomputable def weakerCompetitionGain {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.weakerCompetitionGain μBetter μWorse value

/-- Preference for weaker competition is positivity of the weaker-competition gain. -/
theorem prefersWeakerCompetition_iff_weakerCompetitionGain_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < weakerCompetitionGain μBetter μWorse value := by
  unfold Model.PrefersWeakerCompetition weakerCompetitionGain
  exact AppliedModelingLib.SocialChoice.Ranking.prefersWeakerCompetition_iff_weakerCompetitionGain_pos
    μBetter μWorse value

/--
First-choice-probability decomposition of Definition 3.

The gain from weaker competition is the expected value, over the weaker ranking,
of

`(Pr_better[competitor takes my top] - Pr_worse[competitor takes my top]) * valueGap`.

This isolates the economics: weaker competition is valuable when the stronger
competitor is more likely to collide with the second mover's top candidate.
-/
theorem weakerCompetitionGain_eq_expected_collision_loss_diff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  simpa [weakerCompetitionGain,
    AppliedModelingLib.SocialChoice.Ranking.weakerCompetitionGain,
    firstChoiceProb, valueGap, firstChoice,
    AppliedModelingLib.SocialChoice.Ranking.firstChoice] using
    AppliedModelingLib.SocialChoice.Ranking.weakerCompetitionGain_eq_expected_collision_loss_diff
      (μBetter := μBetter) (μWorse := μWorse) (value := value)

/-- Definition 3, rewritten using first-choice collision probabilities and value gaps. -/
theorem prefersWeakerCompetition_iff_expected_collision_loss_diff_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < pmfExp μWorse
        (fun π =>
          (firstChoiceProb μBetter (firstChoice π) -
              firstChoiceProb μWorse (firstChoice π)) * valueGap value π) := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]

/--
A sufficient monotonicity condition for weak competition to be weakly valuable.
If the better competitor collides at least as often with every relevant first
choice and all top-second gaps are nonnegative, then facing the worse competitor
weakly improves second-mover utility.
-/
theorem weakerCompetitionGain_nonneg_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    0 ≤ weakerCompetitionGain μBetter μWorse value := by
  simpa [weakerCompetitionGain,
    AppliedModelingLib.SocialChoice.Ranking.weakerCompetitionGain,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    AppliedModelingLib.SocialChoice.Ranking.weakerCompetitionGain_nonneg_of_collisionProb_le_and_gap_nonneg
      (μBetter := μBetter) (μWorse := μWorse) (value := value)
      (by
        intro π
        simpa [firstChoiceProb, firstChoice,
          AppliedModelingLib.SocialChoice.Ranking.firstChoice] using hprob π)
      (by
        intro π
        simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
          firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using hgap π)

/-- Utility-side corollary of the sufficient monotonicity condition. -/
theorem expectedSecondMoverIndependent_le_of_collisionProb_le_and_gap_nonneg {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hprob : ∀ π : Ranking n,
      firstChoiceProb μWorse (firstChoice π) ≤ firstChoiceProb μBetter (firstChoice π))
    (hgap : ∀ π : Ranking n, 0 ≤ valueGap value π) :
    expectedSecondMoverIndependent μWorse μBetter value ≤
      expectedSecondMoverIndependent μWorse μWorse value := by
  simpa [expectedSecondMoverIndependent,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    secondMoverUtility, AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_le_self_of_collisionProb_le_and_gap_nonneg
      (μBetter := μBetter) (μWorse := μWorse) (value := value)
      (by
        intro π
        simpa [firstChoiceProb, firstChoice,
          AppliedModelingLib.SocialChoice.Ranking.firstChoice] using hprob π)
      (by
        intro π
        simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
          firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using hgap π)

end KR21Monoculture
