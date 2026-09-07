import KR21Monoculture.WeakCompetition

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
The contribution to expected reranking gain coming from rankings whose top
candidate is `c`.

This packages the part of the expectation that depends on the first-choice fiber
`{ π | firstChoice π = c }`. It is the right object for the Mallows branch,
where finite lemmas are typically stated in terms of top-candidate probabilities.
-/
noncomputable def firstChoiceGapMass {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass μ value c

/--
The collision-probability difference between a better and worse ranking law,
viewed candidate-by-candidate.
-/
noncomputable def firstChoiceCollisionDiff {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (c : Candidate n) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.firstChoiceCollisionDiff μBetter μWorse c

/-- Summing the first-choice fibers recovers the full expected value gap. -/
theorem sum_firstChoiceGapMass_eq_expectedGap {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    (∑ c : Candidate n, firstChoiceGapMass μ value c) =
      pmfExp μ (fun π => valueGap value π) :=
   AppliedModelingLib.SocialChoice.Ranking.sum_firstChoiceGapMass_eq_expectedGap
    μ value

/--
If every ranking in the first-choice fiber of `c` has nonnegative value gap,
then the corresponding first-choice gap mass is nonnegative.
-/
theorem firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) (c : Candidate n)
    (hgap : ∀ π : Ranking n, c = firstChoice π → 0 ≤ valueGap value π) :
    0 ≤ firstChoiceGapMass μ value c :=
   AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass_nonneg_of_gap_nonneg_onFiber
    μ value c hgap

/--
Equation (3) grouped by the second mover's first-choice candidate rather than by
full rankings.
-/
theorem expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    firstChoiceMissProb, firstChoiceGapMass,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass
      (μ := μ) (value := value)

/--
First-mover utility minus the expected utility of an independent second mover
with the same ranking law, grouped by the second mover's first-choice candidate.

This is the collision-loss companion to Equation (3): the first mover loses no
candidate, while the second mover loses their top candidate exactly when the
first mover independently chooses the same top candidate.
-/
theorem expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedFirstMoverUtility μ value - expectedSecondMoverIndependent μ μ value =
      ∑ c : Candidate n,
        firstChoiceProb μ c * firstChoiceGapMass μ value c := by
  simpa [expectedFirstMoverUtility,
    AppliedModelingLib.SocialChoice.Ranking.expectedFirstMoverUtility,
    expectedSecondMoverIndependent,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    firstChoiceProb, firstChoiceGapMass,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
    secondMoverUtility, AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility,
    bestRemainingAfter, AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using
    AppliedModelingLib.SocialChoice.Ranking.expectedFirstMover_sub_secondMoverIndependent_eq_sum_firstChoiceProb_mul_firstChoiceGapMass
      (μ := μ) (value := value)

/-- Candidate-sum version of the utility-side Definition 2. -/
theorem prefersIndependentReranking_iff_firstChoiceGapMassSum_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      0 < ∑ c : Candidate n,
        firstChoiceMissProb μ c * firstChoiceGapMass μ value c := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rw [expectedRerankingGain_eq_sum_firstChoiceMissProb_mul_firstChoiceGapMass]

/--
The collision-loss expression from Definition 3, grouped by the second mover's
first-choice candidate.
-/
theorem expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    pmfExp μWorse
      (fun π =>
        (firstChoiceProb μBetter (firstChoice π) -
            firstChoiceProb μWorse (firstChoice π)) * valueGap value π) =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  simpa [firstChoiceCollisionDiff,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceCollisionDiff,
    firstChoiceProb, firstChoiceGapMass,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceGapMass,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using
    AppliedModelingLib.SocialChoice.Ranking.expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
      (μBetter := μBetter) (μWorse := μWorse) (value := value)

/-- Definition 3 grouped by first-choice candidate rather than full rankings. -/
theorem weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass
    {n : ℕ} (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    weakerCompetitionGain μBetter μWorse value =
      ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [weakerCompetitionGain_eq_expected_collision_loss_diff]
  exact expectedCollisionLossDiff_eq_sum_collisionDiff_mul_firstChoiceGapMass
    (μBetter := μBetter) (μWorse := μWorse) (value := value)

/-- Candidate-sum version of the utility-side Definition 3. -/
theorem prefersWeakerCompetition_iff_firstChoiceCollisionDiffSum_pos {n : ℕ}
    (μBetter μWorse : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersWeakerCompetition μBetter μWorse value ↔
      0 < ∑ c : Candidate n,
        firstChoiceCollisionDiff μBetter μWorse c *
          firstChoiceGapMass μWorse value c := by
  rw [prefersWeakerCompetition_iff_weakerCompetitionGain_pos]
  rw [weakerCompetitionGain_eq_sum_collisionDiff_mul_firstChoiceGapMass]

end KR21Monoculture
