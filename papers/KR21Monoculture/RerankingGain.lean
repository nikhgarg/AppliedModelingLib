import KR21Monoculture.PaperDefinitions
import AppliedModelingLib.Foundations.Probability.FiniteExpectation
import AppliedModelingLib.SocialChoice.Ranking.Payoff

open scoped BigOperators
open AppliedModelingLib

namespace KR21Monoculture

/--
For a pair of rankings, the second mover's pointwise gain from using an
independent reranking instead of sharing the same ranking.
-/
def rerankingGainOnPair {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) : ℝ :=
  if firstChoice π = firstChoice σ then 0
  else value (firstChoice π) - value (secondChoice π)

/--
A pair-lifted version of shared-reranking utility on the common product space
`μ × μ`.
-/
noncomputable def expectedSecondMoverSharedOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π _σ => secondMoverUtility value π π)

/--
The expected gain from independent reranking over a pair of i.i.d. ranking draws.
-/
noncomputable def expectedRerankingGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  pmfPairExp μ μ (fun π σ => rerankingGainOnPair value π σ)

@[simp] theorem rerankingGainOnPair_self {n : ℕ} (value : Candidate n → ℝ)
    (π : Ranking n) :
    rerankingGainOnPair value π π = 0 := by
  simpa [rerankingGainOnPair,
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_self value π

@[simp] theorem rerankingGainOnPair_of_sameFirst {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n)
    (h : firstChoice π = firstChoice σ) :
    rerankingGainOnPair value π σ = 0 := by
  simpa [rerankingGainOnPair,
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_sameFirst
      value π σ h

@[simp] theorem rerankingGainOnPair_of_neFirst {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n)
    (h : firstChoice π ≠ firstChoice σ) :
    rerankingGainOnPair value π σ =
      value (firstChoice π) - value (secondChoice π) := by
  simpa [rerankingGainOnPair,
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair_of_neFirst
      value π σ h

theorem secondMoverUtility_eq_shared_add_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ =
      secondMoverUtility value π π + rerankingGainOnPair value π σ := by
  simpa [rerankingGainOnPair,
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility_eq_shared_add_rerankingGain
      value π σ

theorem secondMoverUtility_sub_self_eq_rerankingGain {n : ℕ}
    (value : Candidate n → ℝ) (π σ : Ranking n) :
    secondMoverUtility value π σ - secondMoverUtility value π π =
      rerankingGainOnPair value π σ := by
  simpa [rerankingGainOnPair,
    AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.secondMoverUtility_sub_self_eq_rerankingGain
      value π σ

theorem expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value -
        expectedSecondMoverSharedOnPairs μ value =
      expectedRerankingGain μ value := by
  simpa [expectedSecondMoverSharedOnPairs,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs,
    expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)

theorem expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value =
      expectedSecondMoverSharedOnPairs μ value + expectedRerankingGain μ value := by
  simpa [expectedSecondMoverSharedOnPairs,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs,
    expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_sharedOnPairs_add_expectedRerankingGain
      (μ := μ) (value := value)

@[simp] theorem expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverSharedOnPairs μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverSharedOnPairs,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverSharedOnPairs_eq_expectedSecondMoverShared
      (μ := μ) (value := value)

theorem expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
    {n : ℕ} (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedSecondMoverIndependent μ μ value - expectedSecondMoverShared μ value =
      expectedRerankingGain μ value := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_sub_shared_eq_expectedRerankingGain
      (μ := μ) (value := value)

/--
Definition 2 source-shaped averaging identity: condition first on the shared
ranking `τ`, then average the independent second draw's best remaining
candidate against `τ`'s second choice.
-/
theorem expectedRerankingGain_eq_expect_firstDraw_gain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfExp μ (fun τ =>
        pmfExp μ (fun π =>
          value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ))) := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice,
    bestRemainingAfter, AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_eq_expect_firstDraw_gain
      (μ := μ) (value := value)

/--
Definition 2 source-shaped bridge: first-choice-fiber conditional gains imply
positive expected independent-reranking gain.
-/
theorem expectedRerankingGain_pos_of_firstChoiceProb_conditional_gain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hcond : ∀ c : Candidate n,
      0 < AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb μ c →
        0 < pmfConditionalExp μ (fun τ => c = firstChoice τ)
          (fun τ =>
            pmfExp μ (fun π =>
              value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))) :
    0 < expectedRerankingGain μ value := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice,
    bestRemainingAfter, AppliedModelingLib.SocialChoice.Ranking.bestRemainingAfter] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_pos_of_firstChoiceProb_conditional_gain_pos
      (μ := μ) (value := value) hcond

@[simp] theorem expectedRerankingGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    expectedRerankingGain (PMF.pure π) value = 0 := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_pure π value

/--
A positivity reformulation of the pair-lifted reranking preference.
-/
noncomputable def PrefersIndependentRerankingOnPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : Prop :=
  0 < expectedRerankingGain μ value

/--
The pair-lifted version of Definition 2 is equivalent to positivity of the
expected reranking gain.
-/
theorem prefersIndependentRerankingOnPairs_iff {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    PrefersIndependentRerankingOnPairs μ value ↔
      expectedSecondMoverSharedOnPairs μ value <
        expectedSecondMoverIndependent μ μ value := by
  unfold PrefersIndependentRerankingOnPairs
  have h :=
    expectedSecondMoverIndependent_sub_sharedOnPairs_eq_expectedRerankingGain
      (μ := μ) (value := value)
  constructor <;> intro hmain <;> linarith

/--
Definition 2 in utility form is exactly positivity of the expected reranking gain.
-/
theorem prefersIndependentReranking_iff_expectedRerankingGain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔ 0 < expectedRerankingGain μ value := by
  simpa [Model.PrefersIndependentReranking,
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking,
    expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair] using
    AppliedModelingLib.SocialChoice.Ranking.prefersIndependentReranking_iff_expectedRerankingGain_pos
      (μ := μ) (value := value)

/--
The pair-lifted positivity formulation is equivalent to the original utility-side
Definition 2.
-/
theorem prefersIndependentReranking_iff_onPairs {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    Model.PrefersIndependentReranking μ value ↔
      PrefersIndependentRerankingOnPairs μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  rfl

/--
Definition 2 from first-choice-fiber conditional gains, in the paper's
utility-preference form.
-/
theorem prefersIndependentReranking_of_firstChoiceProb_conditional_gain_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hcond : ∀ c : Candidate n,
      0 < AppliedModelingLib.SocialChoice.Ranking.firstChoiceProb μ c →
        0 < pmfConditionalExp μ (fun τ => c = firstChoice τ)
          (fun τ =>
            pmfExp μ (fun π =>
              value (bestRemainingAfter π (firstChoice τ)) - value (secondChoice τ)))) :
    Model.PrefersIndependentReranking μ value := by
  rw [prefersIndependentReranking_iff_expectedRerankingGain_pos]
  exact expectedRerankingGain_pos_of_firstChoiceProb_conditional_gain_pos μ value hcond

end KR21Monoculture
