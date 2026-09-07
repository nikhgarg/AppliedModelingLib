import KR21Monoculture.Payoff

open AppliedModelingLib

namespace KR21Monoculture

/--
If every ranking in the outer expectation has zero miss probability for its own
first choice, independent reranking has zero expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedRerankingGain μ value = 0 := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_eq_zero_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/--
If every top-vs-runner-up value gap is zero, independent reranking has zero
expected gain.
-/
theorem expectedRerankingGain_eq_zero_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedRerankingGain μ value = 0 := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_eq_zero_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using hgap π)

/--
Zero miss probability collapses independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverIndependent,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverShared,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_shared_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/--
Zero value gaps also collapse independent and shared second-mover utility.
-/
theorem expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    expectedSecondMoverIndependent μ μ value = expectedSecondMoverShared μ value := by
  simpa [expectedSecondMoverIndependent,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent,
    expectedSecondMoverShared,
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverShared] using
    AppliedModelingLib.SocialChoice.Ranking.expectedSecondMoverIndependent_eq_shared_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using hgap π)

/-- No independent-reranking preference is possible when all relevant miss probabilities vanish. -/
theorem not_prefersIndependentReranking_of_all_missProb_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hmiss : ∀ π : Ranking n, firstChoiceMissProb μ (firstChoice π) = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  simpa [Model.PrefersIndependentReranking,
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking] using
    AppliedModelingLib.SocialChoice.Ranking.not_prefersIndependentReranking_of_all_missProb_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
          firstChoiceMissProb, AppliedModelingLib.SocialChoice.Ranking.firstChoiceMissProb]
          using hmiss π)

/-- No independent-reranking preference is possible when every top-second gap is zero. -/
theorem not_prefersIndependentReranking_of_all_valueGap_zero {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (hgap : ∀ π : Ranking n, valueGap value π = 0) :
    ¬ Model.PrefersIndependentReranking μ value := by
  simpa [Model.PrefersIndependentReranking,
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking] using
    AppliedModelingLib.SocialChoice.Ranking.not_prefersIndependentReranking_of_all_valueGap_zero
      (μ := μ) (value := value) (by
        intro π
        simpa [valueGap, AppliedModelingLib.SocialChoice.Ranking.valueGap] using hgap π)

end KR21Monoculture
