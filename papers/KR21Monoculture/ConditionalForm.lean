import KR21Monoculture.RerankingGain
import AppliedModelingLib.Foundations.Probability.Conditional

open AppliedModelingLib

namespace KR21Monoculture

/-- A pair of i.i.d. ranking draws. -/
abbrev RankingPair (n : ℕ) := Ranking n × Ranking n

/-- The event that two rankings disagree on the first-position candidate. -/
def disagreementEvent {n : ℕ} : RankingPair n → Prop := fun p => firstChoice p.1 ≠ firstChoice p.2

instance decidableDisagreementEvent {n : ℕ} : DecidablePred (@disagreementEvent n) := by
  intro p
  unfold disagreementEvent
  infer_instance

/-- The reranking-gain integrand viewed as a function on ranking pairs. -/
def pairRerankingGain {n : ℕ} (value : Candidate n → ℝ) : RankingPair n → ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.pairRerankingGain value

/-- Probability that two i.i.d. ranking draws disagree on the first choice. -/
noncomputable def disagreementProb {n : ℕ} (μ : PMF (Ranking n)) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.disagreementProb μ

/-- Conditional expected reranking gain given disagreement on the first choice. -/
noncomputable def disagreementConditionalGain {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) : ℝ :=
  AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain μ value

@[simp] theorem pairRerankingGain_apply {n : ℕ} (value : Candidate n → ℝ)
    (π σ : Ranking n) :
    pairRerankingGain value (π, σ) = rerankingGainOnPair value π σ := by
  rfl

/-- Since `rerankingGainOnPair` is already `0` on agreement, the indicator form is exact. -/
theorem expectedRerankingGain_eq_pairIndicatorExp {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ) :
    expectedRerankingGain μ value =
      pmfPairIndicatorExp μ μ disagreementEvent (pairRerankingGain value) := by
  simpa [expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain,
    disagreementEvent, AppliedModelingLib.SocialChoice.Ranking.disagreementEvent,
    pairRerankingGain, AppliedModelingLib.SocialChoice.Ranking.pairRerankingGain,
    rerankingGainOnPair, AppliedModelingLib.SocialChoice.Ranking.rerankingGainOnPair,
    firstChoice, AppliedModelingLib.SocialChoice.Ranking.firstChoice,
    secondChoice, AppliedModelingLib.SocialChoice.Ranking.secondChoice] using
    AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain_eq_pairIndicatorExp
      (μ := μ) (value := value)

/-- On a positive-probability disagreement event, the conditional gain is a simple ratio. -/
theorem disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    disagreementConditionalGain μ value =
      expectedRerankingGain μ value / disagreementProb μ := by
  simpa [disagreementConditionalGain,
    AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain,
    disagreementProb, AppliedModelingLib.SocialChoice.Ranking.disagreementProb,
    expectedRerankingGain, AppliedModelingLib.SocialChoice.Ranking.expectedRerankingGain]
    using
      AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain_eq_expectedRerankingGain_div_of_pos
        (μ := μ) (value := value) h

/-- Positive reranking preference is equivalent to positive conditional gain on disagreement. -/
theorem prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos {n : ℕ}
    (μ : PMF (Ranking n)) (value : Candidate n → ℝ)
    (h : 0 < disagreementProb μ) :
    Model.PrefersIndependentReranking μ value ↔ 0 < disagreementConditionalGain μ value := by
  simpa [Model.PrefersIndependentReranking,
    AppliedModelingLib.SocialChoice.Ranking.PrefersIndependentReranking,
    disagreementConditionalGain,
    AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain,
    disagreementProb, AppliedModelingLib.SocialChoice.Ranking.disagreementProb] using
    AppliedModelingLib.SocialChoice.Ranking.prefersIndependentReranking_iff_conditionalGain_pos_of_disagreementPos
      (μ := μ) (value := value) h

@[simp] theorem disagreementProb_pure {n : ℕ} (π : Ranking n) :
    disagreementProb (PMF.pure π) = 0 := by
  simpa [disagreementProb, AppliedModelingLib.SocialChoice.Ranking.disagreementProb] using
    AppliedModelingLib.SocialChoice.Ranking.disagreementProb_pure (π := π)

@[simp] theorem disagreementConditionalGain_pure {n : ℕ}
    (π : Ranking n) (value : Candidate n → ℝ) :
    disagreementConditionalGain (PMF.pure π) value = 0 := by
  simpa [disagreementConditionalGain,
    AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain] using
    AppliedModelingLib.SocialChoice.Ranking.disagreementConditionalGain_pure
      (π := π) (value := value)

end KR21Monoculture
