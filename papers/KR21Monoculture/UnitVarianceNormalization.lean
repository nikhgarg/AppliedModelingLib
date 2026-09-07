import KR21Monoculture.MainTheorems

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.SocialChoice.Ranking

/-!
# Scale Reparameterization for the KR21 Scaled-Noise Model

This module formalizes only the algebraic/probabilistic transport behind the
source's WLOG scale normalization.  A positive scale `sigma` transports a raw
noise law through `noise |-> noise / sigma` and replaces `theta` by
`theta / sigma`; the score function, ranking function, and induced finite
ranking PMF are unchanged.

It deliberately does *not* identify `sigma` with a standard deviation or prove
that the pushed-forward law has unit variance.  Those distributional
regularity claims remain separate source obligations.
-/

namespace KR21Monoculture

/-- Divide every coordinate of a finite noise vector by a scale. -/
noncomputable def scaledNoiseNormalization {n : ℕ} (sigma : ℝ) :
    (Candidate n → ℝ) → Candidate n → ℝ :=
  fun noise i => noise i / sigma

/-- Coordinatewise division by a fixed real scale is measurable. -/
theorem measurable_scaledNoiseNormalization {n : ℕ} (sigma : ℝ) :
    Measurable (scaledNoiseNormalization (n := n) sigma) := by
  apply measurable_pi_lambda _
  intro i
  change Measurable (fun noise : Candidate n → ℝ => noise i / sigma)
  have hcoordinate : Measurable (fun noise : Candidate n → ℝ => noise i) :=
    measurable_pi_apply i
  exact hcoordinate.div_const sigma

/--
The score functions before and after scale reparameterization agree pointwise.
The nonzero hypothesis is the exact algebraic requirement; source-facing
results below retain the stronger positivity condition on the scale.
-/
theorem scaledNoise_score_reparameterization
    {n : ℕ} (value noise : Candidate n → ℝ) {sigma theta : ℝ}
    (hsigma : sigma ≠ 0) :
    (fun i => value i + (noise i / sigma) / (theta / sigma)) =
      fun i => value i + noise i / theta := by
  funext i
  field_simp

/-- Scaling the noise and scale parameter leaves the score ranking unchanged. -/
theorem rankByScore_scaledNoise_reparameterization
    {n : ℕ} (value noise : Candidate n → ℝ) {sigma theta : ℝ}
    (hsigma : 0 < sigma) :
    rankByScore (fun i => value i + (noise i / sigma) / (theta / sigma)) =
      rankByScore (fun i => value i + noise i / theta) := by
  exact congrArg rankByScore
    (scaledNoise_score_reparameterization value noise (ne_of_gt hsigma))

/--
Transport a finite ranking PMF along a measurable noise reparameterization.
The compatibility hypothesis is extensional: it requires the two ranking maps
to agree after applying the transport, rather than relying on their names.
-/
theorem rankingPMFOfMeasure_map_transport
    {n : ℕ} {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (mu : Measure α) [IsProbabilityMeasure mu]
    (scale : α → β) (hscale : Measurable scale)
    (raw : α → Ranking n) (hraw : Measurable raw)
    (normalized : β → Ranking n) (hnormalized : Measurable normalized)
    (hcomp : normalized ∘ scale = raw) :
    rankingPMFOfMeasure mu raw hraw =
      @rankingPMFOfMeasure n β _ (mu.map scale)
        (Measure.isProbabilityMeasure_map hscale.aemeasurable)
        normalized hnormalized := by
  letI : IsProbabilityMeasure (mu.map scale) :=
    Measure.isProbabilityMeasure_map hscale.aemeasurable
  unfold rankingPMFOfMeasure
  apply PMF.ext
  intro ranking
  simp only [Measure.toPMF_apply]
  have hmeasure : Measure.map normalized (Measure.map scale mu) =
      Measure.map raw mu := by
    rw [Measure.map_map hnormalized hscale, hcomp]
  rw [hmeasure]

/--
The actual Appendix-A scaled-noise ranking law is invariant under a positive
noise-scale reparameterization.  The target law is the pushforward of `mu`
under coordinatewise division by `sigma`; no variance claim is used here.
-/
theorem paper_appendixA_scaledNoiseRankingPMF_scale_reparameterization
    {n : ℕ} (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ) {sigma theta : ℝ} (hsigma : 0 < sigma) :
    paper_appendixA_scaledNoiseRankingPMF mu value theta =
      @paper_appendixA_scaledNoiseRankingPMF n
        (mu.map (scaledNoiseNormalization (n := n) sigma))
        (Measure.isProbabilityMeasure_map
          (measurable_scaledNoiseNormalization (n := n) sigma).aemeasurable)
        value (theta / sigma) := by
  let scale : (Candidate n → ℝ) → Candidate n → ℝ :=
    scaledNoiseNormalization (n := n) sigma
  let raw : (Candidate n → ℝ) → Ranking n :=
    fun noise => rankByScore (fun i => value i + noise i / theta)
  let normalized : (Candidate n → ℝ) → Ranking n :=
    fun noise => rankByScore (fun i => value i + noise i / (theta / sigma))
  have hscale : Measurable scale := by
    exact measurable_scaledNoiseNormalization (n := n) sigma
  have hraw : Measurable raw := by
    dsimp [raw]
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (Ω := Candidate n → ℝ)
      (fun noise i => noise i)
      (fun i => measurable_pi_apply i)
      value theta
  have hnormalized : Measurable normalized := by
    dsimp [normalized]
    exact paper_appendixA_scaledNoise_rankByScore_measurable
      (Ω := Candidate n → ℝ)
      (fun noise i => noise i)
      (fun i => measurable_pi_apply i)
      value (theta / sigma)
  have hcomp : normalized ∘ scale = raw := by
    funext noise
    exact rankByScore_scaledNoise_reparameterization value noise hsigma
  change rankingPMFOfMeasure mu raw hraw =
    @rankingPMFOfMeasure n (Candidate n → ℝ) _ (mu.map scale)
      (Measure.isProbabilityMeasure_map hscale.aemeasurable)
      normalized hnormalized
  exact rankingPMFOfMeasure_map_transport
    mu scale hscale raw hraw normalized hnormalized hcomp

end KR21Monoculture
