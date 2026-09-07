import KR21Monoculture.Definition1FullW11

/-!
# Full asymptotic optimality for corrected Theorem 5

The source's Definition 1 requires a genuine high-accuracy limit, not merely
one sufficiently accurate witness for each tolerance.  The existing
scaled-noise tail proof already establishes an eventual adjacent-misorder
bound.  This module preserves that eventuality through the finite union bound
and exposes the corrected `W^{1,1}` Theorem 5 conclusion with an explicit
`Filter.Tendsto` result.
-/

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

private theorem scaledNoiseRanking_atom_eventually_close_to_pure
    {n : ℕ} (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc))
    (pi : Ranking n) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ theta : ℝ in atTop,
      |((rankingPMFOfMeasure mu
          (fun noise => rankByScore
            (fun c => value c + noise c / theta))
          (paper_appendixA_scaledNoise_rankByScore_measurable
            (Ω := Candidate n → ℝ)
            (fun noise c => noise c)
            (fun c => measurable_pi_apply c) value theta)) pi).toReal -
          ((PMF.pure center : PMF (Ranking n)) pi).toReal| < epsilon := by
  classical
  have hsum := paper_appendixA_scaledNoise_adjacent_score_misorder_sum_tendsto
    mu (fun noise c => noise c) (fun c => measurable_pi_apply c)
    value center hcenter
  filter_upwards [hsum.eventually (Iio_mem_nhds hepsilon)] with theta htheta
  exact
    rankingPMFOfMeasure_rankByScore_atomwise_close_to_pure_of_sum_adjacent_score_misorder_probs_lt
      mu (fun noise c => value c + noise c / theta)
      (paper_appendixA_scaledNoise_rankByScore_measurable
        (Ω := Candidate n → ℝ)
        (fun noise c => noise c)
        (fun c => measurable_pi_apply c) value theta)
      center hepsilon htheta pi

private theorem scaledNoiseRanking_atom_tendsto_to_pure
    {n : ℕ} (mu : Measure (Candidate n → ℝ)) [IsProbabilityMeasure mu]
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    ∀ pi : Ranking n,
      Tendsto
        (fun theta =>
          ((rankingPMFOfMeasure mu
            (fun noise => rankByScore
              (fun c => value c + noise c / theta))
            (paper_appendixA_scaledNoise_rankByScore_measurable
              (Ω := Candidate n → ℝ)
              (fun noise c => noise c)
              (fun c => measurable_pi_apply c) value theta)) pi).toReal)
        atTop (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)) := by
  intro pi
  refine Metric.tendsto_atTop.mpr ?_
  intro epsilon hepsilon
  rcases Filter.eventually_atTop.1
      (scaledNoiseRanking_atom_eventually_close_to_pure
        mu value center hcenter pi hepsilon) with ⟨lower, hlower⟩
  refine ⟨lower, ?_⟩
  intro theta htheta
  rw [Real.dist_eq]
  exact hlower theta htheta

/--
The literal iid corrected W11 family has the source Definition 1 atomwise
high-accuracy limit.  The source-family to raw-rank-PMF identity is supplied by
an explicit proved bridge, rather than unfolded during limit elaboration.
-/
theorem correctedW11ScaledNoiseFamily_atom_tendsto_to_pure
    {n : ℕ} (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    ∀ pi : Ranking n,
      Filter.Tendsto
        (fun theta =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal)) := by
  classical
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  intro pi
  have hraw := scaledNoiseRanking_atom_tendsto_to_pure
    (w11CandidateNoiseLaw (n := n) f) value center hcenter pi
  refine hraw.congr ?_
  intro theta
  exact
    (w11CorrectedScaledNoiseFamily_atom_eq_rankingPMFOfMeasure
      f hnormalized value theta pi
      (paper_appendixA_scaledNoise_rankByScore_measurable
        (Ω := Candidate n → ℝ)
        (fun noise c => noise c)
        (fun c => measurable_pi_apply c) value theta)).symm

/--
The corrected source-facing Theorem 5 route.  The result states Definition 1
directly: atom probabilities are continuous and differentiable at every
positive accuracy, every atom converges to the pure true-ranking law at high
accuracy, removal monotonicity holds for every nonempty remaining candidate
set, and the full-set inequality is strict.

The assumptions are exactly those of
`correctedW11ScaledNoiseDefinition1_full_of_source`; this theorem strengthens
only its weakened concentration conclusion from arbitrarily high witnesses to
the source's actual limit statement.
-/
theorem correctedW11ScaledNoiseDefinition1_sourceFaithful_of_source
    {n : ℕ} (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f)
    (hfullSupport : ∀ x, 0 < f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (center : Ranking n)
    (hcenter : ∀ i : Fin (n + 1),
      value (center i.succ) < value (center i.castSucc)) :
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      ContinuousAt
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta ∧
      DifferentiableAt ℝ
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ pi : Ranking n,
      Filter.Tendsto
        (fun theta =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta pi).toReal)
        Filter.atTop
        (nhds (((PMF.pure center : PMF (Ranking n)) pi).toReal))) ∧
    (∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      ∀ remaining : Finset (Candidate n), remaining.Nonempty →
        expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
            value remaining ≤
          expectedBestInSet
            ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
            value remaining) ∧
    ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
      expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
          value Finset.univ <
        expectedBestInSet
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
          value Finset.univ := by
  rcases correctedW11ScaledNoiseDefinition1_full_of_source
      f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
      derivative_ae_eq hnormalized value center hcenter with
    ⟨hcontinuous, hdifferentiable, _hconcentration, hremoval, hstrict⟩
  refine ⟨?_, ?_, hremoval, hstrict⟩
  · intro theta htheta pi
    exact ⟨AppliedModelingLib.continuousAt_of_epsilonContinuousAt
      (hcontinuous theta htheta pi), hdifferentiable theta htheta pi⟩
  · exact correctedW11ScaledNoiseFamily_atom_tendsto_to_pure
      f hnormalized value center hcenter

end KR21Monoculture
