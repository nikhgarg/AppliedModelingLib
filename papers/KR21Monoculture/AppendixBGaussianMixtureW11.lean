import KR21Monoculture.FiniteGaussianMixtureW11

/-!
# Appendix B finite-mixture `W^{1,1}` source certificates

This module combines the explicit finite Gaussian-mixture regularity proof
with the separately proved latent-source transport.  It exposes only
source-facing B.1/B.2 certificates: the density is explicit, its iid source
law is the actual Appendix-B latent experiment, and the corrected Definition
1 package is instantiated at the paper's concrete value order.
-/

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal NNReal Topology BigOperators

namespace KR21Monoculture

noncomputable section

local instance : MeasurableSpace AppendixB1NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB1NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

local instance : MeasurableSpace AppendixB2NoiseAtom := ⊤
local instance : DiscreteMeasurableSpace AppendixB2NoiseAtom :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- The B.1 mixture density has all global regularity inputs of the repaired
Definition 1 route at every positive component scale. -/
theorem appendixB1GaussianMixture_w11Regularity
    (s : ℝ) (hs : 0 < s) :
    FiniteGaussianMixtureW11Regularity
      appendixB1NoisePMF appendixB1NoiseValue s := by
  exact finiteGaussianMixture_w11Regularity
    appendixB1NoisePMF appendixB1NoiseValue s hs

/-- The B.2 fixed-source mixture density has all global regularity inputs of
the repaired Definition 1 route at every positive component scale. -/
theorem appendixB2GaussianMixture_w11Regularity
    (s : ℝ) (hs : 0 < s) :
    FiniteGaussianMixtureW11Regularity
      appendixB2NoisePMF appendixB2NoiseValue s := by
  exact finiteGaussianMixture_w11Regularity
    appendixB2NoisePMF appendixB2NoiseValue s hs

private theorem appendixB1Value_strict_center_order :
    ∀ i : Fin 2,
      appendixB1Value (rum3Ranking012 i.succ) <
        appendixB1Value (rum3Ranking012 i.castSucc) := by
  intro i
  fin_cases i <;> norm_num [appendixB1Value, Fin.ext_iff]

private theorem appendixB2Value_strict_center_order :
    ∀ i : Fin 2,
      appendixB2Value (rum3Ranking012 i.succ) <
        appendixB2Value (rum3Ranking012 i.castSucc) := by
  intro i
  fin_cases i <;> norm_num [appendixB2Value, Fin.ext_iff]

/-- The actual B.1 latent experiment's source-noise vector. -/
def appendixB1SourceGaussianMixtureNoise
    (s : ℝ) (omega : AppendixB1NoiseTriple × AppendixBGaussianTriple)
    (c : Candidate 1) : ℝ :=
  appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c) +
    s * appendixBGaussianTripleFunction omega.2 c

theorem appendixB1SourceGaussianMixtureNoise_measurable
    (s : ℝ) (c : Candidate 1) :
    Measurable (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
      appendixB1SourceGaussianMixtureNoise s omega c) := by
  unfold appendixB1SourceGaussianMixtureNoise
  have hcenter : Measurable
      (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
        appendixB1NoiseValue (appendixB1NoiseTripleFunction omega.1 c)) :=
    (measurable_of_finite
      (fun noise : AppendixB1NoiseTriple =>
        appendixB1NoiseValue (appendixB1NoiseTripleFunction noise c))).comp
      measurable_fst
  have hperturb : Measurable
      (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
        appendixBGaussianTripleFunction omega.2 c) := by
    fin_cases c <;> simp [appendixBGaussianTripleFunction]
    · exact measurable_fst.comp measurable_snd
    · exact measurable_fst.comp (measurable_snd.comp measurable_snd)
    · exact measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact hcenter.add (measurable_const.mul hperturb)

theorem measurable_appendixB1SourceGaussianMixtureNoise
    (s : ℝ) :
    Measurable (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
      fun c => appendixB1SourceGaussianMixtureNoise s omega c) := by
  apply measurable_pi_lambda
  exact appendixB1SourceGaussianMixtureNoise_measurable s

theorem measurable_appendixB2SourceGaussianMixtureNoise
    (s : ℝ) :
    Measurable (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
      fun c => appendixB2SourceGaussianMixtureNoise s omega c) := by
  apply measurable_pi_lambda
  exact appendixB2SourceGaussianMixtureNoise_measurable s

/-- The B.1 source-noise vector transports the literal latent law to the
explicit iid mixture density law. -/
theorem appendixB1SourceGaussianMixtureNoise_measurePreserving
    (s : ℝ) (hs : 0 < s) :
    MeasurePreserving
      (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
        fun c => appendixB1SourceGaussianMixtureNoise s omega c)
      appendixB1GaussianLatentMeasure
      (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s)) := by
  refine ⟨measurable_appendixB1SourceGaussianMixtureNoise s, ?_⟩
  simpa only [appendixB1SourceGaussianMixtureNoise] using
    (appendixB1GaussianLatentMeasure_map_sourceNoise_eq_candidateNoiseLaw s hs)

/-- The B.2 common source-noise vector transports the literal latent law to
the explicit iid mixture density law. -/
theorem appendixB2SourceGaussianMixtureNoise_measurePreserving
    (s : ℝ) (hs : 0 < s) :
    MeasurePreserving
      (fun omega : AppendixB2NoiseTriple × AppendixBGaussianTriple =>
        fun c => appendixB2SourceGaussianMixtureNoise s omega c)
      appendixB2GaussianLatentMeasure
      (w11CandidateNoiseLaw (appendixB2GaussianMixtureDensity s)) := by
  refine ⟨measurable_appendixB2SourceGaussianMixtureNoise s, ?_⟩
  exact appendixB2GaussianLatentMeasure_map_sourceNoise_eq_candidateNoiseLaw s hs

/-- The literal B.1 source ranking at accuracy `theta`: one fixed finite
Gaussian-mixture source-noise vector is divided by the accuracy parameter.
The paper interpretation uses `0 < theta`; the definition is total only
because `AccuracyFamily.dist` is Lean-total. -/
def appendixB1SourceGaussianMixtureRank
    (s theta : ℝ) :
    (AppendixB1NoiseTriple × AppendixBGaussianTriple) → Ranking 1 :=
  fun omega =>
    AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun c => appendixB1Value c +
        appendixB1SourceGaussianMixtureNoise s omega c / theta)

theorem appendixB1SourceGaussianMixtureRank_measurable
    (s theta : ℝ) :
    Measurable (appendixB1SourceGaussianMixtureRank s theta) := by
  unfold appendixB1SourceGaussianMixtureRank
  exact paper_appendixA_scaledNoise_rankByScore_measurable
    (fun omega : AppendixB1NoiseTriple × AppendixBGaussianTriple =>
      fun c => appendixB1SourceGaussianMixtureNoise s omega c)
    (appendixB1SourceGaussianMixtureNoise_measurable s) appendixB1Value theta

/-- B.1 as one literal scaled-noise source family, separate from its
component-width parameter `s`. -/
noncomputable def appendixB1SourceGaussianMixtureFamily
    (s : ℝ) : AccuracyFamily 1 where
  dist := fun theta =>
    rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
      (appendixB1SourceGaussianMixtureRank s theta)
      (appendixB1SourceGaussianMixtureRank_measurable s theta)
  value := appendixB1Value

/-- The B.1 family at unit accuracy is the original Gaussian-mixture ranking
law used in the Appendix-B payoff calculation. -/
theorem appendixB1SourceGaussianMixtureFamily_dist_one_eq_latentRankingPMF
    (s : ℝ) :
    (appendixB1SourceGaussianMixtureFamily s).dist 1 =
      appendixB1GaussianMixtureRankingPMF s := by
  change rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
      (appendixB1SourceGaussianMixtureRank s 1)
      (appendixB1SourceGaussianMixtureRank_measurable s 1) =
    rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
      (appendixB1GaussianMixtureRank s)
      (appendixB1GaussianMixtureRank_measurable s)
  congr 1
  funext omega
  unfold appendixB1SourceGaussianMixtureRank
    appendixB1GaussianMixtureRank appendixB1GaussianMixtureScore
    appendixB1DiscreteScore appendixB1SourceGaussianMixtureNoise
  congr 1
  funext c
  ring

/-- The repaired scaled-noise family associated with B.1's explicit mixture
density.  The width `s` belongs to the fixed source-noise distribution; the
family parameter is the paper's accuracy `theta`. -/
noncomputable def appendixB1GaussianMixtureW11Family
    (s : ℝ) (hs : 0 < s) : AccuracyFamily 1 :=
  w11CorrectedScaledNoiseFamily
    (appendixB1GaussianMixtureDensity s)
    (appendixB1GaussianMixture_w11Regularity s hs).normalized
    appendixB1Value

/-- The repaired scaled-noise family associated with B.2's one fixed explicit
source-noise density. -/
noncomputable def appendixB2GaussianMixtureW11Family
    (s : ℝ) (hs : 0 < s) : AccuracyFamily 1 :=
  w11CorrectedScaledNoiseFamily
    (appendixB2GaussianMixtureDensity s)
    (appendixB2GaussianMixture_w11Regularity s hs).normalized
    appendixB2Value

/-- B.1's explicit finite mixture satisfies the corrected full Definition 1
package under its literal iid source law. -/
noncomputable def appendixB1GaussianMixture_correctedW11Definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB1GaussianMixtureW11Family s hs) rum3Ranking012 := by
  let hregularity := appendixB1GaussianMixture_w11Regularity s hs
  exact correctedW11ScaledNoiseDefinition1_of_source
    (appendixB1GaussianMixtureDensity s)
    (finiteGaussianMixtureDerivative appendixB1NoisePMF appendixB1NoiseValue s)
    hregularity.density_integrable hregularity.derivative_integrable
    hregularity.density_measurable hregularity.density_positive
    hregularity.absolute_continuity hregularity.derivative_ae_eq
    hregularity.normalized appendixB1Value rum3Ranking012
    appendixB1Value_strict_center_order

/-- B.2's explicit fixed source mixture satisfies the corrected full
Definition 1 package under its literal iid source law. -/
noncomputable def appendixB2GaussianMixture_correctedW11Definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB2GaussianMixtureW11Family s hs) rum3Ranking012 := by
  let hregularity := appendixB2GaussianMixture_w11Regularity s hs
  exact correctedW11ScaledNoiseDefinition1_of_source
    (appendixB2GaussianMixtureDensity s)
    (finiteGaussianMixtureDerivative appendixB2NoisePMF appendixB2NoiseValue s)
    hregularity.density_integrable hregularity.derivative_integrable
    hregularity.density_measurable hregularity.density_positive
    hregularity.absolute_continuity hregularity.derivative_ae_eq
    hregularity.normalized appendixB2Value rum3Ranking012
    appendixB2Value_strict_center_order

/-- At accuracy one, the corrected B.1 source family is exactly the actual
Appendix-B latent Gaussian-mixture ranking law. -/
theorem appendixB1GaussianMixtureW11Family_dist_one_eq_latentRankingPMF
    (s : ℝ) (hs : 0 < s) :
    (appendixB1GaussianMixtureW11Family s hs).dist 1 =
      appendixB1GaussianMixtureRankingPMF s := by
  let hregularity := appendixB1GaussianMixture_w11Regularity s hs
  letI : IsProbabilityMeasure
      (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s)) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      (appendixB1GaussianMixtureDensity s) hregularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s))
      appendixB1Value 1 =
      rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
        (appendixB1GaussianMixtureRank s)
        (appendixB1GaussianMixtureRank_measurable s)
  symm
  refine AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
    appendixB1GaussianLatentMeasure
    (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s))
    (fun omega => fun c => appendixB1SourceGaussianMixtureNoise s omega c)
    (appendixB1SourceGaussianMixtureNoise_measurePreserving s hs)
    (appendixB1GaussianMixtureRank s)
    (appendixB1GaussianMixtureRank_measurable s)
    (fun noise => AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun c => appendixB1Value c + noise c / 1))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun c => noise c)
      (fun c => measurable_pi_apply c) appendixB1Value 1) ?_
  intro omega
  unfold appendixB1GaussianMixtureRank appendixB1GaussianMixtureScore
    appendixB1DiscreteScore appendixB1SourceGaussianMixtureNoise
  congr 1
  funext c
  ring

/-- The corrected B.1 density family and the totalized literal source family
have the same ranking law at every real parameter.  Only the `theta > 0`
restriction is a paper accuracy model. -/
theorem appendixB1GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF
    (s : ℝ) (hs : 0 < s) (theta : ℝ) :
    (appendixB1GaussianMixtureW11Family s hs).dist theta =
      (appendixB1SourceGaussianMixtureFamily s).dist theta := by
  let hregularity := appendixB1GaussianMixture_w11Regularity s hs
  letI : IsProbabilityMeasure
      (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s)) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      (appendixB1GaussianMixtureDensity s) hregularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s))
      appendixB1Value theta =
      rumRankingPMFOfMeasure appendixB1GaussianLatentMeasure
        (appendixB1SourceGaussianMixtureRank s theta)
        (appendixB1SourceGaussianMixtureRank_measurable s theta)
  symm
  refine AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
    appendixB1GaussianLatentMeasure
    (w11CandidateNoiseLaw (appendixB1GaussianMixtureDensity s))
    (fun omega => fun c => appendixB1SourceGaussianMixtureNoise s omega c)
    (appendixB1SourceGaussianMixtureNoise_measurePreserving s hs)
    (appendixB1SourceGaussianMixtureRank s theta)
    (appendixB1SourceGaussianMixtureRank_measurable s theta)
    (fun noise => AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun c => appendixB1Value c + noise c / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun c => noise c)
      (fun c => measurable_pi_apply c) appendixB1Value theta) ?_
  intro omega
  rfl

/-- The corrected B.2 density family and the totalized literal source family
have the same ranking law at every real parameter.  Only the `theta > 0`
restriction is a paper accuracy model. -/
theorem appendixB2GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF
    (s : ℝ) (hs : 0 < s) (theta : ℝ) :
    (appendixB2GaussianMixtureW11Family s hs).dist theta =
      (appendixB2SourceGaussianMixtureFamily s).dist theta := by
  let hregularity := appendixB2GaussianMixture_w11Regularity s hs
  letI : IsProbabilityMeasure
      (w11CandidateNoiseLaw (appendixB2GaussianMixtureDensity s)) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization 1
      (appendixB2GaussianMixtureDensity s) hregularity.normalized
  change
    paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw (appendixB2GaussianMixtureDensity s))
      appendixB2Value theta =
      rumRankingPMFOfMeasure appendixB2GaussianLatentMeasure
        (appendixB2SourceGaussianMixtureRank s theta)
        (appendixB2SourceGaussianMixtureRank_measurable s theta)
  symm
  refine AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eq_of_measurePreserving
    appendixB2GaussianLatentMeasure
    (w11CandidateNoiseLaw (appendixB2GaussianMixtureDensity s))
    (fun omega => fun c => appendixB2SourceGaussianMixtureNoise s omega c)
    (appendixB2SourceGaussianMixtureNoise_measurePreserving s hs)
    (appendixB2SourceGaussianMixtureRank s theta)
    (appendixB2SourceGaussianMixtureRank_measurable s theta)
    (fun noise => AppliedModelingLib.SocialChoice.Ranking.rankByScore
      (fun c => appendixB2Value c + noise c / theta))
    (paper_appendixA_scaledNoise_rankByScore_measurable
      (fun noise : Candidate 1 → ℝ => fun c => noise c)
      (fun c => measurable_pi_apply c) appendixB2Value theta) ?_
  intro omega
  rfl

private theorem accuracyFamily_eq_of_dist_value
    {n : ℕ} (F G : AccuracyFamily n)
    (hdist : F.dist = G.dist) (hvalue : F.value = G.value) : F = G := by
  cases F
  cases G
  cases hdist
  cases hvalue
  rfl

/-- The corrected explicit-density B.1 family and the literal B.1
common-source latent family are the same `AccuracyFamily`. -/
theorem appendixB1GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily
    (s : ℝ) (hs : 0 < s) :
    appendixB1GaussianMixtureW11Family s hs =
      appendixB1SourceGaussianMixtureFamily s := by
  apply accuracyFamily_eq_of_dist_value
  · funext theta
    exact appendixB1GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF s hs theta
  · rfl

/-- The paper's literal B.1 common-source Gaussian-mixture family satisfies
the corrected full Definition 1 package. -/
noncomputable def appendixB1SourceGaussianMixture_correctedW11Definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB1SourceGaussianMixtureFamily s) rum3Ranking012 := by
  rw [← appendixB1GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily s hs]
  exact appendixB1GaussianMixture_correctedW11Definition1 s hs

/-- The corrected explicit-density B.2 family and the paper's literal
common-source latent family are the same `AccuracyFamily`. -/
theorem appendixB2GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily
    (s : ℝ) (hs : 0 < s) :
    appendixB2GaussianMixtureW11Family s hs =
      appendixB2SourceGaussianMixtureFamily s := by
  apply accuracyFamily_eq_of_dist_value
  · funext theta
    exact appendixB2GaussianMixtureW11Family_dist_eq_sourceLatentRankingPMF s hs theta
  · rfl

/-- The paper's actual B.2 common-source Gaussian-mixture family satisfies
the corrected full Definition 1 package. -/
noncomputable def appendixB2SourceGaussianMixture_correctedW11Definition1
    (s : ℝ) (hs : 0 < s) :
    CorrectedW11ScaledNoiseDefinition1
      (appendixB2SourceGaussianMixtureFamily s) rum3Ranking012 := by
  rw [← appendixB2GaussianMixtureW11Family_eq_sourceGaussianMixtureFamily s hs]
  exact appendixB2GaussianMixture_correctedW11Definition1 s hs

end

end KR21Monoculture
