import KR21Monoculture.MainTheorems
import KR21Monoculture.W11ArbitraryFiniteCells

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/-!
# Corrected Appendix A / Theorem 5 Definition 1 package

The archival Appendix A Theorem 5 differentiability claim is false under its
printed assumptions.  This module packages the repaired result for the
literal finite iid source-noise experiment.  The added global `W^{1,1}`
regularity, density normalization, and full-support assumptions are all
visible in the constructor below.

The package has the four clauses that the source's Definition 1 uses:
atomwise continuity, differentiability, high-accuracy concentration, and
finite-removal monotonicity.  The last three non-differentiability clauses are
reused only after proving that the iid source-noise law is the required
positive full-dimensional density law; differentiability is transported from
the actual source scaled-noise ranking atom, not from a declaration name.
-/

/--
The full repaired Definition 1 package for a finite scaled-noise RUM.  Its
parent package supplies continuity, concentration, and removal monotonicity;
the extra field is the corrected global-`W^{1,1}` differentiability clause.
-/
structure CorrectedW11ScaledNoiseDefinition1 {n : ℕ}
    (F : AccuracyFamily n) (center : Ranking n)
    extends PaperAppendixAScaledNoiseDefinition1Consequence F center where
  atom_differentiable :
    ∀ theta, 0 < theta →
      ∀ pi : Ranking n,
        DifferentiableAt ℝ (fun theta' => ((F.dist theta') pi).toReal) theta

/--
The literal source family for the corrected theorem: draw iid noise with
density `f`, then rank `value i + noise i / theta`.  Density normalization is
an input because this is an actual probability model, rather than merely an
algebraic score density.
-/
noncomputable def w11CorrectedScaledNoiseFamily {n : ℕ}
    (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) : AccuracyFamily n := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  exact
    { dist := fun theta =>
        paper_appendixA_scaledNoiseRankingPMF
          (w11CandidateNoiseLaw (n := n) f) value theta
      value := value }

/--
The distribution field of the corrected source family is the literal
scaled-noise ranking PMF.  Keeping this as a named proposition-level bridge
prevents downstream source-facing theorems from unfolding the dependent family
construction during elaboration.
-/
theorem w11CorrectedScaledNoiseFamily_dist_eq_scaledNoiseRankingPMF
    {n : ℕ} (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (theta : ℝ)
    [IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f)] :
    (w11CorrectedScaledNoiseFamily f hnormalized value).dist theta =
      paper_appendixA_scaledNoiseRankingPMF
        (w11CandidateNoiseLaw (n := n) f) value theta := by
  rfl

/--
An atom of the corrected source family is the corresponding atom of the raw
rank-PMF used by the finite-union concentration argument.  The measurability
witness is an explicit argument so downstream proofs can reuse their existing
ranking-event witness without unfolding either PMF wrapper.
-/
theorem w11CorrectedScaledNoiseFamily_atom_eq_rankingPMFOfMeasure
    {n : ℕ} (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (theta : ℝ) (pi : Ranking n)
    [IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f)]
    (hrank : Measurable (fun noise : Candidate n → ℝ =>
      rankByScore (fun i => value i + noise i / theta))) :
    ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta pi).toReal =
      ((AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        (w11CandidateNoiseLaw (n := n) f)
        (fun noise => rankByScore (fun i => value i + noise i / theta)) hrank) pi).toReal := by
  rw [w11CorrectedScaledNoiseFamily_dist_eq_scaledNoiseRankingPMF]
  rfl

/--
Each ranking-PMF atom of the repaired source family is exactly the literal
source scaled-noise ranking event mass.  This is the semantic bridge used by
the differentiability clause below.
-/
theorem w11CorrectedScaledNoiseFamily_atom_eq_sourceScaledNoiseRankingAtom
    {n : ℕ} (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n → ℝ) (theta : ℝ) (pi : Ranking n) :
    ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta pi).toReal =
      w11CandidateScaledNoiseRankingAtom f value pi theta := by
  classical
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  change
    ((paper_appendixA_scaledNoiseRankingPMF
      (w11CandidateNoiseLaw (n := n) f) value theta) pi).toReal =
      w11CandidateScaledNoiseRankingAtom f value pi theta
  rw [← AppliedModelingLib.pmfProb_singleton]
  change AppliedModelingLib.pmfProb
      (AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure
        (w11CandidateNoiseLaw (n := n) f)
        (fun noise => rankByScore (fun i => value i + noise i / theta))
        (paper_appendixA_scaledNoise_rankByScore_measurable
          (Ω := Candidate n → ℝ)
          (fun noise i => noise i)
          (fun i => measurable_pi_apply i) value theta))
      (fun ranking => ranking = pi) =
        w11CandidateScaledNoiseRankingAtom f value pi theta
  rw [AppliedModelingLib.SocialChoice.Ranking.rankingPMFOfMeasure_eventProb]
  rfl

/--
The corrected Appendix A / Theorem 5 conclusion on an arbitrary finite
candidate carrier.  This is not the archival statement: it explicitly adds
global absolute continuity with an `L¹` derivative, source-density
normalization, and full support.  Under those assumptions the actual iid
source-noise ranking PMF satisfies all four Definition 1 clauses.
-/
noncomputable def correctedW11ScaledNoiseDefinition1_of_source
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
    CorrectedW11ScaledNoiseDefinition1
      (w11CorrectedScaledNoiseFamily f hnormalized value) center := by
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  let D : (Candidate n → ℝ) → ℝ≥0∞ :=
    w11CandidateScoreDensityENN f (fun _ : Candidate n => 0) 0
  have hD : Measurable D := by
    dsimp [D]
    exact measurable_w11CandidateScoreDensityENN f hf_measurable
      (fun _ : Candidate n => 0) 0
  have hDpos : ∀ noise, D noise ≠ 0 := by
    intro noise
    apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    unfold w11CandidateScoreDensity
    exact Finset.prod_pos fun i _ => by
      simpa using hfullSupport (noise i)
  have hmu : w11CandidateNoiseLaw (n := n) f =
      (volume : Measure (Candidate n → ℝ)).withDensity D := by
    change w11CandidateNoiseLaw (n := n) f =
      w11CandidateScoreLaw f (fun _ : Candidate n => 0) 0
    rw [w11CandidateScoreLaw_eq_map_w11CandidateNoiseLaw
      n f hf hf_measurable (fun x => (hfullSupport x).le)
      (fun _ : Candidate n => 0) 0]
    have hidentity :
        w11CandidateAdditiveScoreMap (fun _ : Candidate n => 0) 0 = id := by
      funext noise
      funext i
      simp [w11CandidateAdditiveScoreMap]
    rw [hidentity, Measure.map_id]
  have hdist : ∀ theta, 0 < theta →
      (w11CorrectedScaledNoiseFamily f hnormalized value).dist theta =
        paper_appendixA_scaledNoiseRankingPMF
          (w11CandidateNoiseLaw (n := n) f) value theta := by
    intro theta _
    rfl
  let base : PaperAppendixAScaledNoiseDefinition1Consequence
      (w11CorrectedScaledNoiseFamily f hnormalized value) center :=
    paper_appendixA_scaledNoise_definition1_consequence_of_fullSupport_source
      center (w11CandidateNoiseLaw (n := n) f) D hD hDpos hmu hcenter hdist
  refine { base with atom_differentiable := ?_ }
  intro theta htheta pi
  apply (w11CandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
    n f derivative hf hderivative hf_measurable (fun x => (hfullSupport x).le)
    absolute_continuity derivative_ae_eq value pi htheta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun theta' =>
    (w11CorrectedScaledNoiseFamily_atom_eq_sourceScaledNoiseRankingAtom
      f hnormalized value theta' pi)

end KR21Monoculture
