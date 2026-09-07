import KR21Monoculture.W11Definition1Correction
import KR21Monoculture.Definition1FullRemoval

/-!
# Full corrected `W^{1,1}` Definition 1 theorem

`CorrectedW11ScaledNoiseDefinition1` is a useful construction package, but it
is `Type`-valued and its inherited removal field only exposes the
singleton-removal fragment used by the original Theorem 1 proof.  This module
states the repaired source-facing conclusion as one proposition.  Its terminal
conclusion displays every Definition 1 clause: continuity, differentiability,
high-accuracy concentration, weak monotonicity for every nonempty remaining
finite set, and strict improvement for the full candidate set.

The assumptions deliberately remain stronger than the archival Theorem 5:
global absolute continuity with an integrable derivative, density
normalization, and pointwise full support are explicit.  No fact is inferred
from a declaration name or a witness type.
-/

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal Topology

namespace KR21Monoculture

/--
The full repaired Appendix A / Theorem 5 Definition 1 conclusion for the
literal finite iid scaled-noise source family.  The result is proposition
valued so a source audit can inspect the five obligations directly rather than
accepting a structure witness as a proof endpoint.

The `remaining` set is the set left after source-style removals.  Requiring it
to be nonempty is exactly the condition that the partial ranking still has a
top candidate.  The final conjunct is the strict `S = ∅` / full-set clause.
-/
theorem correctedW11ScaledNoiseDefinition1_full_of_source
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
      EpsilonContinuousAt
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ theta, 0 < theta → ∀ pi : Ranking n,
      DifferentiableAt ℝ
        (fun theta' =>
          ((w11CorrectedScaledNoiseFamily f hnormalized value).dist theta' pi).toReal)
        theta) ∧
    (∀ lower delta, 0 < delta → ∃ hi, lower < hi ∧ ∀ pi : Ranking n,
      |((w11CorrectedScaledNoiseFamily f hnormalized value).dist hi pi).toReal -
        ((PMF.pure center : PMF (Ranking n)) pi).toReal| < delta) ∧
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
  classical
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  let certificate : CorrectedW11ScaledNoiseDefinition1
      (w11CorrectedScaledNoiseFamily f hnormalized value) center :=
    correctedW11ScaledNoiseDefinition1_of_source
      f derivative hf hderivative hf_measurable hfullSupport absolute_continuity
      derivative_ae_eq hnormalized value center hcenter
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
  have hfull_removal :
      ∀ thetaA thetaH, 0 < thetaH → thetaH < thetaA →
        (∀ remaining : Finset (Candidate n), remaining.Nonempty →
          expectedBestInSet
              ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
              value remaining ≤
            expectedBestInSet
              ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
              value remaining) ∧
          expectedBestInSet
              ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaH)
              value Finset.univ <
            expectedBestInSet
              ((w11CorrectedScaledNoiseFamily f hnormalized value).dist thetaA)
              value Finset.univ := by
    intro thetaA thetaH hthetaH hthetaHA
    have hthetaA : 0 < thetaA := lt_trans hthetaH hthetaHA
    have hrawRank :
        Measurable (fun noise : Candidate n → ℝ =>
          rankByScore (fun i => value i + noise i / thetaH)) :=
      paper_appendixA_scaledNoise_rankByScore_measurable
        (Ω := Candidate n → ℝ)
        (fun noise c => noise c)
        (fun c => measurable_pi_apply c)
        value thetaH
    have haccurateRank :
        Measurable (fun noise : Candidate n → ℝ =>
          rankByScore (fun i => value i + noise i / thetaA)) :=
      paper_appendixA_scaledNoise_rankByScore_measurable
        (Ω := Candidate n → ℝ)
        (fun noise c => noise c)
        (fun c => measurable_pi_apply c)
        value thetaA
    let i0 : Fin (n + 1) := 0
    have hvalue :
        (w11CorrectedScaledNoiseFamily f hnormalized value).value
            (center i0.succ) <
          (w11CorrectedScaledNoiseFamily f hnormalized value).value
            (center i0.castSucc) := by
      simpa [w11CorrectedScaledNoiseFamily] using hcenter i0
    exact
      paper_definition1_full_removal_monotonicity_of_scaledNoise_fullSupport_density
        (F := w11CorrectedScaledNoiseFamily f hnormalized value)
        (thetaA := thetaA) (thetaH := thetaH)
        (w11CandidateNoiseLaw (n := n) f) D hD hDpos hmu hthetaH hthetaHA
        hrawRank haccurateRank
        (by rfl) (by rfl)
        (low := center i0.succ) (high := center i0.castSucc)
        hvalue
  exact ⟨certificate.toPaperAppendixAScaledNoiseDefinition1Consequence.dist_atom_continuity,
    certificate.atom_differentiable,
    certificate.toPaperAppendixAScaledNoiseDefinition1Consequence.atomwise_concentration,
    fun thetaA thetaH hthetaH hthetaHA =>
      (hfull_removal thetaA thetaH hthetaH hthetaHA).1,
    fun thetaA thetaH hthetaH hthetaHA =>
      (hfull_removal thetaA thetaH hthetaH hthetaHA).2⟩

end KR21Monoculture
