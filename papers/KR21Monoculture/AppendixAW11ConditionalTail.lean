import KR21Monoculture.AppendixAConditionalTail
import KR21Monoculture.W11Definition1Correction

open AppliedModelingLib MeasureTheory ProbabilityTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal

namespace KR21Monoculture

noncomputable section

/-!
# Appendix A conditional-tail formula for the corrected W1,1 source law

The conditional-tail calculation separates candidate `0` from the remaining
finite iid source-noise coordinates.  This module proves that this product
law is the literal corrected W1,1 source law after the displayed coordinate
reassembly, and derives its no-tie condition from the finite-dimensional
density representation.  It does not take no ties as an assumption.
-/

/-- The measurable coordinate reassembly used by the A.1 product formula. -/
noncomputable def sourceAppendixAProductNoiseEquiv (n : Nat) :
    (Prod (Fin (n + 1) -> Real) Real) ≃ᵐ (Candidate n -> Real) :=
  (MeasurableEquiv.prodComm :
      (Prod (Fin (n + 1) -> Real) Real) ≃ᵐ
        (Prod Real (Fin (n + 1) -> Real))).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Candidate n => Real) 0).symm

theorem sourceAppendixAProductNoiseEquiv_apply (n : Nat)
    (z : Prod (Fin (n + 1) -> Real) Real) :
    sourceAppendixAProductNoiseEquiv n z = sourceAppendixAProductNoise z := by
  funext c
  rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨d, rfl⟩
  · simp [sourceAppendixAProductNoiseEquiv, sourceAppendixAProductNoise,
      MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
      Fin.insertNthEquiv]
  · simp [sourceAppendixAProductNoiseEquiv, sourceAppendixAProductNoise,
      MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm,
      Fin.insertNthEquiv]

/-- Reassembling the separated A.1 coordinates gives the literal finite iid
corrected-W1,1 source-noise law. -/
theorem sourceAppendixAProductNoiseEquiv_measurePreserving_w11CandidateNoiseLaw
    {n : Nat} (f : Real -> Real)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    MeasurePreserving (sourceAppendixAProductNoiseEquiv n)
      ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
        (w11BaseNoiseLaw f))
      (w11CandidateNoiseLaw (n := n) f) := by
  let mu : Measure Real := w11BaseNoiseLaw f
  let rest : Measure (Fin (n + 1) -> Real) := sourceAppendixARestNoiseLaw n mu
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    exact w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  letI : IsProbabilityMeasure rest := by
    dsimp [rest, sourceAppendixARestNoiseLaw]
    infer_instance
  letI : forall _ : Candidate n, SigmaFinite mu := fun _ => inferInstance
  have hsplit : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Candidate n => Real) 0)
      (w11CandidateNoiseLaw (n := n) f) (mu.prod rest) := by
    simpa [w11CandidateNoiseLaw, rest, sourceAppendixARestNoiseLaw] using
      (measurePreserving_piFinSuccAbove
        (fun _ : Candidate n => mu) 0)
  have hswap : MeasurePreserving
      (MeasurableEquiv.prodComm :
        (Prod (Fin (n + 1) -> Real) Real) ≃ᵐ
          (Prod Real (Fin (n + 1) -> Real)))
      (rest.prod mu) (mu.prod rest) := by
    exact Measure.measurePreserving_swap
  have hinverse : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Candidate n => Real) 0).symm
      (mu.prod rest) (w11CandidateNoiseLaw (n := n) f) :=
    MeasurePreserving.symm _ hsplit
  simpa [sourceAppendixAProductNoiseEquiv, mu, rest] using hswap.trans hinverse

theorem sourceAppendixAProductNoise_measurePreserving_w11CandidateNoiseLaw
    {n : Nat} (f : Real -> Real)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    MeasurePreserving sourceAppendixAProductNoise
      ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
        (w11BaseNoiseLaw f))
      (w11CandidateNoiseLaw (n := n) f) := by
  have hfun : sourceAppendixAProductNoise =
      sourceAppendixAProductNoiseEquiv n := by
    funext z
    exact (sourceAppendixAProductNoiseEquiv_apply n z).symm
  rw [hfun]
  exact sourceAppendixAProductNoiseEquiv_measurePreserving_w11CandidateNoiseLaw
    (n := n) f hnormalized

/-- The corrected finite iid source-noise law is absolutely continuous with
respect to finite product volume, with its literal product density. -/
theorem w11CandidateNoiseLaw_eq_zeroScoreDensity
    {n : Nat} (f : Real -> Real)
    (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x) :
    w11CandidateNoiseLaw (n := n) f =
      (volume : Measure (Candidate n -> Real)).withDensity
        (w11CandidateScoreDensityENN f (fun _ : Candidate n => 0) 0) := by
  change w11CandidateNoiseLaw (n := n) f =
    w11CandidateScoreLaw f (fun _ : Candidate n => 0) 0
  rw [w11CandidateScoreLaw_eq_map_w11CandidateNoiseLaw
    n f hf hf_measurable h_nonnegative (fun _ : Candidate n => 0) 0]
  have hidentity :
      w11CandidateAdditiveScoreMap (fun _ : Candidate n => 0) 0 = id := by
    funext noise
    funext i
    simp [w11CandidateAdditiveScoreMap]
  rw [hidentity, Measure.map_id]

/-- The A.1 separated product law has no score ties because its reassembly is
the absolutely continuous finite iid corrected-W1,1 noise law. -/
theorem sourceAppendixAProductNoise_noTie_ae_of_w11Density
    {n : Nat} (f : Real -> Real)
    (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real) {theta : Real} (htheta : 0 < theta) :
    ∀ᵐ z ∂((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
      (w11BaseNoiseLaw f)),
      ∀ i j : Candidate n, i ≠ j →
        value i + sourceAppendixAProductNoise z i / theta ≠
          value j + sourceAppendixAProductNoise z j / theta := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  letI : IsProbabilityMeasure (w11CandidateNoiseLaw (n := n) f) :=
    w11CandidateNoiseLaw_isProbabilityMeasure_of_base_normalization n f hnormalized
  let D : (Candidate n -> Real) -> ENNReal :=
    w11CandidateScoreDensityENN f (fun _ : Candidate n => 0) 0
  have hmu : w11CandidateNoiseLaw (n := n) f =
      (volume : Measure (Candidate n -> Real)).withDensity D := by
    simpa [D] using
      (w11CandidateNoiseLaw_eq_zeroScoreDensity (n := n) f hf hf_measurable
        h_nonnegative)
  have hnoTieCandidate :
      ∀ᵐ noise ∂w11CandidateNoiseLaw (n := n) f,
        ∀ i j : Candidate n, i ≠ j →
          value i + noise i / theta ≠ value j + noise j / theta :=
    paper_appendixA_scaledNoise_noTie_ae_of_fullSupport_density
      (w11CandidateNoiseLaw (n := n) f) D hmu value htheta
  refine ae_of_ae_map
    (μ := (sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
      (w11BaseNoiseLaw f))
    (f := sourceAppendixAProductNoise)
    (p := fun noise => ∀ i j : Candidate n, i ≠ j →
      value i + noise i / theta ≠ value j + noise j / theta)
    (sourceAppendixAProductNoise_measurePreserving_w11CandidateNoiseLaw
      (n := n) f hnormalized).measurable.aemeasurable ?_
  rw [(sourceAppendixAProductNoise_measurePreserving_w11CandidateNoiseLaw
    (n := n) f hnormalized).map_eq]
  exact hnoTieCandidate

/-- The source's displayed A.1 conditional-tail formula for the literal
corrected finite iid W1,1 model: every coordinate has law
`w11BaseNoiseLaw f`, and the separated `(rest, epsilon_0)` law is
`(sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod (w11BaseNoiseLaw f)`.
The no-tie bridge is derived above from that model's finite-dimensional
density representation, not assumed as a conclusion-like premise. -/
theorem sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral_of_w11Density
    {n : Nat} (f : Real -> Real)
    (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : forall x, 0 <= f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate n -> Real) {theta : Real} (htheta : 0 < theta) :
    AppliedModelingLib.measureProb
        ((sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f)).prod
          (w11BaseNoiseLaw f))
        (fun z => SourceAppendixATopEvent value
          (sourceAppendixAProductNoise z) theta 0) =
      ∫ rest : Fin (n + 1) -> Real,
        AppliedModelingLib.measureProb (w11BaseNoiseLaw f)
          (fun epsilon => SourceAppendixAFirstTail value theta rest epsilon)
        ∂sourceAppendixARestNoiseLaw n (w11BaseNoiseLaw f) := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  exact sourceAppendixA_selectedTop_probability_eq_conditionalTail_integral
    (w11BaseNoiseLaw f) value htheta
    (sourceAppendixAProductNoise_noTie_ae_of_w11Density
      (n := n) f hf hf_measurable h_nonnegative hnormalized value htheta)

end

end KR21Monoculture
