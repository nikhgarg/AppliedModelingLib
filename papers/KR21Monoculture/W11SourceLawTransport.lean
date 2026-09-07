import KR21Monoculture.W11RankingCells
import KR21Monoculture.W11ScoreTransport
import Mathlib.MeasureTheory.Function.JacobianOneDim

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal

namespace KR21Monoculture

/-!
# Source-noise transport for the corrected Theorem 5 route

The score-space density used by the corrected `W^{1,1}` argument must be
connected to an actual source noise experiment.  This file begins that bridge
for the explicit two-candidate carrier.  It proves that translating a
one-dimensional noise law with density `f` produces the translated density
`x |-> f (x - shift)`, then uses product measures to identify the two-score
law with the pushforward of two iid source-noise draws.

No arbitrary finite-product transport is asserted here.
-/

/-- The one-dimensional source noise law associated with a nonnegative density. -/
noncomputable def w11BaseNoiseLaw (f : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f x))

/-- The source noise law after adding a deterministic score shift. -/
noncomputable def w11TranslatedNoiseLaw (f : ℝ → ℝ) (shift : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (f (x - shift)))

/-- Base-density normalization makes the one-dimensional source noise law probabilistic. -/
theorem w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11BaseNoiseLaw f) := by
  unfold w11BaseNoiseLaw
  exact isProbabilityMeasure_withDensity_of_lintegral_eq_one volume
    (fun x => ENNReal.ofReal (f x)) hnormalized

/--
Translating the source noise law by `shift` gives precisely its displayed
translated density.  The proof is a change of variables, not a density-name
identification.
-/
theorem w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
    (f : ℝ → ℝ) (hf : Integrable f volume) (h_nonnegative : ∀ x, 0 ≤ f x)
    (shift : ℝ) :
    (w11BaseNoiseLaw f).map (fun x => x + shift) =
      w11TranslatedNoiseLaw f shift := by
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight shift).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ : ℝ => 1) x) x := fun _ =>
    (hasDerivAt_id _).sub_const shift
  have hshift_integrable : Integrable (fun x => f (x - shift)) volume :=
    hf.comp_sub_right shift
  change (volume.withDensity fun x => ENNReal.ofReal (f x)).map e.symm =
    volume.withDensity (fun x => ENNReal.ofReal (f (x - shift)))
  ext s hs
  have hlintegral :
      ENNReal.ofReal (∫ x in s, f (x - shift) ∂volume) =
        ∫⁻ x in s, ENNReal.ofReal (f (x - shift)) ∂volume := by
    simpa only [IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := (volume.restrict s)) hshift_integrable.integrableOn
        (Filter.Eventually.of_forall fun x => h_nonnegative (x - shift)))
  calc
    (volume.withDensity fun x => ENNReal.ofReal (f x)).map e.symm s =
        ENNReal.ofReal (∫ x in s, |(1 : ℝ)| * f (e x) ∂volume) := by
      exact e.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul'
        hs he' (Filter.Eventually.of_forall h_nonnegative) hf
    _ = ENNReal.ofReal (∫ x in s, f (x - shift) ∂volume) := by
      congr 1
      apply setIntegral_congr_ae
      · exact hs
      · filter_upwards with x
        simp [e, Homeomorph.addRight, sub_eq_add_neg]
    _ = ∫⁻ x in s, ENNReal.ofReal (f (x - shift)) ∂volume := hlintegral
    _ = (volume.withDensity fun x => ENNReal.ofReal (f (x - shift))) s := by
      rw [withDensity_apply _ hs]

/-- Two independent source-noise coordinates for the explicit two-candidate model. -/
noncomputable def w11TwoCandidateNoiseLaw (f : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)

/-- Two iid normalized source-noise draws form an actual probability law. -/
theorem w11TwoCandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11TwoCandidateNoiseLaw f) := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  unfold w11TwoCandidateNoiseLaw
  infer_instance

/-- Add the two deterministic value-dependent score shifts to source noise. -/
def w11TwoCandidateAdditiveScoreMap (value : Candidate 0 → ℝ) (theta : ℝ) :
    ℝ × ℝ → ℝ × ℝ :=
  fun noise => (noise.1 + theta * value 0, noise.2 + theta * value 1)

theorem measurable_w11TwoCandidateAdditiveScoreMap
    (value : Candidate 0 → ℝ) (theta : ℝ) :
    Measurable (w11TwoCandidateAdditiveScoreMap value theta) := by
  exact (measurable_fst.add measurable_const).prodMk (measurable_snd.add measurable_const)

/--
The corrected two-score law is exactly the pushforward of two iid source-noise
draws under the displayed additive score map.
-/
theorem twoCandidateScoreLaw_eq_map_w11TwoCandidateNoiseLaw
    (f : ℝ → ℝ) (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 0 → ℝ) (theta : ℝ) :
    twoCandidateScoreLaw f value theta =
      (w11TwoCandidateNoiseLaw f).map
        (w11TwoCandidateAdditiveScoreMap value theta) := by
  letI : IsFiniteMeasure (w11BaseNoiseLaw f) := by
    unfold w11BaseNoiseLaw
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  have h0 :
      (w11BaseNoiseLaw f).map (fun x => x + theta * value 0) =
        w11TranslatedNoiseLaw f (theta * value 0) :=
    w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
      f hf h_nonnegative (theta * value 0)
  have h1 :
      (w11BaseNoiseLaw f).map (fun x => x + theta * value 1) =
        w11TranslatedNoiseLaw f (theta * value 1) :=
    w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
      f hf h_nonnegative (theta * value 1)
  calc
    twoCandidateScoreLaw f value theta =
        (w11TranslatedNoiseLaw f (theta * value 0)).prod
          (w11TranslatedNoiseLaw f (theta * value 1)) := by
      unfold twoCandidateScoreLaw w11TranslatedNoiseLaw
      rw [prod_withDensity]
      · congr 1
        funext z
        simp only [twoCandidateScoreDensityENN, twoCandidateScoreDensity]
        rw [ENNReal.ofReal_mul (h_nonnegative _)]
      · exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
      · exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
    _ = ((w11BaseNoiseLaw f).map (fun x => x + theta * value 0)).prod
          ((w11BaseNoiseLaw f).map (fun x => x + theta * value 1)) := by
      rw [h0, h1]
    _ = (w11TwoCandidateNoiseLaw f).map
          (w11TwoCandidateAdditiveScoreMap value theta) := by
      symm
      change Measure.map
          (Prod.map (fun x : ℝ => x + theta * value 0)
            (fun x : ℝ => x + theta * value 1))
          ((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)) =
        (Measure.map (fun x : ℝ => x + theta * value 0) (w11BaseNoiseLaw f)).prod
          (Measure.map (fun x : ℝ => x + theta * value 1) (w11BaseNoiseLaw f))
      exact (Measure.map_prod_map (w11BaseNoiseLaw f) (w11BaseNoiseLaw f)
        (measurable_id.add measurable_const) (measurable_id.add measurable_const)).symm

/-- The source-scaled-noise ranking atom on the explicit two-noise carrier. -/
noncomputable def w11TwoCandidateScaledNoiseRankingAtom
    (f : ℝ → ℝ) (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) : ℝ :=
  (w11TwoCandidateNoiseLaw f).real
    {noise | rankByScore (fun i => value i + twoCandidateScoreVector noise i / theta) = pi}

/-- The additive score map has exactly the displayed coordinatewise form. -/
theorem twoCandidateScoreVector_w11TwoCandidateAdditiveScoreMap
    (value : Candidate 0 → ℝ) (theta : ℝ) (noise : ℝ × ℝ) :
    twoCandidateScoreVector (w11TwoCandidateAdditiveScoreMap value theta noise) =
      fun i => theta * value i + twoCandidateScoreVector noise i := by
  funext i
  fin_cases i <;> simp [w11TwoCandidateAdditiveScoreMap, add_comm]

/-- The additive source-ranking cell is the literal preimage of the score-space ranking cell. -/
theorem w11TwoCandidateAdditiveRankingCell_eq_preimage
    (value : Candidate 0 → ℝ) (theta : ℝ) (pi : Ranking 0) :
    {noise | rankByScore (fun i => theta * value i + twoCandidateScoreVector noise i) = pi} =
      (w11TwoCandidateAdditiveScoreMap value theta) ⁻¹' twoCandidateRankingEvent pi := by
  ext noise
  simp only [Set.mem_setOf_eq, Set.mem_preimage, twoCandidateRankingEvent]
  rw [twoCandidateScoreVector_w11TwoCandidateAdditiveScoreMap]

/--
At positive accuracy, the source scaled-noise atom equals the actual
score-space-law atom.  This composes the proved ranking-map identity with the
proved pushforward law equality; neither is inferred from declaration names.
-/
theorem w11TwoCandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 0 → ℝ)
    (pi : Ranking 0) {theta : ℝ} (htheta : 0 < theta) :
    w11TwoCandidateScaledNoiseRankingAtom f value pi theta =
      twoCandidateScoreLawRankingAtom f value pi theta := by
  have hscaled :
      {noise : ℝ × ℝ |
        rankByScore (fun i => value i + twoCandidateScoreVector noise i / theta) = pi} =
        {noise : ℝ × ℝ |
          rankByScore (fun i => theta * value i + twoCandidateScoreVector noise i) = pi} :=
    scaledNoiseRankingCell_preimage_eq_additiveScore value twoCandidateScoreVector htheta pi
  unfold w11TwoCandidateScaledNoiseRankingAtom twoCandidateScoreLawRankingAtom
  rw [hscaled, w11TwoCandidateAdditiveRankingCell_eq_preimage,
    twoCandidateScoreLaw_eq_map_w11TwoCandidateNoiseLaw
      f hf hf_measurable h_nonnegative value theta]
  change
    ((w11TwoCandidateNoiseLaw f)
      ((w11TwoCandidateAdditiveScoreMap value theta) ⁻¹'
        twoCandidateRankingEvent pi)).toReal =
      ((Measure.map (w11TwoCandidateAdditiveScoreMap value theta)
        (w11TwoCandidateNoiseLaw f))
        (twoCandidateRankingEvent pi)).toReal
  rw [Measure.map_apply (measurable_w11TwoCandidateAdditiveScoreMap value theta)
      (measurableSet_twoCandidateRankingEvent pi)]

/--
The source-scaled two-candidate atom is differentiable under the accepted
global `W^{1,1}` repair, now through an actual source-law pushforward.
-/
theorem w11TwoCandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) {theta : ℝ} (htheta : 0 < theta) :
    DifferentiableAt ℝ (w11TwoCandidateScaledNoiseRankingAtom f value pi) theta := by
  apply (twoCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    f derivative hf hderivative h_nonnegative absolute_continuity derivative_ae_eq
    value pi theta).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds htheta] with t ht
  exact (w11TwoCandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    f hf hf_measurable h_nonnegative value pi ht)

end KR21Monoculture
