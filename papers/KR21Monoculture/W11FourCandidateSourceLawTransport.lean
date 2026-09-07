import KR21Monoculture.W11SourceLawTransport
import KR21Monoculture.W11FourCandidateCells

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped ENNReal

namespace KR21Monoculture

/-!
# Four-coordinate source-noise transport for the corrected Theorem 5 route

This module completes the concrete source-law bridge for the source paper's
four-candidate carrier `Candidate 2 = Fin 4`.  The source experiment is four
iid draws from the density `f` on the explicit nested product
`((R x R) x R) x R`.  A coordinatewise additive map sends it to the concrete
four-score law from `W11FourCandidateCells`.

The proof is intentionally a sequence of checked one-dimensional translation
and binary-product pushforwards.  It does not identify an arbitrary finite
function carrier with a product measure.
-/

/-- Four independent source-noise coordinates on the explicit source-four carrier. -/
noncomputable def w11FourCandidateNoiseLaw (f : ℝ → ℝ) :
    Measure (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).prod
    (w11BaseNoiseLaw f)).prod (w11BaseNoiseLaw f)

/-- Four iid normalized source-noise draws form an actual probability law. -/
theorem w11FourCandidateNoiseLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1) :
    IsProbabilityMeasure (w11FourCandidateNoiseLaw f) := by
  letI : IsProbabilityMeasure (w11BaseNoiseLaw f) :=
    w11BaseNoiseLaw_isProbabilityMeasure_of_base_normalization f hnormalized
  unfold w11FourCandidateNoiseLaw
  infer_instance

/-- Add the four deterministic value-dependent score shifts to source noise. -/
def w11FourCandidateAdditiveScoreMap (value : Candidate 2 → ℝ) (theta : ℝ) :
    ((ℝ × ℝ) × ℝ) × ℝ → ((ℝ × ℝ) × ℝ) × ℝ :=
  fun noise =>
    (((noise.1.1.1 + theta * value 0, noise.1.1.2 + theta * value 1),
      noise.1.2 + theta * value 2), noise.2 + theta * value 3)

/-- The displayed four-coordinate additive score map is measurable. -/
theorem measurable_w11FourCandidateAdditiveScoreMap
    (value : Candidate 2 → ℝ) (theta : ℝ) :
    Measurable (w11FourCandidateAdditiveScoreMap value theta) := by
  unfold w11FourCandidateAdditiveScoreMap
  fun_prop

/--
The corrected four-score law is exactly the pushforward of four iid
source-noise draws under the displayed coordinatewise additive score map.
Each density and product-measure conversion is made explicit below.
-/
theorem fourCandidateScoreLaw_eq_map_w11FourCandidateNoiseLaw
    (f : ℝ → ℝ) (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 2 → ℝ) (theta : ℝ) :
    fourCandidateScoreLaw f value theta =
      (w11FourCandidateNoiseLaw f).map
        (w11FourCandidateAdditiveScoreMap value theta) := by
  letI : IsFiniteMeasure (w11BaseNoiseLaw f) := by
    unfold w11BaseNoiseLaw
    exact MeasureTheory.isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  let g0 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 0))
  let g1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 1))
  let g2 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 2))
  let g3 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 3))
  have hg0 : Measurable g0 := by
    dsimp [g0]
    exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hg1 : Measurable g1 := by
    dsimp [g1]
    exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hg2 : Measurable g2 := by
    dsimp [g2]
    exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hg3 : Measurable g3 := by
    dsimp [g3]
    exact (hf_measurable.comp (measurable_id.sub measurable_const)).ennreal_ofReal
  have hg01 : Measurable (fun z : ℝ × ℝ => g0 z.1 * g1 z.2) := by
    fun_prop
  have hg012 : Measurable (fun z : (ℝ × ℝ) × ℝ =>
      (g0 z.1.1 * g1 z.1.2) * g2 z.2) := by
    fun_prop
  have hscore :
      fourCandidateScoreLaw f value theta =
        (((w11TranslatedNoiseLaw f (theta * value 0)).prod
          (w11TranslatedNoiseLaw f (theta * value 1))).prod
            (w11TranslatedNoiseLaw f (theta * value 2))).prod
              (w11TranslatedNoiseLaw f (theta * value 3)) := by
    change
      (((volume.prod volume).prod volume).prod volume).withDensity
          (fourCandidateScoreDensityENN f value theta) =
        (((volume.withDensity g0).prod (volume.withDensity g1)).prod
          (volume.withDensity g2)).prod (volume.withDensity g3)
    rw [prod_withDensity hg0 hg1, prod_withDensity hg01 hg2,
      prod_withDensity hg012 hg3]
    congr 1
    funext z
    simp [fourCandidateScoreDensityENN, fourCandidateScoreDensity,
      threeCandidateScoreDensity, fourCandidateFirstThreeValue, g0, g1, g2, g3]
    rw [ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg (h_nonnegative _) (h_nonnegative _))
            (h_nonnegative _)),
      ENNReal.ofReal_mul (mul_nonneg (h_nonnegative _) (h_nonnegative _)),
      ENNReal.ofReal_mul (h_nonnegative _)]
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
  have h2 :
      (w11BaseNoiseLaw f).map (fun x => x + theta * value 2) =
        w11TranslatedNoiseLaw f (theta * value 2) :=
    w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
      f hf h_nonnegative (theta * value 2)
  have h3 :
      (w11BaseNoiseLaw f).map (fun x => x + theta * value 3) =
        w11TranslatedNoiseLaw f (theta * value 3) :=
    w11BaseNoiseLaw_map_addRight_eq_translatedNoiseLaw
      f hf h_nonnegative (theta * value 3)
  have hm0 : Measurable (fun x : ℝ => x + theta * value 0) :=
    measurable_id.add measurable_const
  have hm1 : Measurable (fun x : ℝ => x + theta * value 1) :=
    measurable_id.add measurable_const
  have hm2 : Measurable (fun x : ℝ => x + theta * value 2) :=
    measurable_id.add measurable_const
  have hm3 : Measurable (fun x : ℝ => x + theta * value 3) :=
    measurable_id.add measurable_const
  have hmap01 :
      ((w11BaseNoiseLaw f).map (fun x : ℝ => x + theta * value 0)).prod
        ((w11BaseNoiseLaw f).map (fun x : ℝ => x + theta * value 1)) =
      ((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).map
        (Prod.map (fun x : ℝ => x + theta * value 0)
          (fun x : ℝ => x + theta * value 1)) :=
    Measure.map_prod_map (w11BaseNoiseLaw f) (w11BaseNoiseLaw f) hm0 hm1
  have hmap012 :
      (((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).map
          (Prod.map (fun x : ℝ => x + theta * value 0)
            (fun x : ℝ => x + theta * value 1))).prod
        ((w11BaseNoiseLaw f).map (fun x : ℝ => x + theta * value 2)) =
      (((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).prod
        (w11BaseNoiseLaw f)).map
        (Prod.map
          (Prod.map (fun x : ℝ => x + theta * value 0)
            (fun x : ℝ => x + theta * value 1))
          (fun x : ℝ => x + theta * value 2)) :=
    Measure.map_prod_map ((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f))
      (w11BaseNoiseLaw f) (hm0.prodMap hm1) hm2
  have hmap0123 :
      ((((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).prod
          (w11BaseNoiseLaw f)).map
          (Prod.map
            (Prod.map (fun x : ℝ => x + theta * value 0)
              (fun x : ℝ => x + theta * value 1))
            (fun x : ℝ => x + theta * value 2))).prod
        ((w11BaseNoiseLaw f).map (fun x : ℝ => x + theta * value 3)) =
      ((((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).prod
          (w11BaseNoiseLaw f)).prod (w11BaseNoiseLaw f)).map
        (Prod.map
          (Prod.map
            (Prod.map (fun x : ℝ => x + theta * value 0)
              (fun x : ℝ => x + theta * value 1))
            (fun x : ℝ => x + theta * value 2))
          (fun x : ℝ => x + theta * value 3)) :=
    Measure.map_prod_map
      (((w11BaseNoiseLaw f).prod (w11BaseNoiseLaw f)).prod
        (w11BaseNoiseLaw f))
      (w11BaseNoiseLaw f) ((hm0.prodMap hm1).prodMap hm2) hm3
  calc
    fourCandidateScoreLaw f value theta =
        (((w11TranslatedNoiseLaw f (theta * value 0)).prod
          (w11TranslatedNoiseLaw f (theta * value 1))).prod
            (w11TranslatedNoiseLaw f (theta * value 2))).prod
              (w11TranslatedNoiseLaw f (theta * value 3)) := hscore
    _ = ((((w11BaseNoiseLaw f).map (fun x => x + theta * value 0)).prod
          ((w11BaseNoiseLaw f).map (fun x => x + theta * value 1))).prod
            ((w11BaseNoiseLaw f).map (fun x => x + theta * value 2))).prod
              ((w11BaseNoiseLaw f).map (fun x => x + theta * value 3)) := by
      rw [h0, h1, h2, h3]
    _ = (w11FourCandidateNoiseLaw f).map
          (w11FourCandidateAdditiveScoreMap value theta) := by
      rw [hmap01, hmap012, hmap0123]
      rfl

/-- The source-scaled-noise ranking atom on the explicit source-four carrier. -/
noncomputable def w11FourCandidateScaledNoiseRankingAtom
    (f : ℝ → ℝ) (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) : ℝ :=
  (w11FourCandidateNoiseLaw f).real
    {noise | rankByScore
      (fun i => value i + fourCandidateScoreVector noise i / theta) = pi}

/-- The additive score map has the literal four-coordinate score-vector form. -/
theorem fourCandidateScoreVector_w11FourCandidateAdditiveScoreMap
    (value : Candidate 2 → ℝ) (theta : ℝ) (noise : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreVector (w11FourCandidateAdditiveScoreMap value theta noise) =
      fun i => theta * value i + fourCandidateScoreVector noise i := by
  funext i
  fin_cases i <;> simp [w11FourCandidateAdditiveScoreMap, add_comm]

/-- The additive source-ranking cell is the literal preimage of the score-space ranking cell. -/
theorem w11FourCandidateAdditiveRankingCell_eq_preimage
    (value : Candidate 2 → ℝ) (theta : ℝ) (pi : Ranking 2) :
    {noise : ((ℝ × ℝ) × ℝ) × ℝ |
      rankByScore
        (fun i => theta * value i + fourCandidateScoreVector noise i) = pi} =
      (w11FourCandidateAdditiveScoreMap value theta) ⁻¹'
        fourCandidateRankingEvent pi := by
  ext noise
  simp only [Set.mem_setOf_eq, Set.mem_preimage, fourCandidateRankingEvent]
  rw [fourCandidateScoreVector_w11FourCandidateAdditiveScoreMap]

/--
At positive accuracy, the source four-noise atom equals the actual
four-score-law atom.  The equality combines the proved positive-score scaling
identity, a literal ranking-cell preimage, and the checked four-product
pushforward law.
-/
theorem w11FourCandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume) (hf_measurable : Measurable f)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 2 → ℝ)
    (pi : Ranking 2) {theta : ℝ} (htheta : 0 < theta) :
    w11FourCandidateScaledNoiseRankingAtom f value pi theta =
      fourCandidateScoreLawRankingAtom f value pi theta := by
  have hscaled :
      {noise : ((ℝ × ℝ) × ℝ) × ℝ |
        rankByScore
          (fun i => value i + fourCandidateScoreVector noise i / theta) = pi} =
        {noise : ((ℝ × ℝ) × ℝ) × ℝ |
          rankByScore
            (fun i => theta * value i + fourCandidateScoreVector noise i) = pi} :=
    scaledNoiseRankingCell_preimage_eq_additiveScore value fourCandidateScoreVector htheta pi
  unfold w11FourCandidateScaledNoiseRankingAtom fourCandidateScoreLawRankingAtom
  rw [hscaled, w11FourCandidateAdditiveRankingCell_eq_preimage,
    fourCandidateScoreLaw_eq_map_w11FourCandidateNoiseLaw
      f hf hf_measurable h_nonnegative value theta]
  change
    ((w11FourCandidateNoiseLaw f)
      ((w11FourCandidateAdditiveScoreMap value theta) ⁻¹'
        fourCandidateRankingEvent pi)).toReal =
      ((Measure.map (w11FourCandidateAdditiveScoreMap value theta)
        (w11FourCandidateNoiseLaw f))
        (fourCandidateRankingEvent pi)).toReal
  rw [Measure.map_apply (measurable_w11FourCandidateAdditiveScoreMap value theta)
    (measurableSet_fourCandidateRankingEvent pi)]

/--
The source-scaled four-candidate atom is differentiable under the accepted
global `W^{1,1}` repair, through the checked source-law pushforward.
-/
theorem w11FourCandidateScaledNoiseRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (hf_measurable : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) {theta : ℝ} (htheta : 0 < theta) :
    DifferentiableAt ℝ (w11FourCandidateScaledNoiseRankingAtom f value pi) theta := by
  apply (fourCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    f derivative hf hderivative h_nonnegative absolute_continuity derivative_ae_eq
    value pi theta).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds htheta] with t ht
  exact (w11FourCandidateScaledNoiseRankingAtom_eq_scoreLawRankingAtom
    f hf hf_measurable h_nonnegative value pi ht)

end KR21Monoculture
