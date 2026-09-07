import KR21Monoculture.W11ScoreNormalization

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Three-candidate ranking cells for the corrected Theorem 5 route

This module gives the next finite-product instance of the corrected
score-space route, for exactly `Candidate 1 = Fin 3`.  Its ambient carrier is
the explicit nested product `((ℝ × ℝ) × ℝ)` with measure
`(volume.prod volume).prod volume`; it does *not* identify that measure with
the library's ambient measure on `Candidate 1 → ℝ`.

The equivalence below records the coordinate correspondence exactly.  The
resulting fixed ranking cells are measurable in the explicit product carrier,
and the three-factor iid `L¹` density has a fixed-event derivative under the
global `W^{1,1}` hypotheses already used by the one-coordinate route.

No arbitrary finite-product, scaled-noise transport, or full Theorem 5 claim
is made here.
-/

/-- The explicit three-score product carrier, reindexed as `Candidate 1 → ℝ`. -/
def threeCandidateScoreVector (z : (ℝ × ℝ) × ℝ) : Candidate 1 → ℝ :=
  fun i => if i = 0 then z.1.1 else if i = 1 then z.1.2 else z.2

@[simp] theorem threeCandidateScoreVector_zero (z : (ℝ × ℝ) × ℝ) :
    threeCandidateScoreVector z 0 = z.1.1 := by
  simp [threeCandidateScoreVector]

@[simp] theorem threeCandidateScoreVector_one (z : (ℝ × ℝ) × ℝ) :
    threeCandidateScoreVector z 1 = z.1.2 := by
  simp [threeCandidateScoreVector]

@[simp] theorem threeCandidateScoreVector_two (z : (ℝ × ℝ) × ℝ) :
    threeCandidateScoreVector z 2 = z.2 := by
  simp [threeCandidateScoreVector]

/--
The carrier reindexing used by this file.  This is a type-level equivalence
only: no product-measure transport is asserted or assumed.
-/
def threeCandidateScoreCarrierEquiv : ((ℝ × ℝ) × ℝ) ≃ (Candidate 1 → ℝ) where
  toFun := threeCandidateScoreVector
  invFun := fun score => ((score 0, score 1), score 2)
  left_inv := by
    intro z
    rcases z with ⟨⟨z0, z1⟩, z2⟩
    simp [threeCandidateScoreVector]
  right_inv := by
    intro score
    funext i
    fin_cases i <;> simp [threeCandidateScoreVector]

/-- The inverse reindexing simply extracts the three displayed coordinates. -/
theorem threeCandidateScoreCarrierEquiv_symm_apply
    (score : Candidate 1 → ℝ) :
    threeCandidateScoreCarrierEquiv.symm score = ((score 0, score 1), score 2) :=
  rfl

@[simp] theorem threeCandidateScoreCarrierEquiv_apply_symm
    (score : Candidate 1 → ℝ) :
    threeCandidateScoreCarrierEquiv (threeCandidateScoreCarrierEquiv.symm score) = score :=
  threeCandidateScoreCarrierEquiv.apply_symm_apply score

@[simp] theorem threeCandidateScoreCarrierEquiv_symm_apply_apply
    (z : (ℝ × ℝ) × ℝ) :
    threeCandidateScoreCarrierEquiv.symm (threeCandidateScoreCarrierEquiv z) = z :=
  threeCandidateScoreCarrierEquiv.symm_apply_apply z

/-- Each coordinate of the explicit three-score carrier is measurable. -/
theorem measurable_threeCandidateScoreVector_coordinate (i : Candidate 1) :
    Measurable (fun z : (ℝ × ℝ) × ℝ => threeCandidateScoreVector z i) := by
  fin_cases i
  · simpa [threeCandidateScoreVector] using
      ((measurable_fst.comp measurable_fst) :
        Measurable (fun z : (ℝ × ℝ) × ℝ => z.1.1))
  · simpa [threeCandidateScoreVector] using
      ((measurable_snd.comp measurable_fst) :
        Measurable (fun z : (ℝ × ℝ) × ℝ => z.1.2))
  · simpa [threeCandidateScoreVector] using
      (measurable_snd : Measurable (fun z : (ℝ × ℝ) × ℝ => z.2))

/-- A fixed three-candidate ranking cell in the explicit product carrier. -/
noncomputable def threeCandidateRankingEvent (pi : Ranking 1) : Set ((ℝ × ℝ) × ℝ) :=
  {z | rankByScore (threeCandidateScoreVector z) = pi}

/-- The product-carrier ranking cell is exactly the preimage under the displayed reindexing. -/
theorem threeCandidateRankingEvent_eq_preimage (pi : Ranking 1) :
    threeCandidateRankingEvent pi =
      threeCandidateScoreCarrierEquiv ⁻¹' {score | rankByScore score = pi} :=
  rfl

/-- Fixed three-candidate ranking cells are measurable in the explicit product carrier. -/
theorem measurableSet_threeCandidateRankingEvent (pi : Ranking 1) :
    MeasurableSet (threeCandidateRankingEvent pi) := by
  exact measurableSet_rankByScore_eq threeCandidateScoreVector
    measurable_threeCandidateScoreVector_coordinate pi

/-- The concrete iid score density on the three-score product carrier. -/
def threeCandidateScoreDensity (f : ℝ → ℝ) (value : Candidate 1 → ℝ)
    (theta : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  (f (z.1.1 - theta * value 0) * f (z.1.2 - theta * value 1)) *
    f (z.2 - theta * value 2)

/-- The extended-real density used when the explicit product density is made into a law. -/
noncomputable def threeCandidateScoreDensityENN (f : ℝ → ℝ) (value : Candidate 1 → ℝ)
    (theta : ℝ) : (ℝ × ℝ) × ℝ → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (threeCandidateScoreDensity f value theta z)

/--
The three-score product law.  Its probability normalization is intentionally
not built into this definition; the theorem below takes it as an explicit
premise.
-/
noncomputable def threeCandidateScoreLaw (f : ℝ → ℝ) (value : Candidate 1 → ℝ)
    (theta : ℝ) : Measure ((ℝ × ℝ) × ℝ) :=
  ((volume.prod volume).prod volume).withDensity
    (threeCandidateScoreDensityENN f value theta)

/-- The explicit product law is probabilistic only after its displayed density is normalized. -/
theorem threeCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one
    (f : ℝ → ℝ) (value : Candidate 1 → ℝ) (theta : ℝ)
    (hnormalized :
      ∫⁻ z, threeCandidateScoreDensityENN f value theta z ∂(volume.prod volume).prod volume = 1) :
    IsProbabilityMeasure (threeCandidateScoreLaw f value theta) :=
  isProbabilityMeasure_withDensity_of_lintegral_eq_one
    ((volume.prod volume).prod volume) (threeCandidateScoreDensityENN f value theta) hnormalized

/--
The explicit three-score density has mass one under the usual one-dimensional
density normalization.  This is a product-measure calculation on the carrier
used in this module, not an unproved transport to a finite function space.
-/
theorem threeCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 1 → ℝ) (theta : ℝ) :
    ∫⁻ z, threeCandidateScoreDensityENN f value theta z ∂(volume.prod volume).prod volume = 1 := by
  let f0 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 0))
  let f1 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 1))
  let f2 : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (f (x - theta * value 2))
  have hf0 : AEMeasurable f0 (volume : Measure ℝ) := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have hf1 : AEMeasurable f1 (volume : Measure ℝ) := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have hf2 : AEMeasurable f2 (volume : Measure ℝ) := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have h0 : ∫⁻ x, f0 x ∂volume = 1 := by
    exact lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 0)
  have h1 : ∫⁻ x, f1 x ∂volume = 1 := by
    exact lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 1)
  have h2 : ∫⁻ x, f2 x ∂volume = 1 := by
    exact lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 2)
  have hf01 : AEMeasurable (fun p : ℝ × ℝ => f0 p.1 * f1 p.2)
      (volume.prod volume) := by
    exact hf0.comp_quasiMeasurePreserving
      (MeasureTheory.Measure.quasiMeasurePreserving_fst (μ := volume) (ν := volume)) |>.mul
      (hf1.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_snd (μ := volume) (ν := volume)))
  calc
    ∫⁻ z, threeCandidateScoreDensityENN f value theta z ∂(volume.prod volume).prod volume =
        ∫⁻ z : (ℝ × ℝ) × ℝ, (f0 z.1.1 * f1 z.1.2) * f2 z.2 ∂(volume.prod volume).prod volume := by
      apply lintegral_congr
      intro z
      simp only [threeCandidateScoreDensityENN, threeCandidateScoreDensity, f0, f1, f2]
      rw [ENNReal.ofReal_mul (mul_nonneg (h_nonnegative _) (h_nonnegative _)),
        ENNReal.ofReal_mul (h_nonnegative _)]
    _ = (∫⁻ p : ℝ × ℝ, f0 p.1 * f1 p.2 ∂volume.prod volume) * ∫⁻ x, f2 x ∂volume := by
      rw [lintegral_prod_mul hf01 hf2]
    _ = ((∫⁻ x, f0 x ∂volume) * ∫⁻ y, f1 y ∂volume) * ∫⁻ x, f2 x ∂volume := by
      rw [lintegral_prod_mul hf0 hf1]
    _ = 1 := by simp [h0, h1, h2]

/-- The explicit three-score law is probabilistic under base-density normalization. -/
theorem threeCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 1 → ℝ) (theta : ℝ) :
    IsProbabilityMeasure (threeCandidateScoreLaw f value theta) :=
  threeCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one f value theta
    (threeCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
      f hf h_nonnegative hnormalized value theta)

/-- The three-coordinate iid density curve represented in `L¹`. -/
noncomputable def threeCandidateScoreDensityL1 (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate 1 → ℝ) (theta : ℝ) :
    ((ℝ × ℝ) × ℝ) →₁[(volume.prod volume).prod volume] ℝ :=
  l1ExternalProduct
    (l1ExternalProduct
      (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
      (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
    (scoreTranslateL1 (theta * value 2) (hf.toL1 f))

/-- The concrete product density agrees almost everywhere with its `L¹` representative. -/
theorem threeCandidateScoreDensity_ae_eq_l1
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 1 → ℝ)
    (theta : ℝ) :
    threeCandidateScoreDensity f value theta =ᵐ[(volume.prod volume).prod volume]
      threeCandidateScoreDensityL1 f hf value theta := by
  have h0 :
      (fun z : (ℝ × ℝ) × ℝ =>
        (scoreTranslateL1 (theta * value 0) (hf.toL1 f)) z.1.1) =ᵐ[
          (volume.prod volume).prod volume]
        fun z => f (z.1.1 - theta * value 0) := by
    have htranslate :
        (fun x : ℝ => (scoreTranslateL1 (theta * value 0) (hf.toL1 f)) x) =ᵐ[volume]
          fun x => (hf.toL1 f) (x - theta * value 0) :=
      scoreTranslateL1_ae_eq (theta * value 0) (hf.toL1 f)
    have hbase :
        (fun x : ℝ => (hf.toL1 f) (x - theta * value 0)) =ᵐ[volume]
          fun x => f (x - theta * value 0) := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume (theta * value 0)).quasiMeasurePreserving.ae_eq_comp
          hf.coeFn_toL1
    exact
      ((MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp
          ((MeasureTheory.Measure.quasiMeasurePreserving_fst
            (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp htranslate)).trans
        ((MeasureTheory.Measure.quasiMeasurePreserving_fst
          (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp
            ((MeasureTheory.Measure.quasiMeasurePreserving_fst
              (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp hbase))
  have h1 :
      (fun z : (ℝ × ℝ) × ℝ =>
        (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) z.1.2) =ᵐ[
          (volume.prod volume).prod volume]
        fun z => f (z.1.2 - theta * value 1) := by
    have htranslate :
        (fun x : ℝ => (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) x) =ᵐ[volume]
          fun x => (hf.toL1 f) (x - theta * value 1) :=
      scoreTranslateL1_ae_eq (theta * value 1) (hf.toL1 f)
    have hbase :
        (fun x : ℝ => (hf.toL1 f) (x - theta * value 1)) =ᵐ[volume]
          fun x => f (x - theta * value 1) := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume (theta * value 1)).quasiMeasurePreserving.ae_eq_comp
          hf.coeFn_toL1
    exact
      ((MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp
          ((MeasureTheory.Measure.quasiMeasurePreserving_snd
            (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp htranslate)).trans
        ((MeasureTheory.Measure.quasiMeasurePreserving_fst
          (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp
            ((MeasureTheory.Measure.quasiMeasurePreserving_snd
              (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp hbase))
  have h2 :
      (fun z : (ℝ × ℝ) × ℝ =>
        (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) z.2) =ᵐ[
          (volume.prod volume).prod volume]
        fun z => f (z.2 - theta * value 2) := by
    have htranslate :
        (fun x : ℝ => (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) x) =ᵐ[volume]
          fun x => (hf.toL1 f) (x - theta * value 2) :=
      scoreTranslateL1_ae_eq (theta * value 2) (hf.toL1 f)
    have hbase :
        (fun x : ℝ => (hf.toL1 f) (x - theta * value 2)) =ᵐ[volume]
          fun x => f (x - theta * value 2) := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume (theta * value 2)).quasiMeasurePreserving.ae_eq_comp
          hf.coeFn_toL1
    exact
      ((MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp htranslate).trans
        ((MeasureTheory.Measure.quasiMeasurePreserving_snd
          (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp hbase)
  have hpair :
      (fun z : (ℝ × ℝ) × ℝ =>
        (l1ExternalProduct
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f))) z.1) =ᵐ[
          (volume.prod volume).prod volume]
        fun z =>
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f)) z.1.1 *
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) z.1.2 := by
    exact
      (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume.prod volume : Measure (ℝ × ℝ))) (ν := (volume : Measure ℝ))).ae_eq_comp
        (l1ExternalProduct_ae_eq
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
  filter_upwards [l1ExternalProduct_ae_eq
      (l1ExternalProduct
        (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
        (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
      (scoreTranslateL1 (theta * value 2) (hf.toL1 f)),
    hpair, h0, h1, h2] with
      z houter hpair hz0 hz1 hz2
  simp only [threeCandidateScoreDensity, threeCandidateScoreDensityL1]
  rw [houter, hpair, hz0, hz1, hz2]

/-- The explicit three-score density is integrable under the base `L¹` premise. -/
theorem integrable_threeCandidateScoreDensity
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 1 → ℝ)
    (theta : ℝ) :
    Integrable (threeCandidateScoreDensity f value theta)
      ((volume.prod volume).prod volume) := by
  exact (L1.integrable_coeFn (threeCandidateScoreDensityL1 f hf value theta)).congr
    (threeCandidateScoreDensity_ae_eq_l1 f hf value theta).symm

/-- The corrected three-score ranking atom, as an explicit product-space integral. -/
noncomputable def threeCandidateScoreRankingAtom (f : ℝ → ℝ)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) : ℝ :=
  ∫ z in threeCandidateRankingEvent pi,
    threeCandidateScoreDensity f value theta z ∂(volume.prod volume).prod volume

/-- The actual measure-theoretic mass of a fixed three-candidate ranking cell. -/
noncomputable def threeCandidateScoreLawRankingAtom (f : ℝ → ℝ)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) : ℝ :=
  (threeCandidateScoreLaw f value theta).real (threeCandidateRankingEvent pi)

/-- Pointwise nonnegativity of the score density follows from density nonnegativity. -/
theorem threeCandidateScoreDensity_nonneg
    (f : ℝ → ℝ) (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 1 → ℝ)
    (theta : ℝ) (z : (ℝ × ℝ) × ℝ) :
    0 ≤ threeCandidateScoreDensity f value theta z := by
  exact mul_nonneg (mul_nonneg (h_nonnegative _) (h_nonnegative _)) (h_nonnegative _)

/--
The score-law mass is the displayed real product-space integral.  Probability
normalization remains the separate explicit premise/theorem above.
-/
theorem threeCandidateScoreLawRankingAtom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 1 → ℝ)
    (pi : Ranking 1) (theta : ℝ) :
    threeCandidateScoreLawRankingAtom f value pi theta =
      threeCandidateScoreRankingAtom f value pi theta := by
  let s : Set ((ℝ × ℝ) × ℝ) := threeCandidateRankingEvent pi
  have hdensity_integrable :
      Integrable (threeCandidateScoreDensity f value theta)
        ((volume.prod volume).prod volume) :=
    integrable_threeCandidateScoreDensity f hf value theta
  have hnonnegative_event :
      0 ≤ ∫ z in s, threeCandidateScoreDensity f value theta z ∂(volume.prod volume).prod volume := by
    apply integral_nonneg
    intro z
    exact threeCandidateScoreDensity_nonneg f h_nonnegative value theta z
  have hlintegral :
      ENNReal.ofReal (∫ z in s, threeCandidateScoreDensity f value theta z
        ∂(volume.prod volume).prod volume) =
        ∫⁻ z in s, threeCandidateScoreDensityENN f value theta z
          ∂(volume.prod volume).prod volume := by
    simpa only [threeCandidateScoreDensityENN, IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := ((volume.prod volume).prod volume).restrict s)
        hdensity_integrable.integrableOn
        (Filter.Eventually.of_forall fun z =>
          threeCandidateScoreDensity_nonneg f h_nonnegative value theta z))
  unfold threeCandidateScoreLawRankingAtom threeCandidateScoreLaw threeCandidateScoreRankingAtom
  rw [Measure.real_def, withDensity_apply _ (measurableSet_threeCandidateRankingEvent pi),
    ← hlintegral]
  exact ENNReal.toReal_ofReal hnonnegative_event

/-- The same ranking atom represented by the bounded `L¹` event functional. -/
noncomputable def threeCandidateScoreL1Atom (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) : ℝ :=
  l1ProductSetIntegralCLM (threeCandidateRankingEvent pi)
    (threeCandidateScoreDensityL1 f hf value theta)

/-- The concrete ranking atom is exactly the `L¹` fixed-event integral. -/
theorem threeCandidateScoreL1Atom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 1 → ℝ)
    (pi : Ranking 1) (theta : ℝ) :
    threeCandidateScoreL1Atom f hf value pi theta =
      threeCandidateScoreRankingAtom f value pi theta := by
  rw [threeCandidateScoreL1Atom, threeCandidateScoreRankingAtom,
    l1ProductSetIntegralCLM_apply]
  apply setIntegral_congr_ae
  · exact measurableSet_threeCandidateRankingEvent pi
  · filter_upwards [threeCandidateScoreDensity_ae_eq_l1 f hf value theta] with z hz _
    exact hz.symm

/-- The three-coordinate iid score-density curve has the expected `L¹` derivative. -/
theorem threeCandidateScoreDensityL1_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (theta : ℝ) :
    HasDerivAt (fun t => threeCandidateScoreDensityL1 f hf value t)
      (l1ExternalProduct
          (l1ExternalProduct
            ((-value 0) • scoreTranslateL1 (theta * value 0)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
           l1ExternalProduct
            (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
            ((-value 1) • scoreTranslateL1 (theta * value 1)
              (hderivative.toL1 derivative)))
          (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) +
        l1ExternalProduct
          (l1ExternalProduct
            (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
          ((-value 2) • scoreTranslateL1 (theta * value 2)
            (hderivative.toL1 derivative))) theta := by
  unfold threeCandidateScoreDensityL1
  apply l1ExternalProduct_hasDerivAt
  · apply l1ExternalProduct_hasDerivAt
    · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
        absolute_continuity derivative_ae_eq theta (value 0)
    · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
        absolute_continuity derivative_ae_eq theta (value 1)
  · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
      absolute_continuity derivative_ae_eq theta (value 2)

/-- A fixed three-candidate ranking cell preserves the corrected `W^{1,1}` derivative. -/
theorem threeCandidateScoreL1Atom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) :
    HasDerivAt (threeCandidateScoreL1Atom f hf value pi)
      (l1ProductSetIntegralCLM (threeCandidateRankingEvent pi)
        (l1ExternalProduct
            (l1ExternalProduct
              ((-value 0) • scoreTranslateL1 (theta * value 0)
                (hderivative.toL1 derivative))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
             l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              ((-value 1) • scoreTranslateL1 (theta * value 1)
                (hderivative.toL1 derivative)))
            (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) +
          l1ExternalProduct
            (l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
            ((-value 2) • scoreTranslateL1 (theta * value 2)
              (hderivative.toL1 derivative)))) theta := by
  apply l1ProductSetIntegralCLM_hasDerivAt
  exact threeCandidateScoreDensityL1_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq value theta

/-- The concrete three-score ranking atom is differentiable under global `W^{1,1}`. -/
theorem threeCandidateScoreRankingAtom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) :
    HasDerivAt (threeCandidateScoreRankingAtom f value pi)
      (l1ProductSetIntegralCLM (threeCandidateRankingEvent pi)
        (l1ExternalProduct
            (l1ExternalProduct
              ((-value 0) • scoreTranslateL1 (theta * value 0)
                (hderivative.toL1 derivative))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
             l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              ((-value 1) • scoreTranslateL1 (theta * value 1)
                (hderivative.toL1 derivative)))
            (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) +
          l1ExternalProduct
            (l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
            ((-value 2) • scoreTranslateL1 (theta * value 2)
              (hderivative.toL1 derivative)))) theta := by
  apply (threeCandidateScoreL1Atom_hasDerivAt_of_global_W11
    f derivative hf hderivative absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    (threeCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

/--
The actual three-score law's fixed ranking mass has the same corrected
`W^{1,1}` derivative.  To read it as a probability atom, combine this with
`threeCandidateScoreLaw_isProbabilityMeasure_of_base_normalization` (or the
explicit lintegral normalization criterion).
-/
theorem threeCandidateScoreLawRankingAtom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) :
    HasDerivAt (threeCandidateScoreLawRankingAtom f value pi)
      (l1ProductSetIntegralCLM (threeCandidateRankingEvent pi)
        (l1ExternalProduct
            (l1ExternalProduct
              ((-value 0) • scoreTranslateL1 (theta * value 0)
                (hderivative.toL1 derivative))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
             l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              ((-value 1) • scoreTranslateL1 (theta * value 1)
                (hderivative.toL1 derivative)))
            (scoreTranslateL1 (theta * value 2) (hf.toL1 f)) +
          l1ExternalProduct
            (l1ExternalProduct
              (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
              (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))
            ((-value 2) • scoreTranslateL1 (theta * value 2)
              (hderivative.toL1 derivative)))) theta := by
  apply (threeCandidateScoreL1Atom_hasDerivAt_of_global_W11
    f derivative hf hderivative absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => by
    calc
      threeCandidateScoreLawRankingAtom f value pi t =
          threeCandidateScoreRankingAtom f value pi t :=
        threeCandidateScoreLawRankingAtom_eq_rankingAtom f hf h_nonnegative value pi t
      _ = threeCandidateScoreL1Atom f hf value pi t :=
        (threeCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

/-- The fixed atom of the corrected three-score law is differentiable. -/
theorem threeCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 1 → ℝ) (pi : Ranking 1) (theta : ℝ) :
    DifferentiableAt ℝ (threeCandidateScoreLawRankingAtom f value pi) theta :=
  (threeCandidateScoreLawRankingAtom_hasDerivAt_of_global_W11
    f derivative hf hderivative h_nonnegative absolute_continuity derivative_ae_eq value pi theta).differentiableAt

end KR21Monoculture
