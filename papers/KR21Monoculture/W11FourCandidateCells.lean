import KR21Monoculture.W11ThreeCandidateCells

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Four-candidate ranking cells for the corrected Theorem 5 route

This module treats exactly `Candidate 2 = Fin 4`, which is the source paper's
four-candidate carrier.  The ambient space is the displayed nested product
`((ℝ × ℝ) × ℝ) × ℝ` with its iterated product-volume measure.  The type
equivalence to `Candidate 2 → ℝ` records the coordinate translation only; it
does not assert an unproved transport of the ambient measure.

The result is a concrete four-factor endpoint for the corrected global
`W^{1,1}` route: fixed ranking cells are measurable, the iid score law is
normalized from the one-dimensional density, and every fixed ranking atom is
differentiable.  It deliberately makes no arbitrary-finite-product or
scaled-noise probability-transport claim.
-/

/-- Restrict a four-candidate value vector to its first three displayed coordinates. -/
def fourCandidateFirstThreeValue (value : Candidate 2 → ℝ) : Candidate 1 → ℝ :=
  fun i => value i.castSucc

@[simp] theorem fourCandidateFirstThreeValue_zero (value : Candidate 2 → ℝ) :
    fourCandidateFirstThreeValue value 0 = value 0 := by
  simp [fourCandidateFirstThreeValue]

@[simp] theorem fourCandidateFirstThreeValue_one (value : Candidate 2 → ℝ) :
    fourCandidateFirstThreeValue value 1 = value 1 := by
  simp [fourCandidateFirstThreeValue]

@[simp] theorem fourCandidateFirstThreeValue_two (value : Candidate 2 → ℝ) :
    fourCandidateFirstThreeValue value 2 = value 2 := by
  simp [fourCandidateFirstThreeValue]

/-- The explicit four-score product carrier, reindexed as `Candidate 2 → ℝ`. -/
def fourCandidateScoreVector (z : ((ℝ × ℝ) × ℝ) × ℝ) : Candidate 2 → ℝ :=
  fun i =>
    if i = 0 then z.1.1.1 else if i = 1 then z.1.1.2 else if i = 2 then z.1.2 else z.2

@[simp] theorem fourCandidateScoreVector_zero (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreVector z 0 = z.1.1.1 := by
  simp [fourCandidateScoreVector]

@[simp] theorem fourCandidateScoreVector_one (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreVector z 1 = z.1.1.2 := by
  simp [fourCandidateScoreVector]

@[simp] theorem fourCandidateScoreVector_two (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreVector z 2 = z.1.2 := by
  simp [fourCandidateScoreVector]

@[simp] theorem fourCandidateScoreVector_three (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreVector z 3 = z.2 := by
  simp [fourCandidateScoreVector]

/--
The source-four-candidate reindexing.  This is a type equivalence only: no
product-measure transport is asserted or assumed.
-/
def fourCandidateScoreCarrierEquiv : ((ℝ × ℝ) × ℝ) × ℝ ≃ (Candidate 2 → ℝ) where
  toFun := fourCandidateScoreVector
  invFun := fun score => (((score 0, score 1), score 2), score 3)
  left_inv := by
    intro z
    rcases z with ⟨⟨⟨z0, z1⟩, z2⟩, z3⟩
    simp [fourCandidateScoreVector]
  right_inv := by
    intro score
    funext i
    fin_cases i <;> simp [fourCandidateScoreVector]

/-- The inverse reindexing extracts precisely the four displayed coordinates. -/
theorem fourCandidateScoreCarrierEquiv_symm_apply (score : Candidate 2 → ℝ) :
    fourCandidateScoreCarrierEquiv.symm score = (((score 0, score 1), score 2), score 3) :=
  rfl

@[simp] theorem fourCandidateScoreCarrierEquiv_apply_symm (score : Candidate 2 → ℝ) :
    fourCandidateScoreCarrierEquiv (fourCandidateScoreCarrierEquiv.symm score) = score :=
  fourCandidateScoreCarrierEquiv.apply_symm_apply score

@[simp] theorem fourCandidateScoreCarrierEquiv_symm_apply_apply (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    fourCandidateScoreCarrierEquiv.symm (fourCandidateScoreCarrierEquiv z) = z :=
  fourCandidateScoreCarrierEquiv.symm_apply_apply z

/-- Each coordinate of the explicit four-score carrier is measurable. -/
theorem measurable_fourCandidateScoreVector_coordinate (i : Candidate 2) :
    Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ => fourCandidateScoreVector z i) := by
  fin_cases i
  · simpa [fourCandidateScoreVector] using
      ((measurable_fst.comp (measurable_fst.comp measurable_fst)) :
        Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ => z.1.1.1))
  · simpa [fourCandidateScoreVector] using
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)) :
        Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ => z.1.1.2))
  · simpa [fourCandidateScoreVector] using
      ((measurable_snd.comp measurable_fst) :
        Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ => z.1.2))
  · simpa [fourCandidateScoreVector] using
      (measurable_snd : Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ => z.2))

/-- A fixed four-candidate ranking cell in the explicit product carrier. -/
noncomputable def fourCandidateRankingEvent (pi : Ranking 2) : Set (((ℝ × ℝ) × ℝ) × ℝ) :=
  {z | rankByScore (fourCandidateScoreVector z) = pi}

/-- The ranking cell is exactly the preimage under the displayed reindexing. -/
theorem fourCandidateRankingEvent_eq_preimage (pi : Ranking 2) :
    fourCandidateRankingEvent pi =
      fourCandidateScoreCarrierEquiv ⁻¹' {score | rankByScore score = pi} :=
  rfl

/-- Fixed four-candidate ranking cells are measurable in the explicit carrier. -/
theorem measurableSet_fourCandidateRankingEvent (pi : Ranking 2) :
    MeasurableSet (fourCandidateRankingEvent pi) := by
  exact measurableSet_rankByScore_eq fourCandidateScoreVector
    measurable_fourCandidateScoreVector_coordinate pi

/-- The concrete iid score density on the four-score product carrier. -/
def fourCandidateScoreDensity (f : ℝ → ℝ) (value : Candidate 2 → ℝ)
    (theta : ℝ) (z : ((ℝ × ℝ) × ℝ) × ℝ) : ℝ :=
  threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta z.1 *
    f (z.2 - theta * value 3)

/-- The extended-real density used when the explicit product density is made into a law. -/
noncomputable def fourCandidateScoreDensityENN (f : ℝ → ℝ) (value : Candidate 2 → ℝ)
    (theta : ℝ) : ((ℝ × ℝ) × ℝ) × ℝ → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (fourCandidateScoreDensity f value theta z)

/-- The explicit four-score law before normalization is discharged. -/
noncomputable def fourCandidateScoreLaw (f : ℝ → ℝ) (value : Candidate 2 → ℝ)
    (theta : ℝ) : Measure (((ℝ × ℝ) × ℝ) × ℝ) :=
  (((volume.prod volume).prod volume).prod volume).withDensity
    (fourCandidateScoreDensityENN f value theta)

/-- The explicit product law is probabilistic only after its displayed density is normalized. -/
theorem fourCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one
    (f : ℝ → ℝ) (value : Candidate 2 → ℝ) (theta : ℝ)
    (hnormalized :
      ∫⁻ z, fourCandidateScoreDensityENN f value theta z
        ∂((volume.prod volume).prod volume).prod volume = 1) :
    IsProbabilityMeasure (fourCandidateScoreLaw f value theta) :=
  isProbabilityMeasure_withDensity_of_lintegral_eq_one
    (((volume.prod volume).prod volume).prod volume)
    (fourCandidateScoreDensityENN f value theta) hnormalized

/-- The four-score density is measurable when the base density is measurable. -/
theorem measurable_fourCandidateScoreDensity
    (f : ℝ → ℝ) (hf : Measurable f) (value : Candidate 2 → ℝ) (theta : ℝ) :
    Measurable (fourCandidateScoreDensity f value theta) := by
  have h0 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      f (p.1.1 - theta * value 0)) :=
    hf.comp ((measurable_fst.comp measurable_fst).sub measurable_const)
  have h1 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      f (p.1.2 - theta * value 1)) :=
    hf.comp ((measurable_snd.comp measurable_fst).sub measurable_const)
  have h2 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      f (p.2 - theta * value 2)) :=
    hf.comp (measurable_snd.sub measurable_const)
  have hfirst : Measurable
      (threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta) := by
    simpa [threeCandidateScoreDensity, fourCandidateFirstThreeValue] using (h0.mul h1).mul h2
  have hlast : Measurable (fun z : ((ℝ × ℝ) × ℝ) × ℝ =>
      f (z.2 - theta * value 3)) :=
    hf.comp (measurable_snd.sub measurable_const)
  exact hfirst.comp measurable_fst |>.mul hlast

/-- The extended-real four-score density is measurable under the same premise. -/
theorem measurable_fourCandidateScoreDensityENN
    (f : ℝ → ℝ) (hf : Measurable f) (value : Candidate 2 → ℝ) (theta : ℝ) :
    Measurable (fourCandidateScoreDensityENN f value theta) := by
  simpa [fourCandidateScoreDensityENN] using
    (measurable_fourCandidateScoreDensity f hf value theta).ennreal_ofReal

/-- Pointwise nonnegativity of the four-score density follows from density nonnegativity. -/
theorem fourCandidateScoreDensity_nonneg
    (f : ℝ → ℝ) (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 2 → ℝ)
    (theta : ℝ) (z : ((ℝ × ℝ) × ℝ) × ℝ) :
    0 ≤ fourCandidateScoreDensity f value theta z := by
  exact mul_nonneg
    (threeCandidateScoreDensity_nonneg f h_nonnegative
      (fourCandidateFirstThreeValue value) theta z.1)
    (h_nonnegative _)

/--
The explicit four-score density has mass one under one-dimensional density
normalization.  This is a calculation on the displayed nested product carrier,
not an asserted transport to a finite function space.
-/
theorem fourCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 2 → ℝ) (theta : ℝ) :
    ∫⁻ z, fourCandidateScoreDensityENN f value theta z
      ∂((volume.prod volume).prod volume).prod volume = 1 := by
  have hfirst_measurable : Measurable
      (threeCandidateScoreDensityENN f (fourCandidateFirstThreeValue value) theta) := by
    have h0 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        f (p.1.1 - theta * value 0)) :=
      hf.comp ((measurable_fst.comp measurable_fst).sub measurable_const)
    have h1 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        f (p.1.2 - theta * value 1)) :=
      hf.comp ((measurable_snd.comp measurable_fst).sub measurable_const)
    have h2 : Measurable (fun p : (ℝ × ℝ) × ℝ =>
        f (p.2 - theta * value 2)) :=
      hf.comp (measurable_snd.sub measurable_const)
    simpa [threeCandidateScoreDensityENN, threeCandidateScoreDensity,
      fourCandidateFirstThreeValue] using ((h0.mul h1).mul h2).ennreal_ofReal
  have hfirst : AEMeasurable
      (threeCandidateScoreDensityENN f (fourCandidateFirstThreeValue value) theta)
      ((volume.prod volume).prod volume) := hfirst_measurable.aemeasurable
  have hlast : AEMeasurable (fun x : ℝ =>
      ENNReal.ofReal (f (x - theta * value 3))) volume := by
    exact ((hf.comp (measurable_id.sub measurable_const)).ennreal_ofReal).aemeasurable
  have hfirst_mass :
      ∫⁻ p, threeCandidateScoreDensityENN f (fourCandidateFirstThreeValue value) theta p
        ∂(volume.prod volume).prod volume = 1 :=
    threeCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
      f hf h_nonnegative hnormalized (fourCandidateFirstThreeValue value) theta
  have hlast_mass :
      ∫⁻ x, ENNReal.ofReal (f (x - theta * value 3)) ∂volume = 1 :=
    lintegral_ofReal_sub_right_eq_one f hf hnormalized (theta * value 3)
  calc
    ∫⁻ z, fourCandidateScoreDensityENN f value theta z
        ∂((volume.prod volume).prod volume).prod volume =
        ∫⁻ z : ((ℝ × ℝ) × ℝ) × ℝ,
          threeCandidateScoreDensityENN f (fourCandidateFirstThreeValue value) theta z.1 *
            ENNReal.ofReal (f (z.2 - theta * value 3))
          ∂((volume.prod volume).prod volume).prod volume := by
      apply lintegral_congr
      intro z
      change ENNReal.ofReal
          (threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta z.1 *
            f (z.2 - theta * value 3)) =
        ENNReal.ofReal
          (threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta z.1) *
          ENNReal.ofReal (f (z.2 - theta * value 3))
      rw [ENNReal.ofReal_mul
        (threeCandidateScoreDensity_nonneg f h_nonnegative
          (fourCandidateFirstThreeValue value) theta z.1)]
    _ =
        (∫⁻ p, threeCandidateScoreDensityENN f (fourCandidateFirstThreeValue value) theta p
          ∂(volume.prod volume).prod volume) *
          ∫⁻ x, ENNReal.ofReal (f (x - theta * value 3)) ∂volume := by
      rw [lintegral_prod_mul hfirst hlast]
    _ = 1 := by simp [hfirst_mass, hlast_mass]

/-- The explicit four-score law is probabilistic under base-density normalization. -/
theorem fourCandidateScoreLaw_isProbabilityMeasure_of_base_normalization
    (f : ℝ → ℝ) (hf : Measurable f) (h_nonnegative : ∀ x, 0 ≤ f x)
    (hnormalized : ∫⁻ x, ENNReal.ofReal (f x) ∂volume = 1)
    (value : Candidate 2 → ℝ) (theta : ℝ) :
    IsProbabilityMeasure (fourCandidateScoreLaw f value theta) :=
  fourCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one f value theta
    (fourCandidateScoreDensityENN_lintegral_eq_one_of_base_normalization
      f hf h_nonnegative hnormalized value theta)

/-- The four-coordinate iid density curve represented in `L¹`. -/
noncomputable def fourCandidateScoreDensityL1 (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate 2 → ℝ) (theta : ℝ) :
    (((ℝ × ℝ) × ℝ) × ℝ) →₁[((volume.prod volume).prod volume).prod volume] ℝ :=
  l1ExternalProduct
    (threeCandidateScoreDensityL1 f hf (fourCandidateFirstThreeValue value) theta)
    (scoreTranslateL1 (theta * value 3) (hf.toL1 f))

/-- The concrete four-score density agrees almost everywhere with its `L¹` representative. -/
theorem fourCandidateScoreDensity_ae_eq_l1
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 2 → ℝ)
    (theta : ℝ) :
    fourCandidateScoreDensity f value theta =ᵐ[((volume.prod volume).prod volume).prod volume]
      fourCandidateScoreDensityL1 f hf value theta := by
  have hfirst :
      (fun z : ((ℝ × ℝ) × ℝ) × ℝ =>
        (threeCandidateScoreDensityL1 f hf (fourCandidateFirstThreeValue value) theta) z.1) =ᵐ[
          ((volume.prod volume).prod volume).prod volume]
        fun z => threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta z.1 := by
    exact
      (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := ((volume.prod volume).prod volume : Measure ((ℝ × ℝ) × ℝ)))
        (ν := (volume : Measure ℝ))).ae_eq_comp
        (threeCandidateScoreDensity_ae_eq_l1
          f hf (fourCandidateFirstThreeValue value) theta).symm
  have hlast :
      (fun z : ((ℝ × ℝ) × ℝ) × ℝ =>
        (scoreTranslateL1 (theta * value 3) (hf.toL1 f)) z.2) =ᵐ[
          ((volume.prod volume).prod volume).prod volume]
        fun z => f (z.2 - theta * value 3) := by
    have htranslate :
        (fun x : ℝ => (scoreTranslateL1 (theta * value 3) (hf.toL1 f)) x) =ᵐ[volume]
          fun x => (hf.toL1 f) (x - theta * value 3) :=
      scoreTranslateL1_ae_eq (theta * value 3) (hf.toL1 f)
    have hbase :
        (fun x : ℝ => (hf.toL1 f) (x - theta * value 3)) =ᵐ[volume]
          fun x => f (x - theta * value 3) := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume (theta * value 3)).quasiMeasurePreserving.ae_eq_comp
          hf.coeFn_toL1
    exact
      (MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := ((volume.prod volume).prod volume : Measure ((ℝ × ℝ) × ℝ)))
        (ν := (volume : Measure ℝ))).ae_eq_comp (htranslate.trans hbase)
  filter_upwards [l1ExternalProduct_ae_eq
      (threeCandidateScoreDensityL1 f hf (fourCandidateFirstThreeValue value) theta)
      (scoreTranslateL1 (theta * value 3) (hf.toL1 f)), hfirst, hlast] with
      z hproduct hfirst hlast
  calc
    fourCandidateScoreDensity f value theta z =
        threeCandidateScoreDensity f (fourCandidateFirstThreeValue value) theta z.1 *
          f (z.2 - theta * value 3) := rfl
    _ = (threeCandidateScoreDensityL1 f hf (fourCandidateFirstThreeValue value) theta) z.1 *
          (scoreTranslateL1 (theta * value 3) (hf.toL1 f)) z.2 := by
      rw [hfirst.symm, hlast.symm]
    _ = fourCandidateScoreDensityL1 f hf value theta z := by
      simpa [fourCandidateScoreDensityL1] using hproduct.symm

/-- The explicit four-score density is integrable under the base `L¹` premise. -/
theorem integrable_fourCandidateScoreDensity
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 2 → ℝ)
    (theta : ℝ) :
    Integrable (fourCandidateScoreDensity f value theta)
      (((volume.prod volume).prod volume).prod volume) := by
  exact (L1.integrable_coeFn (fourCandidateScoreDensityL1 f hf value theta)).congr
    (fourCandidateScoreDensity_ae_eq_l1 f hf value theta).symm

/-- The corrected four-score ranking atom, as an explicit product-space integral. -/
noncomputable def fourCandidateScoreRankingAtom (f : ℝ → ℝ)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) : ℝ :=
  ∫ z in fourCandidateRankingEvent pi, fourCandidateScoreDensity f value theta z
    ∂((volume.prod volume).prod volume).prod volume

/-- The actual measure-theoretic mass of a fixed four-candidate ranking cell. -/
noncomputable def fourCandidateScoreLawRankingAtom (f : ℝ → ℝ)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) : ℝ :=
  (fourCandidateScoreLaw f value theta).real (fourCandidateRankingEvent pi)

/-- The score-law mass is the displayed real product-space integral. -/
theorem fourCandidateScoreLawRankingAtom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 2 → ℝ)
    (pi : Ranking 2) (theta : ℝ) :
    fourCandidateScoreLawRankingAtom f value pi theta =
      fourCandidateScoreRankingAtom f value pi theta := by
  let s : Set (((ℝ × ℝ) × ℝ) × ℝ) := fourCandidateRankingEvent pi
  have hdensity_integrable :
      Integrable (fourCandidateScoreDensity f value theta)
        (((volume.prod volume).prod volume).prod volume) :=
    integrable_fourCandidateScoreDensity f hf value theta
  have hnonnegative_event :
      0 ≤ ∫ z in s, fourCandidateScoreDensity f value theta z
        ∂((volume.prod volume).prod volume).prod volume := by
    apply integral_nonneg
    intro z
    exact fourCandidateScoreDensity_nonneg f h_nonnegative value theta z
  have hlintegral :
      ENNReal.ofReal (∫ z in s, fourCandidateScoreDensity f value theta z
        ∂((volume.prod volume).prod volume).prod volume) =
        ∫⁻ z in s, fourCandidateScoreDensityENN f value theta z
          ∂((volume.prod volume).prod volume).prod volume := by
    simpa only [fourCandidateScoreDensityENN, IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := (((volume.prod volume).prod volume).prod volume).restrict s)
        hdensity_integrable.integrableOn
        (Filter.Eventually.of_forall fun z =>
          fourCandidateScoreDensity_nonneg f h_nonnegative value theta z))
  unfold fourCandidateScoreLawRankingAtom fourCandidateScoreLaw fourCandidateScoreRankingAtom
  rw [Measure.real_def, withDensity_apply _ (measurableSet_fourCandidateRankingEvent pi),
    ← hlintegral]
  exact ENNReal.toReal_ofReal hnonnegative_event

/-- The same ranking atom represented by the bounded `L¹` event functional. -/
noncomputable def fourCandidateScoreL1Atom (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) : ℝ :=
  l1ProductSetIntegralCLM (fourCandidateRankingEvent pi)
    (fourCandidateScoreDensityL1 f hf value theta)

/-- The concrete ranking atom is exactly the `L¹` fixed-event integral. -/
theorem fourCandidateScoreL1Atom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 2 → ℝ)
    (pi : Ranking 2) (theta : ℝ) :
    fourCandidateScoreL1Atom f hf value pi theta =
      fourCandidateScoreRankingAtom f value pi theta := by
  rw [fourCandidateScoreL1Atom, fourCandidateScoreRankingAtom,
    l1ProductSetIntegralCLM_apply]
  apply setIntegral_congr_ae
  · exact measurableSet_fourCandidateRankingEvent pi
  · filter_upwards [fourCandidateScoreDensity_ae_eq_l1 f hf value theta] with z hz _
    exact hz.symm

/-- The four-coordinate iid `L¹` density curve is differentiable under global `W^{1,1}`. -/
theorem fourCandidateScoreDensityL1_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (theta : ℝ) :
    DifferentiableAt ℝ (fun t => fourCandidateScoreDensityL1 f hf value t) theta := by
  unfold fourCandidateScoreDensityL1
  exact (l1ExternalProduct_hasDerivAt
    (threeCandidateScoreDensityL1_hasDerivAt_of_global_W11
      f derivative hf hderivative absolute_continuity derivative_ae_eq
      (fourCandidateFirstThreeValue value) theta)
    (scoreTranslateL1_hasDerivAt_of_global_W11
      f derivative hf hderivative absolute_continuity derivative_ae_eq theta (value 3))).differentiableAt

/-- A fixed four-candidate ranking cell preserves the corrected `W^{1,1}` differentiability. -/
theorem fourCandidateScoreL1Atom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) :
    DifferentiableAt ℝ (fourCandidateScoreL1Atom f hf value pi) theta := by
  unfold fourCandidateScoreL1Atom fourCandidateScoreDensityL1
  exact (l1ProductSetIntegralCLM_hasDerivAt (fourCandidateRankingEvent pi)
    (l1ExternalProduct_hasDerivAt
      (threeCandidateScoreDensityL1_hasDerivAt_of_global_W11
        f derivative hf hderivative absolute_continuity derivative_ae_eq
        (fourCandidateFirstThreeValue value) theta)
      (scoreTranslateL1_hasDerivAt_of_global_W11
        f derivative hf hderivative absolute_continuity derivative_ae_eq theta (value 3)))).differentiableAt

/-- The concrete four-score ranking atom is differentiable under global `W^{1,1}`. -/
theorem fourCandidateScoreRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) :
    DifferentiableAt ℝ (fourCandidateScoreRankingAtom f value pi) theta := by
  apply (fourCandidateScoreL1Atom_differentiableAt_of_global_W11
    f derivative hf hderivative absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    (fourCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

/-- The actual four-score law's fixed ranking mass is differentiable under global `W^{1,1}`. -/
theorem fourCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 2 → ℝ) (pi : Ranking 2) (theta : ℝ) :
    DifferentiableAt ℝ (fourCandidateScoreLawRankingAtom f value pi) theta := by
  apply (fourCandidateScoreL1Atom_differentiableAt_of_global_W11
    f derivative hf hderivative absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => by
    calc
      fourCandidateScoreLawRankingAtom f value pi t =
          fourCandidateScoreRankingAtom f value pi t :=
        fourCandidateScoreLawRankingAtom_eq_rankingAtom f hf h_nonnegative value pi t
      _ = fourCandidateScoreL1Atom f hf value pi t :=
        (fourCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

end KR21Monoculture
