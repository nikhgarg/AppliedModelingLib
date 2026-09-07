import KR21Monoculture.W11FiniteProduct

open AppliedModelingLib MeasureTheory Filter
open AppliedModelingLib.SocialChoice.Ranking
open scoped Topology ENNReal

namespace KR21Monoculture

/-!
# Two-candidate ranking cells for the corrected Theorem 5 route

This module begins the missing link between the `L¹` product calculation and
the paper's ranking atoms.  It deliberately treats only `Candidate 0 = Fin 2`.
The score coordinates are represented by `ℝ × ℝ`; no unproved identification
with an arbitrary finite function space is used here.

For the corrected score-space model, a noise vector `ε` at accuracy `θ` gives
scores `θ * value i + ε i`.  Thus a fixed ranking cell lives in score space,
while its two coordinate densities are the translations
`r ↦ f (r - θ * value i)`.
-/

/-- The two score coordinates, viewed as a `Candidate 0 → ℝ` vector. -/
def twoCandidateScoreVector (z : ℝ × ℝ) : Candidate 0 → ℝ :=
  fun i => if i = 0 then z.1 else z.2

@[simp] theorem twoCandidateScoreVector_zero (z : ℝ × ℝ) :
    twoCandidateScoreVector z 0 = z.1 := by
  simp [twoCandidateScoreVector]

@[simp] theorem twoCandidateScoreVector_one (z : ℝ × ℝ) :
    twoCandidateScoreVector z 1 = z.2 := by
  simp [twoCandidateScoreVector]

/-- Each coordinate of the concrete two-score vector is measurable. -/
theorem measurable_twoCandidateScoreVector_coordinate (i : Candidate 0) :
    Measurable (fun z : ℝ × ℝ => twoCandidateScoreVector z i) := by
  by_cases hi : i = 0
  · subst i
    simpa [twoCandidateScoreVector] using (measurable_fst : Measurable (Prod.fst : ℝ × ℝ → ℝ))
  · have hi_one : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst i
    simpa [twoCandidateScoreVector] using (measurable_snd : Measurable (Prod.snd : ℝ × ℝ → ℝ))

/-- The fixed score-space event selecting a particular two-candidate ranking. -/
noncomputable def twoCandidateRankingEvent (pi : Ranking 0) : Set (ℝ × ℝ) :=
  {z | rankByScore (twoCandidateScoreVector z) = pi}

/-- Fixed two-candidate score-ranking cells are measurable. -/
theorem measurableSet_twoCandidateRankingEvent (pi : Ranking 0) :
    MeasurableSet (twoCandidateRankingEvent pi) := by
  exact measurableSet_rankByScore_eq twoCandidateScoreVector
    measurable_twoCandidateScoreVector_coordinate pi

/-- The real density of the corrected two-score model on `ℝ × ℝ`. -/
def twoCandidateScoreDensity (f : ℝ → ℝ) (value : Candidate 0 → ℝ)
    (theta : ℝ) (z : ℝ × ℝ) : ℝ :=
  f (z.1 - theta * value 0) * f (z.2 - theta * value 1)

/-- The nonnegative extended-real density used for the corresponding score law. -/
noncomputable def twoCandidateScoreDensityENN (f : ℝ → ℝ) (value : Candidate 0 → ℝ)
    (theta : ℝ) : ℝ × ℝ → ℝ≥0∞ :=
  fun z => ENNReal.ofReal (twoCandidateScoreDensity f value theta z)

/-- The corrected two-score measure before its normalization is discharged. -/
noncomputable def twoCandidateScoreLaw (f : ℝ → ℝ) (value : Candidate 0 → ℝ)
    (theta : ℝ) : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity (twoCandidateScoreDensityENN f value theta)

/-- The actual measure-theoretic mass of a fixed two-candidate ranking event. -/
noncomputable def twoCandidateScoreLawRankingAtom (f : ℝ → ℝ)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) : ℝ :=
  (twoCandidateScoreLaw f value theta).real (twoCandidateRankingEvent pi)

/-- The score law is a probability measure once its displayed density is normalized. -/
theorem twoCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one
    (f : ℝ → ℝ) (value : Candidate 0 → ℝ) (theta : ℝ)
    (hnormalized :
      ∫⁻ z, twoCandidateScoreDensityENN f value theta z ∂volume.prod volume = 1) :
    IsProbabilityMeasure (twoCandidateScoreLaw f value theta) :=
  isProbabilityMeasure_withDensity_of_lintegral_eq_one
    (volume.prod volume) (twoCandidateScoreDensityENN f value theta) hnormalized

/-- Pointwise nonnegativity of the corrected score density follows from density nonnegativity. -/
theorem twoCandidateScoreDensity_nonneg
    (f : ℝ → ℝ) (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 0 → ℝ)
    (theta : ℝ) (z : ℝ × ℝ) :
    0 ≤ twoCandidateScoreDensity f value theta z := by
  exact mul_nonneg (h_nonnegative _) (h_nonnegative _)

/-- The corrected two-candidate ranking atom, written as a score-space integral. -/
noncomputable def twoCandidateScoreRankingAtom (f : ℝ → ℝ)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) : ℝ :=
  ∫ z in twoCandidateRankingEvent pi, twoCandidateScoreDensity f value theta z ∂volume.prod volume

/-- The same atom represented by the bounded `L¹` set-integral functional. -/
noncomputable def twoCandidateScoreL1Atom (f : ℝ → ℝ) (hf : Integrable f volume)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) : ℝ :=
  l1ProductSetIntegralCLM (twoCandidateRankingEvent pi)
    (l1ExternalProduct
      (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
      (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))

/-- The concrete score density agrees almost everywhere with its `L¹` product representative. -/
theorem twoCandidateScoreDensity_ae_eq_l1ExternalProduct
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 0 → ℝ)
    (theta : ℝ) :
    (fun z : ℝ × ℝ => twoCandidateScoreDensity f value theta z) =ᵐ[volume.prod volume]
      fun z =>
        l1ExternalProduct
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) z := by
  have hfst :
      (fun z : ℝ × ℝ =>
        (scoreTranslateL1 (theta * value 0) (hf.toL1 f)) z.1) =ᵐ[volume.prod volume]
        fun z => f (z.1 - theta * value 0) := by
    have htranslate :
        (fun x : ℝ =>
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f)) x) =ᵐ[volume]
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
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp htranslate).trans
        ((MeasureTheory.Measure.quasiMeasurePreserving_fst
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp hbase)
  have hsnd :
      (fun z : ℝ × ℝ =>
        (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) z.2) =ᵐ[volume.prod volume]
        fun z => f (z.2 - theta * value 1) := by
    have htranslate :
        (fun x : ℝ =>
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) x) =ᵐ[volume]
          fun x => (hf.toL1 f) (x - theta * value 1) :=
      scoreTranslateL1_ae_eq (theta * value 1) (hf.toL1 f)
    have hbase :
        (fun x : ℝ => (hf.toL1 f) (x - theta * value 1)) =ᵐ[volume]
          fun x => f (x - theta * value 1) := by
      simpa only [Function.comp_apply] using
        (measurePreserving_sub_right volume (theta * value 1)).quasiMeasurePreserving.ae_eq_comp
          hf.coeFn_toL1
    exact
      ((MeasureTheory.Measure.quasiMeasurePreserving_snd
        (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp htranslate).trans
        ((MeasureTheory.Measure.quasiMeasurePreserving_snd
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae_eq_comp hbase)
  filter_upwards [l1ExternalProduct_ae_eq
      (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
      (scoreTranslateL1 (theta * value 1) (hf.toL1 f)), hfst, hsnd] with z hprod hfst hsnd
  rw [hprod, hfst, hsnd]
  rfl

/-- The concrete two-score density is integrable when the base density is integrable. -/
theorem integrable_twoCandidateScoreDensity
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 0 → ℝ)
    (theta : ℝ) :
    Integrable (twoCandidateScoreDensity f value theta) (volume.prod volume) := by
  exact
    (L1.integrable_coeFn
      (l1ExternalProduct
        (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
        (scoreTranslateL1 (theta * value 1) (hf.toL1 f)))).congr
      (twoCandidateScoreDensity_ae_eq_l1ExternalProduct f hf value theta).symm

/--
The measure-theoretic ranking-event mass equals the real score-density
integral.  Normalization is intentionally not hidden here: the preceding
theorem supplies the separate criterion making this mass a probability.
-/
theorem twoCandidateScoreLawRankingAtom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume)
    (h_nonnegative : ∀ x, 0 ≤ f x) (value : Candidate 0 → ℝ)
    (pi : Ranking 0) (theta : ℝ) :
    twoCandidateScoreLawRankingAtom f value pi theta =
      twoCandidateScoreRankingAtom f value pi theta := by
  let s : Set (ℝ × ℝ) := twoCandidateRankingEvent pi
  have hdensity_integrable :
      Integrable (twoCandidateScoreDensity f value theta) (volume.prod volume) :=
    integrable_twoCandidateScoreDensity f hf value theta
  have hnonnegative_event :
      0 ≤ ∫ z in s, twoCandidateScoreDensity f value theta z ∂volume.prod volume := by
    apply integral_nonneg
    intro z
    exact twoCandidateScoreDensity_nonneg f h_nonnegative value theta z
  have hlintegral :
      ENNReal.ofReal (∫ z in s, twoCandidateScoreDensity f value theta z ∂volume.prod volume) =
        ∫⁻ z in s, twoCandidateScoreDensityENN f value theta z ∂volume.prod volume := by
    simpa only [twoCandidateScoreDensityENN, IntegrableOn] using
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (μ := (volume.prod volume).restrict s)
        hdensity_integrable.integrableOn
        (Filter.Eventually.of_forall fun z =>
          twoCandidateScoreDensity_nonneg f h_nonnegative value theta z))
  unfold twoCandidateScoreLawRankingAtom twoCandidateScoreLaw twoCandidateScoreRankingAtom
  rw [Measure.real_def, withDensity_apply _ (measurableSet_twoCandidateRankingEvent pi),
    ← hlintegral]
  exact ENNReal.toReal_ofReal hnonnegative_event

/-- The score-space atom is exactly the `L¹` set integral used by the product theorem. -/
theorem twoCandidateScoreL1Atom_eq_rankingAtom
    (f : ℝ → ℝ) (hf : Integrable f volume) (value : Candidate 0 → ℝ)
    (pi : Ranking 0) (theta : ℝ) :
    twoCandidateScoreL1Atom f hf value pi theta =
      twoCandidateScoreRankingAtom f value pi theta := by
  rw [twoCandidateScoreL1Atom, twoCandidateScoreRankingAtom,
    l1ProductSetIntegralCLM_apply]
  apply setIntegral_congr_ae
  · exact measurableSet_twoCandidateRankingEvent pi
  · filter_upwards [twoCandidateScoreDensity_ae_eq_l1ExternalProduct f hf value theta]
      with z hz _
    exact hz.symm

/-- The two-coordinate corrected score density has the product-rule `L¹` derivative. -/
theorem twoCandidateScoreDensityL1_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (theta : ℝ) :
    HasDerivAt
      (fun t => l1ExternalProduct
        (scoreTranslateL1 (t * value 0) (hf.toL1 f))
        (scoreTranslateL1 (t * value 1) (hf.toL1 f)))
      (l1ExternalProduct
          ((-value 0) • scoreTranslateL1 (theta * value 0)
            (hderivative.toL1 derivative))
          (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
        l1ExternalProduct
          (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
          ((-value 1) • scoreTranslateL1 (theta * value 1)
            (hderivative.toL1 derivative))) theta := by
  apply l1ExternalProduct_hasDerivAt
  · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
      absolute_continuity derivative_ae_eq theta (value 0)
  · exact scoreTranslateL1_hasDerivAt_of_global_W11 f derivative hf hderivative
      absolute_continuity derivative_ae_eq theta (value 1)

/-- The fixed two-candidate ranking cell preserves the corrected `W^{1,1}` derivative. -/
theorem twoCandidateScoreL1Atom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) :
    HasDerivAt (twoCandidateScoreL1Atom f hf value pi)
      (l1ProductSetIntegralCLM (twoCandidateRankingEvent pi)
        (l1ExternalProduct
            ((-value 0) • scoreTranslateL1 (theta * value 0)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
          l1ExternalProduct
            (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
            ((-value 1) • scoreTranslateL1 (theta * value 1)
              (hderivative.toL1 derivative)))) theta := by
  apply l1ProductSetIntegralCLM_hasDerivAt
  exact twoCandidateScoreDensityL1_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq value theta

/-- The concrete corrected two-candidate ranking atom is differentiable under global `W^{1,1}`. -/
theorem twoCandidateScoreRankingAtom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) :
    HasDerivAt (twoCandidateScoreRankingAtom f value pi)
      (l1ProductSetIntegralCLM (twoCandidateRankingEvent pi)
        (l1ExternalProduct
            ((-value 0) • scoreTranslateL1 (theta * value 0)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
          l1ExternalProduct
            (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
            ((-value 1) • scoreTranslateL1 (theta * value 1)
              (hderivative.toL1 derivative)))) theta := by
  apply (twoCandidateScoreL1Atom_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t =>
    (twoCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

/--
The actual corrected score-law atom has the same derivative.  Together with
`twoCandidateScoreLaw_isProbabilityMeasure_of_lintegral_eq_one`, this is a
two-candidate probability-atom result with the normalization premise exposed.
-/
theorem twoCandidateScoreLawRankingAtom_hasDerivAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) :
    HasDerivAt (twoCandidateScoreLawRankingAtom f value pi)
      (l1ProductSetIntegralCLM (twoCandidateRankingEvent pi)
        (l1ExternalProduct
            ((-value 0) • scoreTranslateL1 (theta * value 0)
              (hderivative.toL1 derivative))
            (scoreTranslateL1 (theta * value 1) (hf.toL1 f)) +
          l1ExternalProduct
            (scoreTranslateL1 (theta * value 0) (hf.toL1 f))
            ((-value 1) • scoreTranslateL1 (theta * value 1)
              (hderivative.toL1 derivative)))) theta := by
  apply (twoCandidateScoreL1Atom_hasDerivAt_of_global_W11 f derivative hf hderivative
    absolute_continuity derivative_ae_eq value pi theta).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun t => by
    calc
      twoCandidateScoreLawRankingAtom f value pi t =
          twoCandidateScoreRankingAtom f value pi t :=
        twoCandidateScoreLawRankingAtom_eq_rankingAtom f hf h_nonnegative value pi t
      _ = twoCandidateScoreL1Atom f hf value pi t :=
        (twoCandidateScoreL1Atom_eq_rankingAtom f hf value pi t).symm

/-- The corresponding two-candidate corrected score-law atom is differentiable. -/
theorem twoCandidateScoreLawRankingAtom_differentiableAt_of_global_W11
    (f derivative : ℝ → ℝ)
    (hf : Integrable f volume) (hderivative : Integrable derivative volume)
    (h_nonnegative : ∀ x, 0 ≤ f x)
    (absolute_continuity : ∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b)
    (derivative_ae_eq : derivative =ᵐ[volume] deriv f)
    (value : Candidate 0 → ℝ) (pi : Ranking 0) (theta : ℝ) :
    DifferentiableAt ℝ (twoCandidateScoreLawRankingAtom f value pi) theta :=
  (twoCandidateScoreLawRankingAtom_hasDerivAt_of_global_W11 f derivative hf hderivative
    h_nonnegative absolute_continuity derivative_ae_eq value pi theta).differentiableAt

end KR21Monoculture
