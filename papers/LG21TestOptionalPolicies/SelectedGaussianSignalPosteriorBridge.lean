import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD
import AppliedModelingLib.Foundations.Probability.GaussianTilt
import AppliedModelingLib.Foundations.Probability.GaussianTranslationAC
import LG21TestOptionalPolicies.SelectedConditionalRCD
import LG21TestOptionalPolicies.SelectedGaussianExAntePayoff
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Selected Gaussian signal posterior bridge

This module starts from the literal unselected Gaussian signal joint law and
then restricts it to an arbitrary measurable latent selection.  The first
step is entirely measure-theoretic: every positive selected prior event has
positive mass in every unselected Gaussian posterior fibre, so the existing
selected-fibre RCD can be used without inventing null-fibre values.

The remaining displayed posterior-mean identity is deliberately separated
from that support/factorization work.  It must identify the selected
restriction of the explicit unselected Gaussian posterior with the canonical
quadratic-likelihood exponential tilt, rather than assuming a PBO formula.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
open AppliedModelingLib Probability

/-- The residual variance in a nondegenerate one-score Gaussian update is
positive. -/
theorem lg21_gaussianSignalPosteriorVariance_pos
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    0 < (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ) := by
  rw [NNReal.coe_pos, Real.toNNReal_pos]
  exact div_pos (mul_pos hpriorVariance hnoiseVariance)
    (add_pos hpriorVariance hnoiseVariance)

/-- The explicit one-score Gaussian posterior is a Markov kernel. -/
theorem lg21_gaussianSignalPosteriorKernel_isMarkov
    (priorMean priorVariance noiseVariance : ℝ) :
    IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) := by
  unfold gaussianSignalPosteriorKernel
  letI : IsMarkovKernel (Kernel.id : Kernel ℝ ℝ) := by infer_instance
  letI : IsMarkovKernel (Kernel.const ℝ
      (gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance))) := by
    infer_instance
  letI : IsMarkovKernel
      ((Kernel.id : Kernel ℝ ℝ) ×ₖ Kernel.const ℝ
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance))) := by
    infer_instance
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/--
A latent selection with positive prior Gaussian mass has positive mass under
every unselected posterior fibre of a nondegenerate Gaussian signal.  This
uses equality of Gaussian null sets, not a pointwise density convention.
-/
theorem lg21_gaussianSignalPosterior_selected_pos
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (score : ℝ) :
    0 < gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
      score selected := by
  rw [gaussianSignalPosteriorKernel_apply]
  have hpriorNN : 0 < priorVariance.toNNReal :=
    Real.toNNReal_pos.mpr hpriorVariance
  have hposteriorNN :
      0 < gaussianSignalPosteriorVariance priorVariance noiseVariance := by
    exact_mod_cast lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hdom : Measure.AbsolutelyContinuous
      (gaussianReal priorMean priorVariance.toNNReal)
      (gaussianReal
        (gaussianSignalWeight priorVariance noiseVariance * score +
          gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance)) := by
    exact AppliedModelingLib.Probability.gaussianReal_absolutelyContinuous_of_positive_variances
      priorMean
      (gaussianSignalWeight priorVariance noiseVariance * score +
        gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
      hpriorNN hposteriorNN
  refine pos_iff_ne_zero.mpr ?_
  intro hzero
  exact (ne_of_gt hselected) (hdom hzero)

/-- The selected-fibre kernel for a positive Gaussian latent selection is
defined on every score, because every posterior Gaussian fibre gives the
selection positive mass. -/
theorem lg21_gaussianSignalPosterior_selectionMass_ne_zero
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    ∀ score,
      selectionMass
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score ≠ 0 := by
  intro score
  simpa [selectionMass, selectedFiber] using
    (ne_of_gt (lg21_gaussianSignalPosterior_selected_pos
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselected score))

/-- The literal score/latent Gaussian joint law assigns positive mass to the
event that the latent skill belongs to a positive selected prior set. -/
theorem lg21_gaussianSignal_selected_event_ne_zero
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal ⊗ₘ
      gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) ≠ 0 := by
  let rawScoreLatentLaw : Measure (ℝ × ℝ) :=
    (gaussianSignalPair priorMean priorVariance noiseVariance).map
      (fun pair : ℝ × ℝ => (gaussianSignalScore pair, pair.1))
  let scoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let rawPosterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let joint : Measure (ℝ × ℝ) := scoreLaw ⊗ₘ rawPosterior
  letI : IsMarkovKernel rawPosterior := by
    exact lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  change joint (Set.univ ×ˢ selected) ≠ 0
  have hfactor : rawScoreLatentLaw = joint := by
    dsimp [rawScoreLatentLaw, joint, scoreLaw, rawPosterior]
    exact gaussianSignalPair_score_latent_joint_factorization
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hrawSnd : rawScoreLatentLaw.map Prod.snd =
      gaussianReal priorMean priorVariance.toNNReal := by
    calc
      rawScoreLatentLaw.map Prod.snd =
          (gaussianSignalPair priorMean priorVariance noiseVariance).map
            (Prod.snd ∘ fun pair : ℝ × ℝ =>
              (gaussianSignalScore pair, pair.1)) := by
            simp only [rawScoreLatentLaw]
            rw [Measure.map_map measurable_snd (by fun_prop)]
      _ = (gaussianSignalPair priorMean priorVariance noiseVariance).map Prod.fst := by
            rfl
      _ = gaussianReal priorMean priorVariance.toNNReal := by
            rw [Measure.map_fst_prod]
            simp
  have hjointSnd : joint.map Prod.snd =
      gaussianReal priorMean priorVariance.toNNReal := by
    rw [← hfactor]
    exact hrawSnd
  have hpreimage : (Prod.snd : ℝ × ℝ → ℝ) ⁻¹' selected =
      (Set.univ : Set ℝ) ×ˢ selected := by
    ext pair
    simp
  have hmass : joint (Set.univ ×ˢ selected) =
      gaussianReal priorMean priorVariance.toNNReal selected := by
    calc
      joint (Set.univ ×ˢ selected) = joint (Prod.snd ⁻¹' selected) := by
        rw [hpreimage]
      _ = (joint.map Prod.snd) selected := by
        rw [Measure.map_apply measurable_snd hselectedMeasurable]
      _ = gaussianReal priorMean priorVariance.toNNReal selected := by
        rw [hjointSnd]
  rw [hmass]
  exact ne_of_gt hselected

/-- The literal unselected Gaussian score/latent source law factors through
the displayed score marginal and Gaussian posterior kernel. -/
theorem lg21_selectedGaussianSignal_raw_scoreLatent_factorization
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (_hselectedMeasurable : MeasurableSet selected)
    (_hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    (gaussianSignalPair priorMean priorVariance noiseVariance).map
      (fun pair : ℝ × ℝ => (gaussianSignalScore pair, pair.1)) =
      gaussianReal priorMean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance := by
  exact gaussianSignalPair_score_latent_joint_factorization
    priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance

/--
After a positive measurable latent selection, the exact factorized Gaussian
score/latent law has the normalized restriction of the explicit unselected
Gaussian posterior as its selected conditional law.  This is an
almost-everywhere statement under the actual selected score marginal.  No
posterior-mean formula or equilibrium cutoff is assumed.
-/
theorem lg21_selectedGaussianSignal_factorized_condDistrib_latent_given_score_ae
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    let scoreLaw : Measure ℝ :=
      gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    let selectedJoint : Measure (ℝ × ℝ) :=
      lg21NormalizedRestriction
        (scoreLaw ⊗ₘ gaussianSignalPosteriorKernel
          priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)
    letI : IsProbabilityMeasure selectedJoint :=
      lg21NormalizedRestriction_isProbability
        (scoreLaw ⊗ₘ gaussianSignalPosteriorKernel
          priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)
        (lg21_gaussianSignal_selected_event_ne_zero
          priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
          hselectedMeasurable hselected)
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedJoint := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst selectedJoint =ᵐ[selectedJoint.map Prod.fst]
      selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) := by
  intro scoreLaw selectedJoint
  let rawPosterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  letI : IsMarkovKernel rawPosterior := by
    exact lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hselection : (scoreLaw ⊗ₘ rawPosterior) event ≠ 0 := by
    dsimp [scoreLaw, rawPosterior, event]
    exact lg21_gaussianSignal_selected_event_ne_zero
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected
  have hpositive : ∀ score, selectionMass rawPosterior event score ≠ 0 := by
    dsimp [rawPosterior, event]
    exact lg21_gaussianSignalPosterior_selectionMass_ne_zero
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselected
  have hevent : MeasurableSet event := by
    dsimp [event]
    exact MeasurableSet.univ.prod hselectedMeasurable
  exact condDistrib_snd_given_fst_normalizedRestriction_ae
    (μ := scoreLaw) (κ := rawPosterior) hevent hpositive hselection

/-! ## Exact selected-posterior tilt identity -/

/-- Re-express a tilt as the normalization of its unnormalized exponential
density.  This is kept private because it is only an internal calculation
needed to transport the literal Gaussian fibre through a selected event. -/
private theorem lg21_tilted_eq_normalized_withDensity_exp
    {Alpha : Type*} [MeasurableSpace Alpha]
    (law : Measure Alpha) [NeZero law] (tilt : Alpha → ℝ)
    (hintegrable : Integrable (fun x => Real.exp (tilt x)) law) :
    law.tilted tilt =
      ((law.withDensity (fun x => ENNReal.ofReal (Real.exp (tilt x))) Set.univ)⁻¹) •
        law.withDensity (fun x => ENNReal.ofReal (Real.exp (tilt x))) := by
  let density : Alpha → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (tilt x))
  let normalizer : ℝ := ∫ x, Real.exp (tilt x) ∂law
  have hnormalizer : 0 < normalizer := by
    exact integral_exp_pos hintegrable
  have hmass : law.withDensity density Set.univ = ENNReal.ofReal normalizer := by
    calc
      law.withDensity density Set.univ = ∫⁻ x, density x ∂law := by
        rw [withDensity_apply density MeasurableSet.univ, setLIntegral_univ]
      _ = ENNReal.ofReal normalizer := by
        rw [show density = fun x => ENNReal.ofReal (Real.exp (tilt x)) by rfl,
          ← ofReal_integral_eq_lintegral_ofReal hintegrable
            (Filter.Eventually.of_forall fun x => (Real.exp_pos (tilt x)).le)]
  have hscale_ne_top : (ENNReal.ofReal normalizer)⁻¹ ≠ ∞ := by
    apply ENNReal.inv_ne_top.mpr
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hnormalizer)
  rw [tilted_eq_withDensity_nnreal, hmass,
    ← withDensity_smul' _ _ hscale_ne_top]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  change (↑(NNReal.mk (Real.exp (tilt x) / normalizer) _) : ℝ≥0∞) =
    (ENNReal.ofReal normalizer)⁻¹ * ENNReal.ofReal (Real.exp (tilt x))
  rw [← ENNReal.ofReal_eq_coe_nnreal]
  rw [ENNReal.ofReal_div_of_pos hnormalizer]
  rw [div_eq_mul_inv, mul_comm]

/-- Normalizing a finite nonzero scalar multiple leaves the probability law
unchanged. -/
private theorem lg21_normalize_smul_eq
    {Alpha : Type*} [MeasurableSpace Alpha]
    (law : Measure Alpha) (scale : ℝ≥0∞)
    (hscale_zero : scale ≠ 0) (hscale_top : scale ≠ ∞) :
    ((scale • law) Set.univ)⁻¹ • (scale • law) =
      (law Set.univ)⁻¹ • law := by
  rw [Measure.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hscale_zero) (Or.inl hscale_top)]
  calc
    (scale⁻¹ * (law Set.univ)⁻¹) * scale =
        (scale⁻¹ * scale) * (law Set.univ)⁻¹ := by ac_rfl
    _ = (law Set.univ)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hscale_zero hscale_top, one_mul]

/-- Conditioning a probability law on a positive measurable event commutes
with a finite exponential tilt.  This records equality of normalized laws,
not a choice of conditional value on an unselected fibre. -/
theorem lg21_normalizedRestriction_tilted_commutes
    {Alpha : Type*} [MeasurableSpace Alpha]
    (law : Measure Alpha) [IsProbabilityMeasure law]
    (tilt : Alpha → ℝ) (selected : Set Alpha) (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < law selected)
    (hintegrable : Integrable (fun x => Real.exp (tilt x)) law) :
    lg21NormalizedRestriction (law.tilted tilt) selected =
      (lg21NormalizedRestriction law selected).tilted tilt := by
  let density : Alpha → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (tilt x))
  let weighted : Measure Alpha := (law.restrict selected).withDensity density
  let scale : ℝ≥0∞ := (law.withDensity density Set.univ)⁻¹
  have hmass : law.withDensity density Set.univ =
      ENNReal.ofReal (∫ x, Real.exp (tilt x) ∂law) := by
    calc
      law.withDensity density Set.univ = ∫⁻ x, density x ∂law := by
        rw [withDensity_apply density MeasurableSet.univ, setLIntegral_univ]
      _ = ENNReal.ofReal (∫ x, Real.exp (tilt x) ∂law) := by
        rw [show density = fun x => ENNReal.ofReal (Real.exp (tilt x)) by rfl,
          ← ofReal_integral_eq_lintegral_ofReal hintegrable
            (Filter.Eventually.of_forall fun x => (Real.exp_pos (tilt x)).le)]
  have hscale_zero : scale ≠ 0 := by
    dsimp [scale]
    apply ENNReal.inv_ne_zero.mpr
    rw [hmass]
    exact ENNReal.ofReal_ne_top
  have hscale_top : scale ≠ ∞ := by
    dsimp [scale]
    apply ENNReal.inv_ne_top.mpr
    rw [hmass]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (integral_exp_pos hintegrable))
  have htilted : law.tilted tilt = scale • law.withDensity density := by
    simpa [scale, density] using
      (lg21_tilted_eq_normalized_withDensity_exp law tilt hintegrable)
  have hleft : lg21NormalizedRestriction (law.tilted tilt) selected =
      (weighted Set.univ)⁻¹ • weighted := by
    unfold lg21NormalizedRestriction
    rw [htilted, ← Measure.restrict_apply_univ selected, Measure.restrict_smul,
      restrict_withDensity hselectedMeasurable]
    exact lg21_normalize_smul_eq weighted scale hscale_zero hscale_top
  let selectedLaw : Measure Alpha := lg21NormalizedRestriction law selected
  let selectedScale : ℝ≥0∞ := (law selected)⁻¹
  have hselectedScale_zero : selectedScale ≠ 0 := by
    dsimp [selectedScale]
    apply ENNReal.inv_ne_zero.mpr
    exact measure_ne_top law selected
  have hselectedScale_top : selectedScale ≠ ∞ := by
    dsimp [selectedScale]
    exact ENNReal.inv_ne_top.mpr (ne_of_gt hselected)
  letI : IsProbabilityMeasure selectedLaw := by
    exact lg21NormalizedRestriction_isProbability law selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  letI : NeZero selectedLaw := ⟨IsProbabilityMeasure.ne_zero selectedLaw⟩
  have hintegrableSelected : Integrable (fun x => Real.exp (tilt x)) selectedLaw := by
    dsimp [selectedLaw, lg21NormalizedRestriction]
    exact hintegrable.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hselected))
  have hrightTilted : selectedLaw.tilted tilt =
      ((selectedLaw.withDensity density Set.univ)⁻¹) •
        selectedLaw.withDensity density := by
    simpa [density] using
      (lg21_tilted_eq_normalized_withDensity_exp selectedLaw tilt hintegrableSelected)
  have hright : selectedLaw.tilted tilt = (weighted Set.univ)⁻¹ • weighted := by
    rw [hrightTilted]
    change (((selectedScale • law.restrict selected).withDensity density Set.univ)⁻¹) •
        (selectedScale • law.restrict selected).withDensity density =
      (weighted Set.univ)⁻¹ • weighted
    rw [withDensity_smul_measure]
    exact lg21_normalize_smul_eq weighted selectedScale
      hselectedScale_zero hselectedScale_top
  change lg21NormalizedRestriction (law.tilted tilt) selected = selectedLaw.tilted tilt
  rw [hleft, hright]

/-- The selected literal Gaussian posterior fibre is exactly a linear
exponential tilt of the score-zero selected posterior.  This is a measure
identity, not a PBO convention: the left side is the selected restriction of
the explicit Gaussian RCD fibre. -/
theorem lg21_selectedGaussianSignal_posterior_eq_linear_tilt
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (score : ℝ) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score =
      (lg21NormalizedRestriction
        (gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance))
        selected).tilted
        (fun latentSkill =>
            ((gaussianSignalWeight priorVariance noiseVariance /
              (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ)) * score) *
            latentSkill) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hevent : MeasurableSet (Set.univ ×ˢ selected : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod hselectedMeasurable
  have hvariance : 0 < gaussianSignalPosteriorVariance priorVariance noiseVariance := by
    exact_mod_cast lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hbaseSelected :
      0 < gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance) selected := by
    simpa [gaussianSignalPosteriorKernel_apply] using
      (lg21_gaussianSignalPosterior_selected_pos
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselected 0)
  rw [selectedNormalizedKernel_apply hevent]
  have hfiber : selectedFiber (Set.univ ×ˢ selected : Set (ℝ × ℝ)) score = selected := by
    ext latentSkill
    simp [selectedFiber]
  rw [hfiber]
  change lg21NormalizedRestriction
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
      selected = _
  rw [gaussianSignalPosteriorKernel_apply]
  have hmean :
      gaussianSignalWeight priorVariance noiseVariance * score +
          gaussianSignalPriorWeight priorVariance noiseVariance * priorMean =
        gaussianSignalPriorWeight priorVariance noiseVariance * priorMean +
          gaussianSignalWeight priorVariance noiseVariance * score := by
    ring
  rw [hmean,
    AppliedModelingLib.Probability.gaussianReal_shift_eq_tilted_linear
      (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
      (gaussianSignalWeight priorVariance noiseVariance * score)
      (gaussianSignalPosteriorVariance priorVariance noiseVariance) hvariance]
  have htilt :
      (fun latentSkill : ℝ =>
          ((gaussianSignalWeight priorVariance noiseVariance * score /
              (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ))) *
            latentSkill) =
        (fun latentSkill : ℝ =>
          ((gaussianSignalWeight priorVariance noiseVariance /
              (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ)) * score) *
            latentSkill) := by
    funext latentSkill
    ring
  rw [htilt]
  exact lg21_normalizedRestriction_tilted_commutes
    (gaussianReal
      (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
      (gaussianSignalPosteriorVariance priorVariance noiseVariance))
    _ selected hselectedMeasurable hbaseSelected
    (integrable_exp_mul_gaussianReal
      (μ := gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
      (v := gaussianSignalPosteriorVariance priorVariance noiseVariance)
      ((gaussianSignalWeight priorVariance noiseVariance /
        (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ)) * score))

/--
The score-zero Gaussian posterior, after a latent selection, is exactly the
fixed quadratic likelihood base of the selected prior.  This identifies the
likelihood factor as part of the literal Bayesian update rather than a
convenient candidate payoff convention.
-/
theorem lg21_selectedGaussianSignal_zeroPosterior_eq_likelihoodBase
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    lg21NormalizedRestriction
      (gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance)) selected =
      lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction
          (gaussianReal priorMean priorVariance.toNNReal) selected)
        noiseVariance := by
  have htilted :
      gaussianReal
          (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
          (gaussianSignalPosteriorVariance priorVariance noiseVariance) =
        (gaussianReal priorMean priorVariance.toNNReal).tilted
          (fun latentSkill : ℝ => -latentSkill ^ 2 / (2 * noiseVariance)) := by
    rw [AppliedModelingLib.Probability.gaussianReal_tilted_quadratic_eq_posterior
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance]
    congr 1
    simp only [gaussianSignalPriorWeight]
    ring
  rw [htilted, lg21_normalizedRestriction_tilted_commutes]
  · rfl
  · exact hselectedMeasurable
  · exact hselected
  · apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x))
        (by positivity))

/--
The literal Gaussian selected posterior is the canonical selected Gaussian
likelihood family: a score-independent quadratic update followed by the
score's linear exponential tilt.  This equality of measures is the bridge
needed to reuse the proved shifted-score integrability theorem.
-/
theorem lg21_selectedGaussianSignal_posterior_eq_canonical
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (score : ℝ) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score =
      (lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction
          (gaussianReal priorMean priorVariance.toNNReal) selected)
        noiseVariance).tilted
        (fun latentSkill => noiseVariance⁻¹ * score * latentSkill) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  rw [lg21_selectedGaussianSignal_posterior_eq_linear_tilt
    priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
    hselectedMeasurable hselected score,
    lg21_selectedGaussianSignal_zeroPosterior_eq_likelihoodBase
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected]
  congr 2
  funext latentSkill
  change
    ((gaussianSignalWeight priorVariance noiseVariance /
      (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ)) * score) *
        latentSkill =
      noiseVariance⁻¹ * score * latentSkill
  simp only [gaussianSignalWeight, gaussianSignalPosteriorVariance]
  have hsum : priorVariance + noiseVariance ≠ 0 :=
    ne_of_gt (add_pos hpriorVariance hnoiseVariance)
  have hnoise : noiseVariance ≠ 0 := ne_of_gt hnoiseVariance
  rw [Real.coe_toNNReal _
    (div_nonneg (mul_nonneg hpriorVariance.le hnoiseVariance.le)
      (add_nonneg hpriorVariance.le hnoiseVariance.le))]
  field_simp

/--
The literal selected Gaussian posterior mean is integrable under every
Gaussian score law generated by a latent skill.  The proof transports the
already-established canonical likelihood-family bound through the exact
posterior-law identity above.
-/
theorem lg21_selectedGaussianSignal_posteriorMean_integrable_gaussianShift
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    ∀ skill : ℝ,
      Integrable
        (fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected) score)
        (gaussianReal skill noiseVariance.toNNReal) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have hnoiseVarianceNN : 0 < (noiseVariance.toNNReal : ℝ) :=
    Real.toNNReal_pos.mpr hnoiseVariance
  intro skill
  have hcanonical :=
    lg21_selectedGaussian_canonicalPosteriorMean_integrable_gaussianShift
      priorMean priorVariance.toNNReal selected noiseVariance.toNNReal
      hpriorVarianceNN hselected hnoiseVarianceNN skill
  apply hcanonical.congr
  filter_upwards with score
  rw [lg21_selectedGaussianSignal_posterior_eq_canonical
    priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
    hselectedMeasurable hselected score]
  have hnoiseVarianceCoe : (noiseVariance.toNNReal : ℝ) = noiseVariance :=
    Real.coe_toNNReal _ hnoiseVariance.le
  rw [hnoiseVarianceCoe]
  rfl

/-- The mean of the actual selected Gaussian posterior fibre is strictly
increasing in the reported score.  It is derived from the literal selected
RCD fibre above; no canonical PBO formula or cutoff is assumed. -/
theorem lg21_selectedGaussianSignal_posteriorMean_strictMono
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    StrictMono (fun score =>
      ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hvariance : 0 < gaussianSignalPosteriorVariance priorVariance noiseVariance := by
    exact_mod_cast lg21_gaussianSignalPosteriorVariance_pos
      priorVariance noiseVariance hpriorVariance hnoiseVariance
  have hvarianceReal : 0 <
      (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ) := by
    exact_mod_cast hvariance
  have hbaseSelected :
      0 < gaussianReal
        (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance) selected := by
    simpa [gaussianSignalPosteriorKernel_apply] using
      (lg21_gaussianSignalPosterior_selected_pos
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselected 0)
  have hweight : 0 < gaussianSignalWeight priorVariance noiseVariance := by
    change 0 < priorVariance / (priorVariance + noiseVariance)
    exact div_pos hpriorVariance (add_pos hpriorVariance hnoiseVariance)
  have hcoefficient : 0 < gaussianSignalWeight priorVariance noiseVariance /
      (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ) :=
    div_pos hweight hvarianceReal
  have hmono := lg21_selectedGaussianExponentialTiltMean_strictMono
    (gaussianSignalPriorWeight priorVariance noiseVariance * priorMean)
    (gaussianSignalPosteriorVariance priorVariance noiseVariance) selected
    (gaussianSignalWeight priorVariance noiseVariance /
      (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ))
    (ne_of_gt hvariance) hbaseSelected hcoefficient
  intro lowScore highScore hlowHigh
  change (∫ latentSkill, latentSkill ∂selectedNormalizedKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected) lowScore) <
    ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected) highScore
  rw [lg21_selectedGaussianSignal_posterior_eq_linear_tilt
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected lowScore,
    lg21_selectedGaussianSignal_posterior_eq_linear_tilt
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected highScore]
  simpa [lg21SelectedGaussianExponentialTiltMean, lg21ExponentialTiltMean] using
    hmono hlowHigh

/-- A literal selected-posterior PBO with the source model's score-law
integrability has a strictly increasing pre-test expected payoff.  The PBO
identity is explicit rather than inferred from a field name; a source bridge
can supply it from the actual reporter conditional expectation. -/
theorem lg21_selectedGaussianSignal_expectedPBO_strictMono
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (reportedPBO : ℝ → ℝ)
    (hreportedPBO : ∀ score, reportedPBO score =
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
        selected)
    (hintegrable : ∀ skill,
      Integrable reportedPBO (gaussianReal skill noiseVariance.toNNReal)) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    StrictMono (fun skill =>
      ∫ score, reportedPBO score ∂gaussianReal skill noiseVariance.toNNReal) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hposteriorStrict : StrictMono (fun score =>
      ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) score) := by
    exact lg21_selectedGaussianSignal_posteriorMean_strictMono
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected
  have hevent : MeasurableSet (Set.univ ×ˢ selected : Set (ℝ × ℝ)) :=
    MeasurableSet.univ.prod hselectedMeasurable
  have hnormalize :
      (fun score => ∫ latentSkill, latentSkill ∂selectedNormalizedKernel
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
          (Set.univ ×ˢ selected) score) =
        (fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
          (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
          selected) := by
    funext score
    rw [selectedNormalizedKernel_apply hevent]
    congr 3
    ext latentSkill
    simp [selectedFiber]
  have hdirectStrict : StrictMono (fun score =>
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
        selected) := by
    rw [← hnormalize]
    exact hposteriorStrict
  have hreportedStrict : StrictMono reportedPBO := by
    intro lowScore highScore hlowHigh
    rw [hreportedPBO lowScore, hreportedPBO highScore]
    exact hdirectStrict hlowHigh
  exact lg21_gaussianShiftExpectedPayoff_strictMono
    reportedPBO noiseVariance.toNNReal hreportedStrict hintegrable

/-- A positive selected Gaussian latent event gives a selected score law with
the same null sets as the unselected score law.  This transports an on-path
PBO identity from the actual reporter score law to every Gaussian test draw;
it does not choose a value on a zero-mass selected branch. -/
theorem lg21_gaussianSignal_scoreLaw_absolutelyContinuous_selectedScoreLaw
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal ≪
      normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  let scoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let rawPosterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  have hevent : MeasurableSet event := by
    dsimp [event]
    exact MeasurableSet.univ.prod hselectedMeasurable
  have hpositive : ∀ score, selectionMass rawPosterior event score ≠ 0 := by
    dsimp [rawPosterior, event]
    exact lg21_gaussianSignalPosterior_selectionMass_ne_zero
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselected
  have hnormalizer_ne_zero : ((scoreLaw ⊗ₘ rawPosterior) event)⁻¹ ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    exact measure_ne_top _ _
  have hwithDensity : scoreLaw ≪
      scoreLaw.withDensity (selectionMass rawPosterior event) := by
    exact withDensity_absolutelyContinuous'
      (selectionMass_measurable hevent).aemeasurable
      (Filter.Eventually.of_forall hpositive)
  change scoreLaw ≪ ((scoreLaw ⊗ₘ rawPosterior) event)⁻¹ •
    scoreLaw.withDensity (selectionMass rawPosterior event)
  exact hwithDensity.smul_right hnormalizer_ne_zero

/-- Every individual Gaussian score law is absolutely continuous with respect
to the attained positive selected score law.  The result is a null-set
transport statement, not a pointwise posterior convention. -/
theorem lg21_gaussianTestLaw_absolutelyContinuous_selectedScoreLaw
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (skill : ℝ) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    gaussianReal skill noiseVariance.toNNReal ≪
      normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hnoiseNN : 0 < noiseVariance.toNNReal :=
    Real.toNNReal_pos.mpr hnoiseVariance
  have hscoreNN : 0 < (priorVariance + noiseVariance).toNNReal :=
    Real.toNNReal_pos.mpr (add_pos hpriorVariance hnoiseVariance)
  exact
    (AppliedModelingLib.Probability.gaussianReal_absolutelyContinuous_of_positive_variances
      skill priorMean hnoiseNN hscoreNN).trans
      (lg21_gaussianSignal_scoreLaw_absolutelyContinuous_selectedScoreLaw
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselectedMeasurable hselected)

/-- An on-path selected-PBO identity need only hold almost everywhere under
the attained reporter score law.  Literal Gaussian absolute-continuity
transport carries it to every pre-test score law, so the resulting expected
payoff is still strictly increasing in latent skill. -/
theorem lg21_selectedGaussianSignal_expectedPBO_strictMono_of_ae
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (reportedPBO : ℝ → ℝ)
    (hreportedPBO : reportedPBO =ᵐ[
      normalizedSelectedBase
        (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
        (Set.univ ×ˢ selected)]
      fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
        selected)
    (hintegrable : ∀ skill,
      Integrable reportedPBO (gaussianReal skill noiseVariance.toNNReal)) :
    letI : IsMarkovKernel
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
      lg21_gaussianSignalPosteriorKernel_isMarkov
        priorMean priorVariance noiseVariance
    StrictMono (fun skill =>
      ∫ score, reportedPBO score ∂gaussianReal skill noiseVariance.toNNReal) := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance) :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  let canonicalPBO : ℝ → ℝ := fun score =>
    ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
      (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
      selected
  have htransport : ∀ skill,
      reportedPBO =ᵐ[gaussianReal skill noiseVariance.toNNReal] canonicalPBO := by
    intro skill
    exact
      (lg21_gaussianTestLaw_absolutelyContinuous_selectedScoreLaw
        priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
        hselectedMeasurable hselected skill).ae_eq (by
          simpa [canonicalPBO] using hreportedPBO)
  have hcanonicalIntegrable : ∀ skill,
      Integrable canonicalPBO (gaussianReal skill noiseVariance.toNNReal) := by
    intro skill
    exact (hintegrable skill).congr (htransport skill)
  have hcanonicalStrict : StrictMono (fun skill =>
      ∫ score, canonicalPBO score ∂gaussianReal skill noiseVariance.toNNReal) := by
    exact lg21_selectedGaussianSignal_expectedPBO_strictMono
      priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
      hselectedMeasurable hselected canonicalPBO (by
        intro score
        rfl) hcanonicalIntegrable
  intro lowSkill highSkill hlowHigh
  calc
    (∫ score, reportedPBO score ∂gaussianReal lowSkill noiseVariance.toNNReal) =
        ∫ score, canonicalPBO score ∂gaussianReal lowSkill noiseVariance.toNNReal :=
      integral_congr_ae (htransport lowSkill)
    _ < ∫ score, canonicalPBO score ∂gaussianReal highSkill noiseVariance.toNNReal :=
      hcanonicalStrict hlowHigh
    _ = ∫ score, reportedPBO score ∂gaussianReal highSkill noiseVariance.toNNReal :=
      (integral_congr_ae (htransport highSkill)).symm

/-- Per-public-base report-required adapter for the literal selected Gaussian
PBO.  The source must state both the actual Gaussian score law and the exact
conditional-mean identity; this theorem then supplies the strict ex-ante
payoff needed by the positive-mass closure without assuming a cutoff. -/
theorem lg21_reportRequired_takeExpectedPayoff_strictMono_of_selectedGaussianPBO
    {Base : Type*}
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) (base : Base)
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (htestLaw : ∀ skill,
      E.testLaw skill base = gaussianReal skill noiseVariance.toNNReal)
    (hreportedPBO : ∀ score, E.reportedPayoff base score =
      ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance score)
        selected)
    (hintegrable : ∀ skill,
      Integrable (E.reportedPayoff base)
        (gaussianReal skill noiseVariance.toNNReal)) :
    StrictMono (fun skill =>
      lg21ReportRequiredSequentialTakeExpectedPayoff E skill base) := by
  have hstrict := lg21_selectedGaussianSignal_expectedPBO_strictMono
    priorMean priorVariance noiseVariance selected hpriorVariance hnoiseVariance
    hselectedMeasurable hselected (E.reportedPayoff base) hreportedPBO hintegrable
  intro lowSkill highSkill hlowHigh
  change (∫ score, E.reportedPayoff base score ∂E.testLaw lowSkill base) <
    ∫ score, E.reportedPayoff base score ∂E.testLaw highSkill base
  rw [htestLaw lowSkill, htestLaw highSkill]
  exact hstrict hlowHigh

end

end LG21TestOptionalPolicies
