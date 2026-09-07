import AppliedModelingLib.Foundations.Probability.GaussianSignalKernelRCD

/-!
# Sequential Gaussian Signal RCD Transport

This module is the induction transition for a finite family of independent
additive Gaussian signals.  It starts from a *proved* joint-law factorization
for an arbitrary measurable base profile and latent skill, adds one
independent Gaussian signal, and identifies the actual extended joint law
and conditional latent-skill kernel.  The statement is deliberately
measure-level: it has no supplied posterior field or named belief object.

An application to a finite source profile must still prove the base-case
factorization and use this transition once per coordinate.  Equality of the
conditional kernels is, correctly, only almost everywhere in the actual
extended observation marginal.
-/

namespace AppliedModelingLib
namespace Probability

universe u

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Add one independent centered Gaussian noise coordinate to an actual
base-profile/latent-skill joint law, retaining the old base profile, the new
score, and the latent skill. -/
def gaussianSignalExtendBaseLatentLaw {α : Type*} [MeasurableSpace α]
    (baseLatentLaw : Measure (α × ℝ)) (noiseVariance : ℝ) :
    Measure ((α × ℝ) × ℝ) :=
  (baseLatentLaw.prod (gaussianReal 0 noiseVariance.toNNReal)).map
    (fun primitive : (α × ℝ) × ℝ =>
      ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2))

/-- The measurable repackaging map used by
`gaussianSignalExtendBaseLatentLaw`. -/
private theorem measurable_gaussianSignalExtendBaseLatent_repackage
    {α : Type*} [MeasurableSpace α] :
    Measurable (fun primitive : (α × ℝ) × ℝ =>
      ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)) := by
  fun_prop

/-- If an actual base-profile/latent-skill law has a proved Gaussian
factorization, adjoining independent additive Gaussian noise gives the
standard one-step Gaussian signal law.  This is the reusable finite-profile
induction transition. -/
theorem gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
    {α : Type*} [MeasurableSpace α]
    (baseLaw : Measure α) [IsProbabilityMeasure baseLaw]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (baseLatentLaw : Measure (α × ℝ))
    (hbaseLatentLaw :
      baseLatentLaw =
        baseLaw ⊗ₘ gaussianLocationKernel mean hmean priorVariance.toNNReal) :
    gaussianSignalExtendBaseLatentLaw baseLatentLaw noiseVariance =
      gaussianSignalBaseScoreLatentLaw baseLaw mean hmean priorVariance noiseVariance := by
  let posteriorLocation : Kernel α ℝ :=
    gaussianLocationKernel mean hmean priorVariance.toNNReal
  let scoreNoise : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let follow : (α × ℝ) × ℝ → (α × ℝ) × ℝ :=
    fun primitive => ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
  have hfollow : Measurable follow := by
    exact measurable_gaussianSignalExtendBaseLatent_repackage
  let stage : ℝ × ℝ → ℝ × ℝ := fun pair => (pair.1 + pair.2, pair.1)
  have hstage : Measurable stage := by fun_prop
  letI : IsMarkovKernel posteriorLocation :=
    gaussianLocationKernel_isMarkov mean hmean priorVariance.toNNReal
  letI : IsProbabilityMeasure scoreNoise := by
    dsimp [scoreNoise]
    infer_instance
  change (baseLatentLaw.prod scoreNoise).map follow = _
  rw [hbaseLatentLaw]
  unfold gaussianSignalBaseScoreLatentLaw gaussianSignalJointKernel
  rw [← Measure.compProd_const]
  rw [← Measure.compProd_assoc]
  rw [Measure.map_map hfollow (MeasurableEquiv.measurable _)]
  have hfun : follow ∘ MeasurableEquiv.prodAssoc.symm =
      MeasurableEquiv.prodAssoc.symm ∘ Prod.map id stage := by
    funext primitive
    rfl
  rw [hfun]
  rw [← Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  rw [← Measure.compProd_map hstage]
  have hkernel :
      posteriorLocation ⊗ₖ Kernel.const (α × ℝ) scoreNoise =
        posteriorLocation ×ₖ Kernel.const α scoreNoise := by
    ext base target htarget
    rw [Kernel.compProd_apply htarget, Kernel.prod_apply,
      Measure.prod_apply htarget]
    simp only [Kernel.const_apply]
  rw [hkernel]

/-- The a.e. conditional latent-skill law after adjoining one independent
Gaussian signal to a proved Gaussian base-profile factorization. -/
theorem gaussianSignalExtendBaseLatent_condDistrib_latent_given_baseScore
    {α : Type*} [MeasurableSpace α]
    (baseLaw : Measure α) [IsProbabilityMeasure baseLaw]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (baseLatentLaw : Measure (α × ℝ))
    (hbaseLatentLaw :
      baseLatentLaw =
        baseLaw ⊗ₘ gaussianLocationKernel mean hmean priorVariance.toNNReal) :
    let law := gaussianSignalExtendBaseLatentLaw baseLatentLaw noiseVariance
    letI : IsProbabilityMeasure law := by
      change IsProbabilityMeasure
        (gaussianSignalExtendBaseLatentLaw baseLatentLaw noiseVariance)
      rw [gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
        baseLaw mean hmean priorVariance noiseVariance baseLatentLaw hbaseLatentLaw]
      unfold gaussianSignalBaseScoreLatentLaw
      letI : IsMarkovKernel
          (gaussianSignalJointKernel mean hmean priorVariance noiseVariance) :=
        gaussianSignalJointKernel_isMarkov mean hmean priorVariance noiseVariance
      exact Measure.isProbabilityMeasure_map (by fun_prop)
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst law =ᵐ[law.map Prod.fst]
      gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance := by
  intro law
  have heq := gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
    baseLaw mean hmean priorVariance noiseVariance baseLatentLaw hbaseLatentLaw
  letI : IsProbabilityMeasure law := by
    change IsProbabilityMeasure
      (gaussianSignalExtendBaseLatentLaw baseLatentLaw noiseVariance)
    rw [heq]
    unfold gaussianSignalBaseScoreLatentLaw
    letI : IsMarkovKernel
        (gaussianSignalJointKernel mean hmean priorVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov mean hmean priorVariance noiseVariance
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  letI : IsFiniteMeasure law := ⟨by simp⟩
  let scoreKernel : Kernel α ℝ :=
    gaussianLocationKernel mean hmean (priorVariance + noiseVariance).toNNReal
  let posteriorKernel : Kernel (α × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov mean hmean
      (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov mean hmean priorVariance noiseVariance
  have hfactor : law = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
    calc
      law = gaussianSignalBaseScoreLatentLaw
          baseLaw mean hmean priorVariance noiseVariance := heq
      _ = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
        exact gaussianSignalBaseScoreLatentLaw_factorization
          baseLaw mean hmean priorVariance noiseVariance
          hpriorVariance hnoiseVariance
  have hfst : law.map Prod.fst = baseLaw ⊗ₘ scoreKernel := by
    rw [hfactor]
    exact Measure.fst_compProd _ _
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := law) (X := Prod.fst) (Y := Prod.snd) (κ := posteriorKernel)
    measurable_fst measurable_snd
  calc
    law.map (fun pair => (Prod.fst pair, Prod.snd pair)) = law := by
      change law.map id = law
      exact Measure.map_id
    _ = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := hfactor
    _ = law.map Prod.fst ⊗ₘ posteriorKernel := by rw [hfst]

/-- A nondegenerate Gaussian prior assigns strictly positive weight to one
further nondegenerate observed score. -/
theorem gaussianSignalWeight_pos
    {priorVariance noiseVariance : ℝ}
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    0 < gaussianSignalWeight priorVariance noiseVariance := by
  exact div_pos hpriorVariance (add_pos hpriorVariance hnoiseVariance)

/-- The residual conditional variance after one nondegenerate Gaussian score
remains strictly positive. -/
theorem gaussianSignalPosteriorVariance_pos
    {priorVariance noiseVariance : ℝ}
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    0 < (gaussianSignalPosteriorVariance priorVariance noiseVariance : ℝ) := by
  rw [NNReal.coe_pos, Real.toNNReal_pos]
  exact div_pos (mul_pos hpriorVariance hnoiseVariance)
    (add_pos hpriorVariance hnoiseVariance)

/-- The conditional mean of the canonical one-step posterior kernel is the
displayed affine score formula. -/
theorem gaussianSignalPosteriorBaseKernel_integral_id
    {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) (base : α) (score : ℝ) :
    ∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
      mean hmean priorVariance noiseVariance (base, score) =
      gaussianSignalWeight priorVariance noiseVariance * score +
        gaussianSignalPriorWeight priorVariance noiseVariance * mean base := by
  rw [gaussianSignalPosteriorBaseKernel_apply, integral_id_gaussianReal]

/-- Holding a full base profile fixed, the actual conditional expected skill
under the canonical one-step Gaussian posterior is strictly increasing in the
new score.  Combined with
`gaussianSignalExtendBaseLatent_condDistrib_latent_given_baseScore`, this is
an a.e. fact about the extended source law, not a supplied PBO assumption. -/
theorem strictMono_gaussianSignalPosteriorBaseKernel_integral_id
    {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) (base : α) :
    StrictMono (fun score : ℝ =>
      ∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
        mean hmean priorVariance noiseVariance (base, score)) := by
  intro lower upper hlowerUpper
  change
    (∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
      mean hmean priorVariance noiseVariance (base, lower)) <
    (∫ skill, skill ∂gaussianSignalPosteriorBaseKernel
      mean hmean priorVariance noiseVariance (base, upper))
  rw [gaussianSignalPosteriorBaseKernel_integral_id,
    gaussianSignalPosteriorBaseKernel_integral_id]
  have hweight : 0 < gaussianSignalWeight priorVariance noiseVariance :=
    gaussianSignalWeight_pos hpriorVariance hnoiseVariance
  nlinarith

/-- The actual joint law of a finite observed Gaussian profile and its latent
coordinate.  Every observation is the common latent coordinate plus its own
independent centered Gaussian noise. -/
def gaussianFiniteProfileLatentLaw
    {Index : Type*} [Fintype Index]
    (priorMean priorVariance : ℝ) (noiseVariance : Index → ℝ) :
    Measure ((Index → ℝ) × ℝ) :=
  ((gaussianReal priorMean priorVariance.toNNReal).prod
    (Measure.pi fun index => gaussianReal 0 (noiseVariance index).toNNReal)).map
    (fun primitive =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1))

/-- Splitting the observed profile indexed by `Option Index` into the old
profile and the newly added coordinate. -/
def gaussianFiniteProfileOptionSplit (Index : Type*) [Fintype Index] :
    (Option Index → ℝ) ≃ᵐ (Index → ℝ) × ℝ :=
  MeasurableEquiv.piOptionEquivProd (fun _ : Option Index => ℝ)

/-- Transport a Gaussian latent-skill factorization through a measurable
equivalence of the retained base profile.  The latent coordinate is left
unchanged.  This is the profile-reindexing step required by the finite
`Option` induction. -/
theorem gaussianLocationFactorization_map_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (baseLaw : Measure α) [IsProbabilityMeasure baseLaw]
    (mean : α → ℝ) (hmean : Measurable mean) (variance : ℝ≥0) :
    (baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance).map
        (Prod.map e id) =
      (baseLaw.map e) ⊗ₘ gaussianLocationKernel
        (mean ∘ e.symm) (hmean.comp e.symm.measurable) variance := by
  let sourceKernel : Kernel α ℝ := gaussianLocationKernel mean hmean variance
  let targetKernel : Kernel β ℝ := gaussianLocationKernel
    (mean ∘ e.symm) (hmean.comp e.symm.measurable) variance
  have hmap : Measurable
      (Prod.map (e : α → β) (id : ℝ → ℝ)) := by fun_prop
  letI : IsMarkovKernel sourceKernel :=
    gaussianLocationKernel_isMarkov mean hmean variance
  letI : IsMarkovKernel targetKernel :=
    gaussianLocationKernel_isMarkov (mean ∘ e.symm)
      (hmean.comp e.symm.measurable) variance
  ext target htarget
  have hpre : MeasurableSet ((Prod.map e id) ⁻¹' target) :=
    htarget.preimage hmap
  change ((baseLaw ⊗ₘ sourceKernel).map (Prod.map e id)) target =
    (baseLaw.map e ⊗ₘ targetKernel) target
  rw [Measure.map_apply hmap htarget, Measure.compProd_apply hpre,
    Measure.compProd_apply htarget]
  rw [MeasureTheory.lintegral_map
    (Kernel.measurable_kernel_prodMk_left htarget) e.measurable]
  congr with base
  have hkernel : targetKernel (e base) = sourceKernel base := by
    rw [gaussianLocationKernel_apply, gaussianLocationKernel_apply]
    simp [Function.comp_apply]
  rw [hkernel]
  congr 1

private theorem measurable_gaussianFiniteProfilePrimitiveMap
    {Index : Type*} [Fintype Index] :
    Measurable (fun primitive : ℝ × (Index → ℝ) =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1)) := by
  exact (measurable_pi_lambda _ fun index =>
    measurable_fst.add ((measurable_pi_apply index).comp measurable_snd)).prodMk
      measurable_fst

/-- The exact source-law transition when one Gaussian profile coordinate is
adjoined.  This is the Option step used by the finite-profile induction: it
does not assume a posterior formula, only rearranges independent product
noise and the observable profile. -/
theorem gaussianFiniteProfileLatentLaw_option_eq_extend
    {Index : Type*} [Fintype Index]
    (priorMean priorVariance : ℝ) (noiseVariance : Option Index → ℝ) :
    (gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
      (fun profileSkill =>
        (gaussianFiniteProfileOptionSplit Index profileSkill.1, profileSkill.2)) =
      gaussianSignalExtendBaseLatentLaw
        (gaussianFiniteProfileLatentLaw priorMean priorVariance
          (fun index => noiseVariance (some index)))
        (noiseVariance none) := by
  let prior : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
  let tailNoise : Measure (Index → ℝ) :=
    Measure.pi fun index => gaussianReal 0 (noiseVariance (some index)).toNNReal
  let headNoise : Measure ℝ := gaussianReal 0 (noiseVariance none).toNNReal
  let optionNoise : Measure (Option Index → ℝ) :=
    Measure.pi fun index => gaussianReal 0 (noiseVariance index).toNNReal
  let noiseSplit : (Option Index → ℝ) ≃ᵐ (Index → ℝ) × ℝ :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option Index => ℝ)
  let profileSplit : (Option Index → ℝ) ≃ᵐ (Index → ℝ) × ℝ :=
    gaussianFiniteProfileOptionSplit Index
  let baseMap : ℝ × (Index → ℝ) → (Index → ℝ) × ℝ :=
    fun primitive =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1)
  let optionProfileMap : ℝ × (Option Index → ℝ) → (Option Index → ℝ) × ℝ :=
    fun primitive =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1)
  let follow : ((Index → ℝ) × ℝ) × ℝ → ((Index → ℝ) × ℝ) × ℝ :=
    fun primitive =>
      ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
  have hbaseMap : Measurable baseMap :=
    measurable_gaussianFiniteProfilePrimitiveMap
  have hoptionProfileMap : Measurable optionProfileMap :=
    measurable_gaussianFiniteProfilePrimitiveMap
  have hfollow : Measurable follow := by fun_prop
  have hassoc : Measurable
      (MeasurableEquiv.prodAssoc :
        (ℝ × (Index → ℝ)) × ℝ ≃ᵐ ℝ × ((Index → ℝ) × ℝ)) := by
    fun_prop
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    infer_instance
  letI : IsProbabilityMeasure tailNoise := by
    dsimp [tailNoise]
    infer_instance
  letI : IsProbabilityMeasure headNoise := by
    dsimp [headNoise]
    infer_instance
  have hnoise : (tailNoise.prod headNoise).map noiseSplit.symm = optionNoise := by
    simpa [tailNoise, headNoise, optionNoise, noiseSplit] using
      (Measure.pi_map_piOptionEquivProd
        (fun index : Option Index =>
          gaussianReal 0 (noiseVariance index).toNNReal))
  have hproduct :
      (prior.prod (tailNoise.prod headNoise)).map
          (Prod.map id noiseSplit.symm) = prior.prod optionNoise := by
    rw [← Measure.map_prod_map prior (tailNoise.prod headNoise)
      measurable_id noiseSplit.symm.measurable]
    simpa [hnoise]
  dsimp [gaussianFiniteProfileLatentLaw,
    gaussianSignalExtendBaseLatentLaw]
  change ((prior.prod optionNoise).map optionProfileMap).map
      (fun profileSkill => (profileSplit profileSkill.1, profileSkill.2)) =
    (((prior.prod tailNoise).map baseMap).prod headNoise).map follow
  rw [Measure.map_map (by fun_prop) hoptionProfileMap]
  rw [← hproduct]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← Measure.prodAssoc_prod]
  rw [Measure.map_map (by fun_prop) hassoc]
  change ((prior.prod tailNoise).prod headNoise).map
      (follow ∘ Prod.map baseMap id) =
    (((prior.prod tailNoise).map baseMap).prod headNoise).map follow
  calc
    ((prior.prod tailNoise).prod headNoise).map
        (follow ∘ Prod.map baseMap id) =
        (((prior.prod tailNoise).map baseMap).prod
          (headNoise.map id)).map follow := by
          rw [Measure.map_prod_map (prior.prod tailNoise) headNoise
            hbaseMap measurable_id]
          rw [Measure.map_map hfollow (by fun_prop)]
    _ = (((prior.prod tailNoise).map baseMap).prod headNoise).map follow := by
          simp

/-- One `Option`-indexed finite-profile induction step.  From a proved
Gaussian factorization for an arbitrary finite old profile, this constructs a
Gaussian factorization for the profile with one more independent additive
Gaussian observation.  The conclusion is existential only about the
*derived* base law, mean, and positive variance; it does not take any
posterior formula as an assumption. -/
theorem gaussianFiniteProfileLatentLaw_option_exists_gaussianLocationFactorization
    {Index : Type*} [Fintype Index]
    (priorMean priorVariance : ℝ) (noiseVariance : Option Index → ℝ)
    (hheadNoiseVariance : 0 < noiseVariance none)
    (htail : ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
        (variance : ℝ) (hmean : Measurable mean),
        IsProbabilityMeasure baseLaw ∧ 0 < variance ∧
          gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)) =
            baseLaw ⊗ₘ gaussianLocationKernel mean hmean
              variance.toNNReal) :
    ∃ (baseLaw : Measure (Option Index → ℝ))
        (mean : (Option Index → ℝ) → ℝ) (variance : ℝ)
        (hmean : Measurable mean),
      IsProbabilityMeasure baseLaw ∧ 0 < variance ∧
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
          baseLaw ⊗ₘ gaussianLocationKernel mean hmean
            variance.toNNReal := by
  rcases htail with ⟨tailBaseLaw, tailMean, tailVariance,
    htailMean, htailBaseLaw, htailVariance, htailFactorization⟩
  letI : IsProbabilityMeasure tailBaseLaw := htailBaseLaw
  let scoreKernel : Kernel (Index → ℝ) ℝ :=
    gaussianLocationKernel tailMean htailMean
      (tailVariance + noiseVariance none).toNNReal
  let posteriorKernel : Kernel ((Index → ℝ) × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel tailMean htailMean tailVariance
      (noiseVariance none)
  let newBaseLaw : Measure ((Index → ℝ) × ℝ) :=
    tailBaseLaw ⊗ₘ scoreKernel
  let newMean : (Index → ℝ) × ℝ → ℝ := fun profileScore =>
    gaussianSignalWeight tailVariance (noiseVariance none) * profileScore.2 +
      gaussianSignalPriorWeight tailVariance (noiseVariance none) *
        tailMean profileScore.1
  let newVariance : ℝ :=
    tailVariance * noiseVariance none /
      (tailVariance + noiseVariance none)
  let profileSplit : (Option Index → ℝ) ≃ᵐ (Index → ℝ) × ℝ :=
    gaussianFiniteProfileOptionSplit Index
  have hnewMean : Measurable newMean := by
    dsimp [newMean]
    fun_prop
  have hnewVariance : 0 < newVariance := by
    dsimp [newVariance]
    exact div_pos (mul_pos htailVariance hheadNoiseVariance)
      (add_pos htailVariance hheadNoiseVariance)
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov tailMean htailMean
      (tailVariance + noiseVariance none).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov tailMean htailMean tailVariance
      (noiseVariance none)
  have hupdate :
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
        gaussianSignalBaseScoreLatentLaw tailBaseLaw tailMean htailMean
          tailVariance (noiseVariance none) :=
    gaussianSignalExtendBaseLatentLaw_eq_baseScoreLatentLaw
      tailBaseLaw tailMean htailMean tailVariance (noiseVariance none)
      (gaussianFiniteProfileLatentLaw priorMean priorVariance
        (fun index => noiseVariance (some index))) htailFactorization
  have hnewFactorization :
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
        newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
          newVariance.toNNReal := by
    calc
      gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) =
          gaussianSignalBaseScoreLatentLaw tailBaseLaw tailMean htailMean
            tailVariance (noiseVariance none) := hupdate
      _ = tailBaseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
        exact gaussianSignalBaseScoreLatentLaw_factorization
          tailBaseLaw tailMean htailMean tailVariance (noiseVariance none)
          htailVariance hheadNoiseVariance
      _ = newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
          newVariance.toNNReal := by
        dsimp [newBaseLaw, posteriorKernel, newMean, newVariance]
        rfl
  have hnewBaseLaw : IsProbabilityMeasure newBaseLaw := by
    dsimp [newBaseLaw]
    infer_instance
  letI : IsProbabilityMeasure newBaseLaw := hnewBaseLaw
  refine ⟨newBaseLaw.map profileSplit.symm, newMean ∘ profileSplit,
    newVariance, hnewMean.comp profileSplit.measurable, ?_, hnewVariance, ?_⟩
  · exact Measure.isProbabilityMeasure_map profileSplit.symm.measurable.aemeasurable
  have hround :
      ((gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
          (Prod.map profileSplit id)).map (Prod.map profileSplit.symm id) =
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    have hfun :
        (Prod.map
          (profileSplit.symm : ((Index → ℝ) × ℝ) → (Option Index → ℝ))
          (id : ℝ → ℝ)) ∘
          (Prod.map
            (profileSplit : (Option Index → ℝ) → (Index → ℝ) × ℝ)
            (id : ℝ → ℝ)) =
          (id : ((Option Index → ℝ) × ℝ) → (Option Index → ℝ) × ℝ) := by
      funext profileSkill
      rcases profileSkill with ⟨profile, skill⟩
      change (profileSplit.symm (profileSplit profile), skill) = (profile, skill)
      simp
    rw [hfun, Measure.map_id]
  have hoptionStep :
      (gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
          (Prod.map profileSplit id) =
        gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none) := by
    simpa [profileSplit] using
      (gaussianFiniteProfileLatentLaw_option_eq_extend
        priorMean priorVariance noiseVariance)
  calc
    gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
        ((gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance).map
          (Prod.map profileSplit id)).map (Prod.map profileSplit.symm id) :=
          hround.symm
    _ = (gaussianSignalExtendBaseLatentLaw
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noiseVariance (some index)))
          (noiseVariance none)).map (Prod.map profileSplit.symm id) := by
          rw [hoptionStep]
    _ = (newBaseLaw ⊗ₘ gaussianLocationKernel newMean hnewMean
          newVariance.toNNReal).map (Prod.map profileSplit.symm id) := by
          rw [hnewFactorization]
    _ = newBaseLaw.map profileSplit.symm ⊗ₘ
        gaussianLocationKernel (newMean ∘ profileSplit)
          (hnewMean.comp profileSplit.measurable) newVariance.toNNReal := by
          exact gaussianLocationFactorization_map_measurableEquiv
            profileSplit.symm newBaseLaw newMean hnewMean newVariance.toNNReal

/-- The zero-coordinate base case for finite Gaussian-profile conditioning.
With no observed profile coordinates, the latent law is the original Gaussian
prior and the retained profile law is a point mass on the unique empty
profile. -/
theorem gaussianFiniteProfileLatentLaw_empty_exists_gaussianLocationFactorization
    (priorMean priorVariance : ℝ) (hpriorVariance : 0 < priorVariance) :
    ∃ (baseLaw : Measure (PEmpty → ℝ)) (mean : (PEmpty → ℝ) → ℝ)
        (variance : ℝ) (hmean : Measurable mean),
      IsProbabilityMeasure baseLaw ∧ 0 < variance ∧
        gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index : PEmpty => nomatch index) =
          baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal := by
  let emptyProfile : PEmpty → ℝ := fun index => nomatch index
  let prior : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
  have hprior : IsProbabilityMeasure prior := by
    dsimp [prior]
    infer_instance
  refine ⟨Measure.dirac emptyProfile, (fun _ => priorMean), priorVariance,
    measurable_const, Measure.dirac.isProbabilityMeasure, hpriorVariance, ?_⟩
  have hleft :
      gaussianFiniteProfileLatentLaw priorMean priorVariance
          (fun index : PEmpty => nomatch index) =
        (Measure.dirac emptyProfile).prod prior := by
    unfold gaussianFiniteProfileLatentLaw
    rw [Measure.pi_of_empty]
    rw [Measure.prod_dirac]
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rw [Measure.dirac_prod]
    congr 1
    funext skill
    apply Prod.ext
    · exact Subsingleton.elim _ _
    · rfl
  letI : IsMarkovKernel
      (gaussianLocationKernel (fun _ : PEmpty → ℝ => priorMean)
        measurable_const priorVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov (fun _ : PEmpty → ℝ => priorMean)
      measurable_const priorVariance.toNNReal
  rw [hleft]
  symm
  ext target htarget
  rw [Measure.compProd_apply htarget, lintegral_dirac,
    gaussianLocationKernel_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left htarget]

/-- Reindex an observed finite profile along an equivalence of its coordinate
types. -/
def gaussianFiniteProfileReindex
    {α β : Type*} [Fintype β] (e : α ≃ β) :
    (α → ℝ) ≃ᵐ (β → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : β => ℝ) e

/-- The finite Gaussian profile/latent source law is equivariant under a
coordinate reindexing.  This is the equivalence case of
`Fintype.induction_empty_option`. -/
theorem gaussianFiniteProfileLatentLaw_reindex
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (priorMean priorVariance : ℝ) (noiseVariance : β → ℝ) :
    (gaussianFiniteProfileLatentLaw priorMean priorVariance
        (fun index => noiseVariance (e index))).map
      (Prod.map (gaussianFiniteProfileReindex e) id) =
      gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance := by
  let prior : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
  let sourceNoise : Measure (α → ℝ) :=
    Measure.pi fun index => gaussianReal 0 (noiseVariance (e index)).toNNReal
  let targetNoise : Measure (β → ℝ) :=
    Measure.pi fun index => gaussianReal 0 (noiseVariance index).toNNReal
  let profileReindex : (α → ℝ) ≃ᵐ (β → ℝ) :=
    gaussianFiniteProfileReindex e
  let sourceObservation : ℝ × (α → ℝ) → (α → ℝ) × ℝ :=
    fun primitive =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1)
  let targetObservation : ℝ × (β → ℝ) → (β → ℝ) × ℝ :=
    fun primitive =>
      ((fun index => primitive.1 + primitive.2 index), primitive.1)
  have hsourceObservation : Measurable sourceObservation :=
    measurable_gaussianFiniteProfilePrimitiveMap
  have htargetObservation : Measurable targetObservation :=
    measurable_gaussianFiniteProfilePrimitiveMap
  have hprofileReindex : Measurable profileReindex := profileReindex.measurable
  letI : IsProbabilityMeasure prior := by
    dsimp [prior]
    infer_instance
  letI : IsProbabilityMeasure sourceNoise := by
    dsimp [sourceNoise]
    infer_instance
  have hnoise : sourceNoise.map profileReindex = targetNoise := by
    simpa [sourceNoise, targetNoise, profileReindex,
      gaussianFiniteProfileReindex] using
      (Measure.pi_map_piCongrLeft e
        (fun index : β => gaussianReal 0 (noiseVariance index).toNNReal))
  have hprimitive :
      (prior.prod sourceNoise).map (Prod.map id profileReindex) =
        prior.prod targetNoise := by
    rw [← Measure.map_prod_map prior sourceNoise measurable_id hprofileReindex]
    simpa [hnoise]
  dsimp [gaussianFiniteProfileLatentLaw]
  change ((prior.prod sourceNoise).map sourceObservation).map
      (Prod.map profileReindex id) =
    (prior.prod targetNoise).map targetObservation
  rw [Measure.map_map (by fun_prop) hsourceObservation]
  have hfun : (Prod.map profileReindex id) ∘ sourceObservation =
      targetObservation ∘ Prod.map id profileReindex := by
    funext primitive
    apply Prod.ext
    · apply funext
      intro index
      obtain ⟨sourceIndex, rfl⟩ := e.surjective index
      dsimp [profileReindex, gaussianFiniteProfileReindex,
        sourceObservation, targetObservation]
      rw [MeasurableEquiv.piCongrLeft_apply_apply,
        MeasurableEquiv.piCongrLeft_apply_apply]
    · rfl
  rw [hfun]
  rw [← Measure.map_map htargetObservation (by fun_prop)]
  rw [hprimitive]

/-- Every finite family of independent nondegenerate additive Gaussian
observations has an actual Gaussian conditional latent-skill kernel after the
entire observed profile.  The theorem deliberately records only the derived
measurable conditional mean and positive variance, not a pre-supplied
posterior formula.  It is proved by finite `Option` induction, with exact
source-law reindexing in the equivalence case. -/
theorem gaussianFiniteProfileLatentLaw_exists_gaussianLocationFactorization
    {Index : Type u} [Fintype Index]
    (priorMean priorVariance : ℝ) (hpriorVariance : 0 < priorVariance)
    (noiseVariance : Index → ℝ)
    (hnoiseVariance : ∀ index, 0 < noiseVariance index) :
    ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
        (variance : ℝ) (hmean : Measurable mean),
      IsProbabilityMeasure baseLaw ∧ 0 < variance ∧
        gaussianFiniteProfileLatentLaw priorMean priorVariance noiseVariance =
          baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal := by
  classical
  let P : ∀ (Index : Type u) [Fintype Index], Prop :=
    fun Index _ => ∀ (noise : Index → ℝ), (∀ index, 0 < noise index) →
      ∃ (baseLaw : Measure (Index → ℝ)) (mean : (Index → ℝ) → ℝ)
          (variance : ℝ) (hmean : Measurable mean),
        IsProbabilityMeasure baseLaw ∧ 0 < variance ∧
          gaussianFiniteProfileLatentLaw priorMean priorVariance noise =
            baseLaw ⊗ₘ gaussianLocationKernel mean hmean variance.toNNReal
  refine Fintype.induction_empty_option (P := P) ?_ ?_ ?_ Index
    noiseVariance hnoiseVariance
  · intro α β instβ e ih noise hnoise
    letI : Fintype α := Fintype.ofEquiv β e.symm
    let profileReindex : (α → ℝ) ≃ᵐ (β → ℝ) :=
      gaussianFiniteProfileReindex e
    have hsourceNoise : ∀ index : α, 0 < noise (e index) := by
      intro index
      exact hnoise (e index)
    rcases ih (fun index => noise (e index)) hsourceNoise with
      ⟨sourceBaseLaw, sourceMean, sourceVariance, hsourceMean,
        hsourceBaseLaw, hsourceVariance, hsourceFactorization⟩
    letI : IsProbabilityMeasure sourceBaseLaw := hsourceBaseLaw
    refine ⟨sourceBaseLaw.map profileReindex,
      sourceMean ∘ profileReindex.symm, sourceVariance,
      hsourceMean.comp profileReindex.symm.measurable,
      Measure.isProbabilityMeasure_map profileReindex.measurable.aemeasurable,
      hsourceVariance, ?_⟩
    calc
      gaussianFiniteProfileLatentLaw priorMean priorVariance noise =
          (gaussianFiniteProfileLatentLaw priorMean priorVariance
            (fun index => noise (e index))).map
              (Prod.map profileReindex id) := by
                simpa [profileReindex] using
                  (gaussianFiniteProfileLatentLaw_reindex
                    e priorMean priorVariance noise).symm
      _ = (sourceBaseLaw ⊗ₘ gaussianLocationKernel sourceMean
          hsourceMean sourceVariance.toNNReal).map
            (Prod.map profileReindex id) := by
              rw [hsourceFactorization]
      _ = sourceBaseLaw.map profileReindex ⊗ₘ
          gaussianLocationKernel (sourceMean ∘ profileReindex.symm)
            (hsourceMean.comp profileReindex.symm.measurable)
            sourceVariance.toNNReal := by
              exact gaussianLocationFactorization_map_measurableEquiv
                profileReindex sourceBaseLaw sourceMean hsourceMean
                sourceVariance.toNNReal
  · intro noise hnoise
    have hempty :=
      gaussianFiniteProfileLatentLaw_empty_exists_gaussianLocationFactorization
        priorMean priorVariance hpriorVariance
    simpa only [Subsingleton.elim noise (fun index : PEmpty => nomatch index)]
      using hempty
  · intro α instα ih noise hnoise
    exact gaussianFiniteProfileLatentLaw_option_exists_gaussianLocationFactorization
      priorMean priorVariance noise (hnoise none)
      (ih (fun index => noise (some index)) (fun index => hnoise (some index)))

end

end Probability
end AppliedModelingLib
