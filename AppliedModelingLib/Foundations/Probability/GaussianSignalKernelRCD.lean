import AppliedModelingLib.Foundations.Probability.GaussianSignalRCD

/-!
# Base-Indexed Gaussian Signal Conditional Distributions

This module supplies the kernel-level update step for a finite sequence of
independent additive Gaussian observations.  It derives the actual regular
conditional law of a latent Gaussian variable given an arbitrary base
coordinate and one further noisy score.  The theorem is source-neutral and
states its equality at the natural almost-everywhere scope.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace AppliedModelingLib
namespace Probability

noncomputable section

/-- A measurable family of Gaussians with fixed variance and varying mean. -/
def gaussianLocationKernel {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean) (variance : ℝ≥0) : Kernel α ℝ :=
  ((Kernel.deterministic mean hmean) ×ₖ
    Kernel.const α (gaussianReal 0 variance)).map
    (fun pair : ℝ × ℝ => pair.1 + pair.2)

theorem gaussianLocationKernel_apply {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean) (variance : ℝ≥0) (a : α) :
    gaussianLocationKernel mean hmean variance a = gaussianReal (mean a) variance := by
  unfold gaussianLocationKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    Kernel.deterministic_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (by fun_prop) measurable_prodMk_left]
  rw [show
      ((fun pair : ℝ × ℝ => pair.1 + pair.2) ∘ Prod.mk (mean a)) =
        (fun noise : ℝ => noise + mean a) by
          funext noise
          simp only [Function.comp_apply]
          ring]
  rw [gaussianReal_map_add_const]
  congr 1
  ring

theorem gaussianLocationKernel_isMarkov {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean) (variance : ℝ≥0) :
    IsMarkovKernel (gaussianLocationKernel mean hmean variance) := by
  letI : IsProbabilityMeasure (gaussianReal 0 variance) := by
    infer_instance
  unfold gaussianLocationKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Given a base-indexed Gaussian latent law, draw independent additive Gaussian noise and retain
the resulting score together with the latent coordinate. -/
def gaussianSignalJointKernel {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) : Kernel α (ℝ × ℝ) :=
  (gaussianLocationKernel mean hmean priorVariance.toNNReal ×ₖ
    Kernel.const α (gaussianReal 0 noiseVariance.toNNReal)).map
    (fun pair : ℝ × ℝ => (pair.1 + pair.2, pair.1))

/-- The score-indexed posterior kernel after a base-indexed Gaussian prior and one additive
Gaussian signal. -/
def gaussianSignalPosteriorBaseKernel {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) : Kernel (α × ℝ) ℝ :=
  gaussianLocationKernel
    (fun pair =>
      gaussianSignalWeight priorVariance noiseVariance * pair.2 +
        gaussianSignalPriorWeight priorVariance noiseVariance * mean pair.1)
    ((measurable_const.mul measurable_snd).add
      (measurable_const.mul (hmean.comp measurable_fst)))
    (gaussianSignalPosteriorVariance priorVariance noiseVariance)

theorem gaussianSignalJointKernel_apply {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) (a : α) :
    gaussianSignalJointKernel mean hmean priorVariance noiseVariance a =
      (gaussianSignalPair (mean a) priorVariance noiseVariance).map
        (fun pair : ℝ × ℝ => (pair.1 + pair.2, pair.1)) := by
  letI : IsMarkovKernel
      (gaussianLocationKernel mean hmean priorVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov mean hmean priorVariance.toNNReal
  letI : IsProbabilityMeasure (gaussianReal 0 noiseVariance.toNNReal) := by
    infer_instance
  unfold gaussianSignalJointKernel
  rw [Kernel.map_apply _ (by fun_prop), Kernel.prod_apply,
    gaussianLocationKernel_apply, Kernel.const_apply]

theorem gaussianSignalJointKernel_isMarkov {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) :
    IsMarkovKernel (gaussianSignalJointKernel mean hmean priorVariance noiseVariance) := by
  letI : IsMarkovKernel
      (gaussianLocationKernel mean hmean priorVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov mean hmean priorVariance.toNNReal
  letI : IsProbabilityMeasure (gaussianReal 0 noiseVariance.toNNReal) := by
    infer_instance
  unfold gaussianSignalJointKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem gaussianSignalPosteriorBaseKernel_apply {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) (a : α) (score : ℝ) :
    gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance (a, score) =
      gaussianReal
        (gaussianSignalWeight priorVariance noiseVariance * score +
          gaussianSignalPriorWeight priorVariance noiseVariance * mean a)
        (gaussianSignalPosteriorVariance priorVariance noiseVariance) := by
  unfold gaussianSignalPosteriorBaseKernel
  rw [gaussianLocationKernel_apply]

theorem gaussianSignalPosteriorBaseKernel_isMarkov {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) :
    IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance) := by
  unfold gaussianSignalPosteriorBaseKernel
  exact gaussianLocationKernel_isMarkov _ _ _

theorem gaussianSignalPosteriorBaseKernel_sectR {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) (a : α) :
    Kernel.sectR
      (gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance) a =
      gaussianSignalPosteriorKernel (mean a) priorVariance noiseVariance := by
  ext score
  rw [Kernel.sectR_apply, gaussianSignalPosteriorBaseKernel_apply,
    gaussianSignalPosteriorKernel_apply]

/-- A base-indexed lift of the one-signal Gaussian joint factorization. -/
theorem gaussianSignalJointKernel_factorization {α : Type*} [MeasurableSpace α]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    gaussianSignalJointKernel mean hmean priorVariance noiseVariance =
      gaussianLocationKernel mean hmean
        (priorVariance + noiseVariance).toNNReal ⊗ₖ
        gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance := by
  letI : IsMarkovKernel
      (gaussianLocationKernel mean hmean (priorVariance + noiseVariance).toNNReal) :=
    gaussianLocationKernel_isMarkov mean hmean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov mean hmean priorVariance noiseVariance
  ext a target htarget
  rw [Kernel.compProd_apply_eq_compProd_sectR,
    gaussianSignalJointKernel_apply,
    gaussianLocationKernel_apply,
    gaussianSignalPosteriorBaseKernel_sectR]
  exact congrArg (fun measure => measure target)
    (gaussianSignalPair_score_latent_joint_factorization
      (mean a) priorVariance noiseVariance hpriorVariance hnoiseVariance)

/-- The joint law of a base coordinate, its additive-Gaussian score, and its latent variable,
reassociated as `((base, score), latent)`. -/
def gaussianSignalBaseScoreLatentLaw {α : Type*} [MeasurableSpace α]
    (baseLaw : Measure α) (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ) : Measure ((α × ℝ) × ℝ) :=
  (baseLaw ⊗ₘ gaussianSignalJointKernel mean hmean priorVariance noiseVariance).map
    MeasurableEquiv.prodAssoc.symm

theorem gaussianSignalBaseScoreLatentLaw_factorization {α : Type*} [MeasurableSpace α]
    (baseLaw : Measure α) (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    gaussianSignalBaseScoreLatentLaw baseLaw mean hmean priorVariance noiseVariance =
      baseLaw ⊗ₘ gaussianLocationKernel mean hmean
        (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance := by
  unfold gaussianSignalBaseScoreLatentLaw
  rw [gaussianSignalJointKernel_factorization mean hmean priorVariance noiseVariance
    hpriorVariance hnoiseVariance]
  exact Measure.compProd_assoc

/-- The actual RCD update after one additive Gaussian signal, conditional on an arbitrary
base coordinate whose latent conditional law is Gaussian with measurable mean and constant positive
variance.  This is the sequential induction step for a finite family of independent Gaussian
observations. -/
theorem gaussianSignalBaseScoreLatent_condDistrib_latent_given_baseScore {α : Type*}
    [MeasurableSpace α] (baseLaw : Measure α) [IsProbabilityMeasure baseLaw]
    (mean : α → ℝ) (hmean : Measurable mean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance) :
    let law := gaussianSignalBaseScoreLatentLaw
      baseLaw mean hmean priorVariance noiseVariance
    letI : IsProbabilityMeasure law := by
      unfold law gaussianSignalBaseScoreLatentLaw
      letI : IsMarkovKernel
          (gaussianSignalJointKernel mean hmean priorVariance noiseVariance) :=
        gaussianSignalJointKernel_isMarkov mean hmean priorVariance noiseVariance
      have hassoc : Measurable
          (MeasurableEquiv.prodAssoc.symm : α × (ℝ × ℝ) → (α × ℝ) × ℝ) := by
        fun_prop
      exact Measure.isProbabilityMeasure_map hassoc.aemeasurable
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst law =ᵐ[law.map Prod.fst]
      gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance := by
  intro law
  letI : IsMarkovKernel
      (gaussianSignalJointKernel mean hmean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov mean hmean priorVariance noiseVariance
  letI : IsProbabilityMeasure law := by
    unfold law gaussianSignalBaseScoreLatentLaw
    have hassoc : Measurable
        (MeasurableEquiv.prodAssoc.symm : α × (ℝ × ℝ) → (α × ℝ) × ℝ) := by
      fun_prop
    exact Measure.isProbabilityMeasure_map hassoc.aemeasurable
  letI : IsFiniteMeasure law := ⟨by simp⟩
  let scoreKernel : Kernel α ℝ :=
    gaussianLocationKernel mean hmean (priorVariance + noiseVariance).toNNReal
  let posteriorKernel : Kernel (α × ℝ) ℝ :=
    gaussianSignalPosteriorBaseKernel mean hmean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov mean hmean (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov mean hmean priorVariance noiseVariance
  have hfactor : law = baseLaw ⊗ₘ scoreKernel ⊗ₘ posteriorKernel := by
    exact gaussianSignalBaseScoreLatentLaw_factorization
      baseLaw mean hmean priorVariance noiseVariance hpriorVariance hnoiseVariance
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

end

end Probability
end AppliedModelingLib
