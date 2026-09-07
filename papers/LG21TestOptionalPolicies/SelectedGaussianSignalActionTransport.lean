import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge
import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge
import AppliedModelingLib.Foundations.Probability.FiniteGaussianSignalKernelRCD

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open AppliedModelingLib Probability
open scoped ENNReal ProbabilityTheory

/--
The event in an extended base/score/skill record induced by a latent
base/skill action event.  It depends on the retained base and latent skill,
not on the independently drawn score noise.
-/
def gaussianSignalExtendedSelectionEvent
    {Base : Type*} [MeasurableSpace Base]
    (selected : Set (Base × ℝ)) : Set ((Base × ℝ) × ℝ) :=
  {observationSkill | (observationSkill.1.1, observationSkill.2) ∈ selected}

/--
Normalizing an action-selected latent population before adding independent
Gaussian score noise gives exactly the same extended law as selecting the
extended score/skill population by that action.  This is an equality of
measures; it introduces no conditional value on a zero-mass action branch.
-/
theorem normalizedRestriction_gaussianSignalExtendBaseLatentLaw
    {Base : Type*} [MeasurableSpace Base]
    (baseSkillLaw : Measure (Base × ℝ)) [IsProbabilityMeasure baseSkillLaw]
    (noiseVariance : ℝ) (selected : Set (Base × ℝ))
    (hselected : MeasurableSet selected) :
    lg21NormalizedRestriction
      (gaussianSignalExtendBaseLatentLaw baseSkillLaw noiseVariance)
      (gaussianSignalExtendedSelectionEvent selected) =
      gaussianSignalExtendBaseLatentLaw
        (lg21NormalizedRestriction baseSkillLaw selected) noiseVariance := by
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let repackage : ((Base × ℝ) × ℝ) -> ((Base × ℝ) × ℝ) :=
    fun primitive => ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
  let extendedEvent : Set ((Base × ℝ) × ℝ) :=
    gaussianSignalExtendedSelectionEvent selected
  have hnoise : IsProbabilityMeasure noiseLaw := by
    dsimp [noiseLaw]
    infer_instance
  letI : IsProbabilityMeasure noiseLaw := hnoise
  have hrepackage : Measurable repackage := by
    dsimp [repackage]
    fun_prop
  have hextendedEvent : MeasurableSet extendedEvent := by
    change MeasurableSet
      ((fun observationSkill : (Base × ℝ) × ℝ =>
        (observationSkill.1.1, observationSkill.2)) ⁻¹' selected)
    exact hselected.preimage (by fun_prop)
  have hpreimage : repackage ⁻¹' extendedEvent = selected ×ˢ Set.univ := by
    ext primitive
    simp [repackage, extendedEvent, gaussianSignalExtendedSelectionEvent]
  letI : SFinite (lg21NormalizedRestriction baseSkillLaw selected) := by
    unfold lg21NormalizedRestriction
    infer_instance
  change lg21NormalizedRestriction
      ((baseSkillLaw.prod noiseLaw).map repackage) extendedEvent =
    ((lg21NormalizedRestriction baseSkillLaw selected).prod noiseLaw).map repackage
  rw [← lg21_normalizedRestriction_map_preimage
    (baseSkillLaw.prod noiseLaw) repackage hrepackage extendedEvent hextendedEvent]
  rw [hpreimage]
  rw [← Measure.compProd_const]
  rw [lg21_normalizedRestriction_compProd_left baseSkillLaw
    (Kernel.const (Base × ℝ) noiseLaw) selected hselected]
  rw [Measure.compProd_const]

/-- Draw independent Gaussian score noise after a base-indexed latent kernel,
retaining the resulting score and latent skill. -/
def gaussianSignalJointKernelOfLatentKernel
    {Base : Type*} [MeasurableSpace Base]
    (latentKernel : Kernel Base ℝ) (noiseVariance : ℝ) : Kernel Base (ℝ × ℝ) :=
  (latentKernel ×ₖ Kernel.const Base
    (gaussianReal 0 noiseVariance.toNNReal)).map
    (fun skillNoise : ℝ × ℝ => (skillNoise.1 + skillNoise.2, skillNoise.1))

theorem gaussianSignalJointKernelOfLatentKernel_isMarkov
    {Base : Type*} [MeasurableSpace Base]
    (latentKernel : Kernel Base ℝ) [IsMarkovKernel latentKernel]
    (noiseVariance : ℝ) :
    IsMarkovKernel
      (gaussianSignalJointKernelOfLatentKernel latentKernel noiseVariance) := by
  unfold gaussianSignalJointKernelOfLatentKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- Extending a base/skill composition-product law by independent Gaussian
noise factors through the corresponding score/skill kernel. -/
theorem gaussianSignalExtendBaseLatentLaw_compProd
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (latentKernel : Kernel Base ℝ) [IsMarkovKernel latentKernel]
    (noiseVariance : ℝ) :
    gaussianSignalExtendBaseLatentLaw (baseLaw ⊗ₘ latentKernel) noiseVariance =
      (baseLaw ⊗ₘ gaussianSignalJointKernelOfLatentKernel
        latentKernel noiseVariance).map MeasurableEquiv.prodAssoc.symm := by
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let follow : (Base × ℝ) × ℝ → (Base × ℝ) × ℝ :=
    fun primitive => ((primitive.1.1, primitive.1.2 + primitive.2), primitive.1.2)
  let stage : ℝ × ℝ → ℝ × ℝ :=
    fun pair => (pair.1 + pair.2, pair.1)
  have hfollow : Measurable follow := by
    dsimp [follow]
    fun_prop
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  letI : IsProbabilityMeasure noiseLaw := by
    dsimp [noiseLaw]
    infer_instance
  change ((baseLaw ⊗ₘ latentKernel).prod noiseLaw).map follow =
    (baseLaw ⊗ₘ (latentKernel ×ₖ Kernel.const Base noiseLaw).map stage).map
      MeasurableEquiv.prodAssoc.symm
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
      latentKernel ⊗ₖ Kernel.const (Base × ℝ) noiseLaw =
        latentKernel ×ₖ Kernel.const Base noiseLaw := by
    ext base target htarget
    rw [Kernel.compProd_apply htarget, Kernel.prod_apply,
      Measure.prod_apply htarget]
    simp only [Kernel.const_apply]
  rw [hkernel]

/-- The score/skill law obtained by selecting a Gaussian latent set before
independent additive noise is the normalized restriction of the explicit
unselected Gaussian score/posterior joint law. -/
theorem normalizedRestriction_gaussianSignal_scoreLatent
    (priorMean priorVariance noiseVariance : ℝ) (selected : Set ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hselected : MeasurableSet selected) :
    lg21NormalizedRestriction
      (gaussianReal priorMean (priorVariance + noiseVariance).toNNReal ⊗ₘ
        gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance)
      (Set.univ ×ˢ selected) =
      ((lg21NormalizedRestriction
        (gaussianReal priorMean priorVariance.toNNReal) selected).prod
          (gaussianReal 0 noiseVariance.toNNReal)).map
        (fun skillNoise : ℝ × ℝ => (skillNoise.1 + skillNoise.2, skillNoise.1)) := by
  let priorLaw : Measure ℝ := gaussianReal priorMean priorVariance.toNNReal
  let noiseLaw : Measure ℝ := gaussianReal 0 noiseVariance.toNNReal
  let scoreLaw : Measure ℝ :=
    gaussianReal priorMean (priorVariance + noiseVariance).toNNReal
  let posterior : Kernel ℝ ℝ :=
    gaussianSignalPosteriorKernel priorMean priorVariance noiseVariance
  let event : Set (ℝ × ℝ) := Set.univ ×ˢ selected
  let stage : ℝ × ℝ → ℝ × ℝ :=
    fun skillNoise => (skillNoise.1 + skillNoise.2, skillNoise.1)
  letI : IsProbabilityMeasure priorLaw := by
    dsimp [priorLaw]
    infer_instance
  letI : IsProbabilityMeasure noiseLaw := by
    dsimp [noiseLaw]
    infer_instance
  letI : IsMarkovKernel posterior :=
    lg21_gaussianSignalPosteriorKernel_isMarkov
      priorMean priorVariance noiseVariance
  have hstage : Measurable stage := by
    dsimp [stage]
    fun_prop
  have hevent : MeasurableSet event :=
    MeasurableSet.univ.prod hselected
  have hpreimage : stage ⁻¹' event = selected ×ˢ Set.univ := by
    ext skillNoise
    simp [stage, event]
  have hraw : (priorLaw.prod noiseLaw).map stage = scoreLaw ⊗ₘ posterior := by
    dsimp [priorLaw, noiseLaw, scoreLaw, posterior, stage]
    exact gaussianSignalPair_score_latent_joint_factorization
      priorMean priorVariance noiseVariance hpriorVariance hnoiseVariance
  letI : SFinite (lg21NormalizedRestriction priorLaw selected) := by
    unfold lg21NormalizedRestriction
    infer_instance
  calc
    lg21NormalizedRestriction (scoreLaw ⊗ₘ posterior) event =
        lg21NormalizedRestriction ((priorLaw.prod noiseLaw).map stage) event := by
          rw [hraw]
    _ = (lg21NormalizedRestriction (priorLaw.prod noiseLaw)
          (stage ⁻¹' event)).map stage := by
          symm
          exact lg21_normalizedRestriction_map_preimage
            (priorLaw.prod noiseLaw) stage hstage event hevent
    _ = (lg21NormalizedRestriction (priorLaw.prod noiseLaw)
          (selected ×ˢ Set.univ)).map stage := by rw [hpreimage]
    _ = ((lg21NormalizedRestriction priorLaw selected).prod noiseLaw).map stage := by
          rw [← Measure.compProd_const]
          rw [lg21_normalizedRestriction_compProd_left priorLaw
            (Kernel.const ℝ noiseLaw) selected hselected]
          rw [Measure.compProd_const]

end

end LG21TestOptionalPolicies
