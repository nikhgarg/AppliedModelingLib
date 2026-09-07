import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralOutputLawBridge

/-!
# Fibrewise output integrability for report-required LG21 Theorem 3.1

The source PBO makes literal primitive access output integrable. This module
transports that fact through the literal base/score/skill factorization and
disintegrates it over the public base. No output integrability is added as an
equilibrium assumption.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/--
The literal source PBO gives fibrewise integrability of report-required actual
output for almost every public base under its Gaussian source factorization.
-/
theorem lg21HiddenAccessReportRequired_observableOutput_integrable_ae_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    ∀ᵐ publicBase ∂baseLaw,
      Integrable (fun scoreSkill : ℝ × ℝ =>
        lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
          scoreSkill.1)
        (gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) publicBase) := by
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let observation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let output : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun profile =>
      lg21HiddenAccessReportRequiredSourceOutput E profile.2.2 profile.1
        profile.2.1
  have hobservation : Measurable observation := by
    simpa [observation] using
      lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
        (Feature := Feature) testFeature
  have houtput : Measurable output := by
    unfold output
    apply Measurable.ite
      ((measurableSet_singleton true).preimage
        (E.source.takeDecision_measurable.comp
          ((measurable_snd.comp measurable_snd).prodMk measurable_fst)))
    · exact E.source.reportedPayoff_measurable.comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    · exact E.source.noReportPayoff_measurable.comp measurable_fst
  have hcompose : output ∘ observation =
      lg21HiddenAccessReportRequiredPrimitiveAccessOutput E := by
    funext primitive
    rfl
  have hmapIntegrable : Integrable output (primitiveLaw.map observation) := by
    rw [integrable_map_measure houtput.aestronglyMeasurable
      hobservation.aemeasurable]
    simpa [hcompose] using E.primitiveAccessOutput_integrable
  have hfactor : primitiveLaw.map observation =
      baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    simpa [primitiveLaw, observation] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance hsourceFactor)
  rw [hfactor] at hmapIntegrable
  letI : IsMarkovKernel (gaussianSignalJointKernel baseMean hbaseMean
      baseVariance (M.noiseVariance testFeature : ℝ)) :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  exact (Measure.integrable_compProd_iff houtput.aestronglyMeasurable).mp
    hmapIntegrable |>.1

end

end LG21TestOptionalPolicies
