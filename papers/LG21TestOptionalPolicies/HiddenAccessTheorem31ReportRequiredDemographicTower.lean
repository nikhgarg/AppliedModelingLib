import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredOutputIntegrability

/-!
# Primitive-output towers for report-required LG21 Theorem 3.1

These are literal source-population transports.  They turn the source PBO's
primitive output integrability into the base/score/skill towers induced by the
Gaussian source factorization; no tower or integrability fact is supplied by a
caller.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The mean actual access output on the literal primitive population is the
base-indexed Gaussian score/skill tower from the source factorization. -/
theorem lg21HiddenAccessReportRequired_primitiveAccessOutput_integral_eq_sourceGaussianTower_of_sourceFactor
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
    (∫ primitive, lg21HiddenAccessReportRequiredPrimitiveAccessOutput E primitive
      ∂lg21ContinuousGaussianStudentPrimitiveLaw M) =
      ∫ publicBase, ∫ scoreSkill : ℝ × ℝ,
        lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
          scoreSkill.1
        ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) publicBase
      ∂baseLaw := by
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let observation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let output : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun profile =>
      lg21HiddenAccessReportRequiredSourceOutput E profile.2.2 profile.1
        profile.2.1
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
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
  have hfactor : primitiveLaw.map observation = baseLaw ⊗ₘ joint := by
    simpa [primitiveLaw, observation, joint] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance hsourceFactor)
  letI : IsMarkovKernel joint :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  calc
    (∫ primitive, lg21HiddenAccessReportRequiredPrimitiveAccessOutput E primitive
      ∂lg21ContinuousGaussianStudentPrimitiveLaw M) =
        ∫ profile, output profile ∂primitiveLaw.map observation := by
          symm
          simpa only [hcompose] using
            (integral_map_of_stronglyMeasurable hobservation
              houtput.stronglyMeasurable)
    _ = ∫ profile, output profile ∂baseLaw ⊗ₘ joint := by rw [hfactor]
    _ = ∫ publicBase, ∫ scoreSkill, output (publicBase, scoreSkill)
        ∂joint publicBase ∂baseLaw :=
      Measure.integral_compProd (by simpa [hfactor] using hmapIntegrable)
    _ = ∫ publicBase, ∫ scoreSkill : ℝ × ℝ,
        lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
          scoreSkill.1
        ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ) publicBase
      ∂baseLaw := by
      rfl

/-- The mean actual no-access output on the literal primitive population is
the base-law mean of the source no-report payoff. -/
theorem lg21HiddenAccessReportRequired_primitiveNoAccessOutput_integral_eq_baseLaw_of_sourceFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    (∫ primitive, lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E primitive
      ∂lg21ContinuousGaussianStudentPrimitiveLaw M) =
      ∫ publicBase, E.source.noReportPayoff publicBase ∂baseLaw := by
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let observation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let output : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun profile => E.source.noReportPayoff profile.1
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
  have hobservation : Measurable observation := by
    simpa [observation] using
      lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
        (Feature := Feature) testFeature
  have houtput : Measurable output := by
    exact E.source.noReportPayoff_measurable.comp measurable_fst
  have hcompose : output ∘ observation =
      lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E := by
    funext primitive
    rfl
  have hmapIntegrable : Integrable output (primitiveLaw.map observation) := by
    rw [integrable_map_measure houtput.aestronglyMeasurable
      hobservation.aemeasurable]
    simpa [hcompose] using E.primitiveNoAccessOutput_integrable hnoAccess
  have hfactor : primitiveLaw.map observation = baseLaw ⊗ₘ joint := by
    simpa [primitiveLaw, observation, joint] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance hsourceFactor)
  letI : IsMarkovKernel joint :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  calc
    (∫ primitive, lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E primitive
      ∂lg21ContinuousGaussianStudentPrimitiveLaw M) =
        ∫ profile, output profile ∂primitiveLaw.map observation := by
          symm
          simpa only [hcompose] using
            (integral_map_of_stronglyMeasurable hobservation
              houtput.stronglyMeasurable)
    _ = ∫ profile, output profile ∂baseLaw ⊗ₘ joint := by rw [hfactor]
    _ = ∫ publicBase, ∫ scoreSkill, output (publicBase, scoreSkill)
        ∂joint publicBase ∂baseLaw :=
      Measure.integral_compProd (by simpa [hfactor] using hmapIntegrable)
    _ = ∫ publicBase, E.source.noReportPayoff publicBase ∂baseLaw := by
      apply integral_congr_ae
      filter_upwards with publicBase
      letI : IsProbabilityMeasure (joint publicBase) :=
        IsMarkovKernel.isProbabilityMeasure publicBase
      simp [output]

/-- The literal source PBO also makes the base-indexed expected actual output
integrable.  This is obtained by transporting primitive access-output
integrability through the source factorization and applying Fubini; it is not
an additional regularity premise on a final fairness theorem. -/
theorem lg21HiddenAccessReportRequired_observableOutputIntegral_integrable_of_sourceGaussianFactor
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
    Integrable (fun publicBase => ∫ scoreSkill : ℝ × ℝ,
      lg21HiddenAccessReportRequiredSourceOutput E scoreSkill.2 publicBase
        scoreSkill.1
      ∂gaussianSignalJointKernel baseMean hbaseMean baseVariance
        (M.noiseVariance testFeature : ℝ) publicBase) baseLaw := by
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let observation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let output : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun profile =>
      lg21HiddenAccessReportRequiredSourceOutput E profile.2.2 profile.1
        profile.2.1
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
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
  have hfactor : primitiveLaw.map observation = baseLaw ⊗ₘ joint := by
    simpa [primitiveLaw, observation, joint] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance hsourceFactor)
  letI : IsMarkovKernel joint :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  rw [hfactor] at hmapIntegrable
  simpa [output, joint] using hmapIntegrable.integral_compProd

/-- The same literal transport yields integrability of the base-only
no-report output.  The no-access mass is needed solely for the source's
conditioned no-access output carrier. -/
theorem lg21HiddenAccessReportRequired_noReportPayoff_integrable_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    Integrable E.source.noReportPayoff baseLaw := by
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let observation :=
    lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation testFeature
  let output : (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun profile => E.source.noReportPayoff profile.1
  let joint := gaussianSignalJointKernel baseMean hbaseMean baseVariance
    (M.noiseVariance testFeature : ℝ)
  have hobservation : Measurable observation := by
    simpa [observation] using
      lg21HiddenAccessOptionalPrimitiveBaseScoreSkillObservation_measurable
        (Feature := Feature) testFeature
  have houtput : Measurable output := by
    exact E.source.noReportPayoff_measurable.comp measurable_fst
  have hcompose : output ∘ observation =
      lg21HiddenAccessReportRequiredPrimitiveNoAccessOutput E := by
    funext primitive
    rfl
  have hmapIntegrable : Integrable output (primitiveLaw.map observation) := by
    rw [integrable_map_measure houtput.aestronglyMeasurable
      hobservation.aemeasurable]
    simpa [hcompose] using E.primitiveNoAccessOutput_integrable hnoAccess
  have hfactor : primitiveLaw.map observation = baseLaw ⊗ₘ joint := by
    simpa [primitiveLaw, observation, joint] using
      (lg21HiddenAccessOptional_primitiveBaseScoreSkill_factorization_of_sourceFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance hsourceFactor)
  letI : IsMarkovKernel joint :=
    gaussianSignalJointKernel_isMarkov baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ)
  rw [hfactor] at hmapIntegrable
  have hintegral : Integrable (fun publicBase => ∫ scoreSkill,
      output (publicBase, scoreSkill) ∂joint publicBase) baseLaw :=
    hmapIntegrable.integral_compProd
  have heq : (fun publicBase => ∫ scoreSkill,
      output (publicBase, scoreSkill) ∂joint publicBase) =
      E.source.noReportPayoff := by
    funext publicBase
    letI : IsProbabilityMeasure (joint publicBase) :=
      IsMarkovKernel.isProbabilityMeasure publicBase
    simp [output]
  rw [heq] at hintegral
  exact hintegral

end

end LG21TestOptionalPolicies
