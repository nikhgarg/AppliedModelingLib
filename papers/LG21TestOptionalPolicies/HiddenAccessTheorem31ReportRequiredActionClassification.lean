import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralSource
import LG21TestOptionalPolicies.ReportRequiredBaseDependentTailSourceBridge
import LG21TestOptionalPolicies.SemanticActionCutoff
import LG21TestOptionalPolicies.SelectedGaussianSourcePosterior
import LG21TestOptionalPolicies.SelectedGaussianSignalPosteriorBridge
import LG21TestOptionalPolicies.SelectedGaussianSourceActionFactor
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterPBOBridge

/-!
# Literal source/Fubini action classification for LG21 Theorem 3.1

This module begins with the report-required literal source carrier rather than
an abstract sequential-equilibrium adapter.  Its first bridge is purely
measure-theoretic: it disintegrates the a.e. pre-score best response over the
actual public-base source law.  It does not assume a cutoff, an affine payoff,
or an off-path posterior.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal best response on public-base fibres -/

/--
The literal report-required take best response holds on almost every
public-base/latent-skill fibre whenever the actual access population has the
displayed base--skill factorization.  The factorization is deliberately in
`(base, skill)` order; the source carrier uses `(skill, base)`, so the proof
uses the measurable coordinate swap before applying Fubini.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.take_best_response_ae_by_base_of_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    (skillKernel : Kernel (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    [SFinite baseLaw] [IsSFiniteKernel skillKernel]
    (hfactor :
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap =
        baseLaw ⊗ₘ skillKernel) :
    ∀ᵐ publicBase ∂baseLaw,
      NoProfitableBinaryChoiceDeviationAE (skillKernel publicBase)
        (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
        (fun latentSkill => ∫ score,
          E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase)
        (fun _ => E.source.noReportPayoff publicBase) := by
  let accessLaw := lg21HiddenAccessAccessLatentBaseLaw M testFeature
  let takePayoff : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun profile => ∫ score,
      E.source.reportedPayoff profile.2 score ∂E.source.testLaw profile.1 profile.2
  let noTakePayoff : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun profile => E.source.noReportPayoff profile.2
  have hbest : NoProfitableBinaryChoiceDeviationAE accessLaw
      (fun profile => E.source.takeDecision profile.1 profile.2 = true)
      takePayoff noTakePayoff := by
    simpa [accessLaw, takePayoff, noTakePayoff] using E.take_best_response_ae
  have hswapSwap : (accessLaw.map Prod.swap).map Prod.swap = accessLaw := by
    rw [Measure.map_map measurable_swap measurable_swap]
    simpa only [Function.comp_apply, Prod.swap_prod_mk] using
      (Measure.map_id (μ := accessLaw))
  have hchosenMapMap : ∀ᵐ profile ∂(accessLaw.map Prod.swap).map Prod.swap,
      E.source.takeDecision profile.1 profile.2 = true ->
        noTakePayoff profile ≤ takePayoff profile := by
    rw [hswapSwap]
    exact hbest.1
  have hunchosenMapMap : ∀ᵐ profile ∂(accessLaw.map Prod.swap).map Prod.swap,
      E.source.takeDecision profile.1 profile.2 ≠ true ->
        takePayoff profile ≤ noTakePayoff profile := by
    rw [hswapSwap]
    exact hbest.2
  have hchosenSwap : ∀ᵐ profile ∂accessLaw.map Prod.swap,
      E.source.takeDecision profile.2 profile.1 = true ->
        noTakePayoff (Prod.swap profile) ≤ takePayoff (Prod.swap profile) := by
    exact ae_of_ae_map measurable_swap.aemeasurable hchosenMapMap
  have hunchosenSwap : ∀ᵐ profile ∂accessLaw.map Prod.swap,
      E.source.takeDecision profile.2 profile.1 ≠ true ->
        takePayoff (Prod.swap profile) ≤ noTakePayoff (Prod.swap profile) := by
    exact ae_of_ae_map measurable_swap.aemeasurable hunchosenMapMap
  rw [hfactor] at hchosenSwap hunchosenSwap
  have hchosenFibres := Measure.ae_ae_of_ae_compProd hchosenSwap
  have hunchosenFibres := Measure.ae_ae_of_ae_compProd hunchosenSwap
  filter_upwards [hchosenFibres, hunchosenFibres] with publicBase
    hchosen hunchosen
  constructor
  · simpa [takePayoff, noTakePayoff] using hchosen
  · simpa [takePayoff, noTakePayoff] using hunchosen

/-! ## Gaussian source specialization -/

/--
For the literal positive-access population, swapping the source's
`(latentSkill, publicBase)` input law gives the same base--skill marginal as
the full raw Gaussian population.  Forgetting score in the supplied full
source factorization therefore gives the factorization consumed by the
Fubini bridge above.
-/
theorem lg21HiddenAccessAccessLatentBaseLaw_swap_eq_gaussianLocation_of_scoreFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        baseVariance.toNNReal := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let latentBase : Bool × (ℝ × (Feature -> ℝ)) ->
      ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21HiddenAccessStudentBase testFeature student.2)
  have hlatentBase : Measurable latentBase := by
    simpa [latentBase] using
      (lg21HiddenAccessLatentBaseObservation_measurable testFeature)
  calc
    (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap =
        (accessLaw.map latentBase).map Prod.swap := by rfl
    _ = accessLaw.map (lg21HiddenAccessBaseSkillObservation testFeature) := by
      rw [Measure.map_map measurable_swap hlatentBase]
      rfl
    _ = lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature := by
      simpa [accessLaw] using
        (lg21ContinuousGaussianAccessPopulation_base_skill_law
          M haccess testFeature)
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by
      exact
        lg21ReportRequiredBaseDependentTail_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
          M haccess testFeature baseLaw baseMean hbaseMean baseVariance
          noiseVariance hsourceFactor

/--
Specialization of the clean law-only posterior disintegration to the literal
forced-report source carrier.  The selected set is the actual measurable
taking action; it is not a latent label observed by the school.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.taker_condDistrib_eq_selectedGaussianPosterior_ae_of_factorization
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance) (hnoiseVariance : 0 < noiseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance noiseVariance)
    (htakePositive : 0 < lg21ContinuousGaussianAccessPopulationLaw M
      {student | E.source.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}) :
    let posteriorKernel := gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance
    letI : IsMarkovKernel posteriorKernel :=
      gaussianSignalPosteriorBaseKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    let takeEvent : Set
        (((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) × ℝ) :=
      {observationSkill |
        E.source.takeDecision observationSkill.2 observationSkill.1.1 = true}
    let takerLaw := lg21NormalizedRestriction
      (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | E.source.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
    letI : IsProbabilityMeasure takerLaw :=
      lg21NormalizedRestriction_isProbability
        (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | E.source.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true}
        (ne_of_gt htakePositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
    ∀ᵐ student ∂takerLaw,
      condDistrib lg21ContinuousPopulationSkill
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            lg21HiddenAccessStudentScore testFeature student.2))
        takerLaw
        (lg21HiddenAccessStudentBase testFeature student.2,
          lg21HiddenAccessStudentScore testFeature student.2) =
        selectedNormalizedKernel posteriorKernel takeEvent
          (lg21HiddenAccessStudentBase testFeature student.2,
            lg21HiddenAccessStudentScore testFeature student.2) := by
  intro posteriorKernel takeEvent takerLaw
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.source.access_positive
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability
      (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | E.source.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
      (ne_of_gt htakePositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  exact
    lg21_source_taker_condDistrib_eq_selectedGaussianPosterior_ae_lawOnly
      (sourceLaw := lg21ContinuousGaussianAccessPopulationLaw M)
      (base := fun student => lg21HiddenAccessStudentBase testFeature student.2)
      (score := fun student => lg21HiddenAccessStudentScore testFeature student.2)
      (skill := lg21ContinuousPopulationSkill)
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
      ((lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd)
      (measurable_fst.comp measurable_snd)
      baseLaw baseMean hbaseMean priorVariance noiseVariance
      hpriorVariance hnoiseVariance hsourceFactor
      (fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase)
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst)) htakePositive

/--
The selected-posterior expected payoff is strictly increasing in latent skill
once the literal reporter payoff has been identified on its attained selected
score law.  This is a direct specialization of the selected-Gaussian
calculation to the forced-report literal carrier, not an affine-PBO premise.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.takeExpectedPayoff_strictMono_of_selectedGaussianPBO_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (priorMean priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (selected : Set ℝ) (hselectedMeasurable : MeasurableSet selected)
    (hselected : 0 < gaussianReal priorMean priorVariance.toNNReal selected)
    (hreportedPBO : E.source.reportedPayoff publicBase =ᵐ[
      normalizedSelectedBase
        (gaussianReal priorMean
          (priorVariance + (M.noiseVariance testFeature : ℝ)).toNNReal)
        (gaussianSignalPosteriorKernel priorMean priorVariance
          (M.noiseVariance testFeature : ℝ))
        (Set.univ ×ˢ selected)]
      fun score => ∫ latentSkill, latentSkill ∂lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel priorMean priorVariance
          (M.noiseVariance testFeature : ℝ) score)
        selected) :
    StrictMono (fun latentSkill => ∫ score,
      E.source.reportedPayoff publicBase score
        ∂E.source.testLaw latentSkill publicBase) := by
  have hintegrable : ∀ latentSkill,
      Integrable (E.source.reportedPayoff publicBase)
        (gaussianReal latentSkill
          (M.noiseVariance testFeature : ℝ).toNNReal) := by
    intro latentSkill
    have hsource := E.source.continuationPayoff_integrable latentSkill publicBase
    have hreported : Integrable (E.source.reportedPayoff publicBase)
        (E.source.testLaw latentSkill publicBase) := by
      simpa only [E.reportDecision_eq_true, if_true] using hsource
    rw [E.source.raw_test_law latentSkill publicBase] at hreported
    simpa using hreported
  have hstrict := lg21_selectedGaussianSignal_expectedPBO_strictMono_of_ae
    priorMean priorVariance (M.noiseVariance testFeature : ℝ) selected
    hpriorVariance hnoiseVariance hselectedMeasurable hselected
    (E.source.reportedPayoff publicBase) hreportedPBO hintegrable
  intro lowSkill highSkill hlowHigh
  change (∫ score, E.source.reportedPayoff publicBase score
      ∂E.source.testLaw lowSkill publicBase) <
    ∫ score, E.source.reportedPayoff publicBase score
      ∂E.source.testLaw highSkill publicBase
  rw [E.source.raw_test_law lowSkill publicBase,
    E.source.raw_test_law highSkill publicBase]
  simpa using hstrict hlowHigh

/--
Direct source form of the literal fibrewise taking best response.  Every
premise is either a field of the report-required literal source carrier or an
equality of the actual Gaussian source law; no generic equilibrium adapter or
fibre best-response hypothesis is introduced.
-/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.take_best_response_ae_by_base_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    ∀ᵐ publicBase ∂baseLaw,
      NoProfitableBinaryChoiceDeviationAE
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal publicBase)
        (fun latentSkill => E.source.takeDecision latentSkill publicBase = true)
        (fun latentSkill => ∫ score,
          E.source.reportedPayoff publicBase score
            ∂E.source.testLaw latentSkill publicBase)
        (fun _ => E.source.noReportPayoff publicBase) := by
  let skillKernel := gaussianLocationKernel
    baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel skillKernel := by
    simpa [skillKernel] using
      (gaussianLocationKernel_isMarkov
        baseMean hbaseMean baseVariance.toNNReal)
  apply E.take_best_response_ae_by_base_of_factorization baseLaw skillKernel
  simpa [skillKernel] using
    (lg21HiddenAccessAccessLatentBaseLaw_swap_eq_gaussianLocation_of_scoreFactor
      M E.source.access_positive testFeature baseLaw baseMean hbaseMean
      baseVariance noiseVariance hsourceFactor)

end

end LG21TestOptionalPolicies
