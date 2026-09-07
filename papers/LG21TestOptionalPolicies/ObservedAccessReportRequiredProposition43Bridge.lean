import LG21TestOptionalPolicies.ObservedAccessReportRequiredD6OutputBridge
import LG21TestOptionalPolicies.ObservedAccessProposition43FairnessBridge

/-!
# Report-required literal Proposition 4.3 bridge for LG21

This endpoint instantiates the semantic Proposition 4.3 calculation with the
literal report-required carrier.  The access output is obtained from the
attained reporter PBO only after the positive-mass stability argument proves
that taking (and hence reporting) occurs almost everywhere.  The no-access
output is constrained only by its own conditional-mean PBO semantics.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the literal observed-access report-required protocol, the actual
PBO output differs from the actual no-access PBO both conditionally on almost
every public base profile and in its population output law.  The displayed
Gaussian factorization and posterior-mean law are derived from the source
population.  In particular, this endpoint does not assume that the no-access
output already equals a supplied base-mean function. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_actualPBO_not_observableOrDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (htestLaw : ∀ latentSkill publicBase,
      E.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
    ∀ (source : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) E),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (source.base_measurable.prodMk
          (source.score_measurable.prodMk source.skill_measurable))
        (fun latentSkill publicBase => E.takeDecision latentSkill publicBase) →
    ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
        (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (baseVariance baseMeanVariance : ℝ)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseMean : Measurable baseMean)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
          baseLaw ⊗ₘ gaussianLocationKernel
            baseMean hbaseMean baseVariance.toNNReal ∧
        0 ≤ baseMeanVariance ∧
        ((∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) E)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) E) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput)) := by
  intro source hstable
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hbaseMeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  have haccessOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E htestLaw baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization source hstable
  simpa using
    (lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      noAccessOutput haccessOutput hnoAccessPBO)

end

end LG21TestOptionalPolicies
