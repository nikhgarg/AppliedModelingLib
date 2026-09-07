import LG21TestOptionalPolicies.ObservedAccessConditionalOutputKernel
import LG21TestOptionalPolicies.ObservedAccessReportRequiredD6OutputBridge

/-!
# Report-required literal Theorem 4.4 endpoint for LG21

This module isolates the report-required observed-access protocol.  It first
uses the literal positive-mass stability carrier to identify the realized
school output with the Definition 6 estimator almost everywhere, then applies
the common conditional-output transport.  No mandatory or optional-protocol
hypothesis is used here.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the literal report-required observed-access source carrier,
Definition 6's resampling policy is observably fair up to null public-base
fibres and demographically fair for the actual school output. -/
theorem lg21ContinuousGaussianPopulation_reportRequired_resampling_observableAndDemographicFair
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
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
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
        (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
        (hbaseLaw : IsProbabilityMeasure baseLaw)
        (hbaseVariance : 0 < baseVariance),
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal ∧
      (letI : IsProbabilityMeasure baseLaw := hbaseLaw
       let S : LG21GaussianPBOResamplingSource
          (LG21NonTestFeature Feature testFeature -> ℝ) :=
        { baseLaw := baseLaw
          baseLaw_isProbability := inferInstance
          posteriorBaseMean := baseMean
          posteriorBaseMean_measurable := hbaseMean
          posteriorBaseVariance := baseVariance.toNNReal
          posteriorBaseVariance_pos := by
            rw [NNReal.coe_pos, Real.toNNReal_pos]
            exact hbaseVariance
          testNoiseVariance := M.noiseVariance testFeature
          testNoiseVariance_pos := htestNoiseVariance }
       let actualOutput := lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) E
       (condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S))) := by
  intro source hstable
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  have hactualOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E htestLaw baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization source hstable
  simpa using
    (lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) E)
      hactualOutput)

end

end LG21TestOptionalPolicies
