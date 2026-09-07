import LG21TestOptionalPolicies.MandatoryObservedAccessTheorem44FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredD6OutputBridge
import LG21TestOptionalPolicies.ObservedAccessTheorem44FairnessBridge

/-!
# Three-protocol literal Theorem 4.4 endpoint for LG21

This is the source-facing Section 4 endpoint.  Each fairness conjunct concerns
the literal actual output of one requirement protocol, not a detached
Gaussian-summary experiment or a marginal-law alias.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the literal observed-access source carriers, Definition 6's
resampling policy is observably fair up to null base fibres and demographically
fair for mandatory-given-access, optional reporting, and report-required
testing. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_resampling_observableAndDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (mandatoryReportedPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (mandatoryNoReportPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hmandatoryReportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) mandatoryReportedPayoff)
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
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
       let mandatoryOutput := lg21ObservedAccessActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff
       let optionalOutput := lg21OptionalSourceTimedActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions
       let reportRequiredOutput := lg21ReportRequiredSequentialActualOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
       (condDistrib mandatoryOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map mandatoryOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S)) ∧
        (condDistrib optionalOutput (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map optionalOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S)) ∧
        (condDistrib reportRequiredOutput
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
            (lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature)]
            lg21D6NoAccessResamplingEstimateKernel S) ∧
        ((lg21ContinuousGaussianAccessPopulationLaw M).map reportRequiredOutput =
          Measure.bind
            ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
              (lg21ContinuousPopulationBase testFeature))
            (lg21D6NoAccessResamplingEstimateKernel S))) := by
  intro reportRequiredSource hreportRequiredStable
  rcases lg21ContinuousGaussianPopulation_exists_d6ResamplingSource
      M testFeature hpriorVariance hnonTestNoiseVariance htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw, hbaseVariance,
      hfactorization, _S, _hbaseLaw, _hbaseMean, _hbaseVariance,
      _htestNoiseVariance⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, hbaseMean, hbaseLaw,
    hbaseVariance, hfactorization, ?_⟩
  have hmandatory :=
    lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization mandatory
      mandatoryReportedPayoff mandatoryNoReportPayoff hmandatoryReportedPBO
  have hoptionalOutput :=
    lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization
  have hoptional :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
      hoptionalOutput
  have hreportRequiredOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance reportRequired hreportRequiredTestLaw baseLaw baseMean
      hbaseMean baseVariance hbaseVariance hfactorization
      reportRequiredSource hreportRequiredStable
  have hreportRequired :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_observableAndDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
      hreportRequiredOutput
  simpa using ⟨hmandatory.1, hmandatory.2, hoptional.1, hoptional.2,
    hreportRequired.1, hreportRequired.2⟩

end

end LG21TestOptionalPolicies
