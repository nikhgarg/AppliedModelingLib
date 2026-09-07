import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessOptionalProposition43SourceTimedBridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredProposition43Bridge

/-!
# Three-protocol literal Proposition 4.3 endpoint for LG21

This endpoint compares actual PBO outputs on the literal positive-access and
no-access populations.  It keeps the no-access PBO as an RCD-mean obligation,
rather than replacing it by a base-mean output in the theorem statement.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the three literal observed-access requirement protocols, PBO is not
observably fair outside null base fibres and is not demographically fair. -/
theorem lg21ContinuousGaussianPopulation_allObservedAccessProtocols_actualPBO_not_observableOrDemographicFair
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
        ((M.noiseVariance testFeature : ℝ).toNNReal))
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
      lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
    letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
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
               (lg21ObservedAccessActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ObservedAccessActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput) ∧
          (∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21OptionalSourceTimedActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21OptionalSourceTimedActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput) ∧
          (∀ᵐ publicBase ∂baseLaw,
           condDistrib
               (lg21ReportRequiredSequentialActualOutput
                 (lg21ContinuousPopulationBase testFeature)
                 (lg21ContinuousPopulationFeature testFeature)
                 (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ReportRequiredSequentialActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput)) := by
  intro reportRequiredSource hreportRequiredStable
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hbaseMeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  have hallMandatory : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport :=
    lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible
  have hmandatoryOutput :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization mandatory.action
      mandatoryReportedPayoff mandatoryNoReportPayoff hallMandatory
      hmandatoryReportedPBO
  have hmandatory :=
    lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21ObservedAccessActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        mandatory.action mandatoryReportedPayoff mandatoryNoReportPayoff)
      noAccessOutput hmandatoryOutput hnoAccessPBO
  have hoptionalOutput :=
    lg21ContinuousGaussianAccessPopulation_optional_sourceTimed_actualOutput_eq_d6_ae
      M haccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance optional baseLaw baseMean hbaseMean baseVariance
      hbaseVariance hfactorization
  have hoptional :=
    lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21OptionalSourceTimedActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) optional.actions)
      noAccessOutput hoptionalOutput hnoAccessPBO
  have hreportRequiredOutput :=
    lg21ContinuousGaussianAccessPopulation_reportRequired_actualOutput_eq_d6_ae_of_literalSource
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance reportRequired hreportRequiredTestLaw baseLaw baseMean
      hbaseMean baseVariance hbaseVariance hfactorization
      reportRequiredSource hreportRequiredStable
  have hreportRequired :=
    lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21ReportRequiredSequentialActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired)
      noAccessOutput hreportRequiredOutput hnoAccessPBO
  exact ⟨hmandatory.1, hmandatory.2, hoptional.1, hoptional.2,
    hreportRequired.1, hreportRequired.2⟩

end

end LG21TestOptionalPolicies
