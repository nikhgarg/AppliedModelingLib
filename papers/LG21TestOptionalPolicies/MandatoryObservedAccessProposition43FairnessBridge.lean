import LG21TestOptionalPolicies.ObservedAccessProposition43FairnessBridge

/-!
# Mandatory observed-access Proposition 4.3 bridge for LG21

This is the literal mandatory-given-access specialization of the common
Proposition 4.3 Gaussian argument.  Mandatory feasibility derives the actual
all-report action on the positive-access population; the full-record PBO then
identifies its realized output with the source-derived Definition 6 access
estimator.  The no-access side is constrained only by its own literal PBO
semantics.

No output law or conditional-kernel gap is an input to this endpoint.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- Under the literal mandatory-given-access protocol, the actual PBO output
differs from the actual no-access PBO both conditionally on almost every
public base profile and in its population output law.  The displayed Gaussian
factorization and posterior-mean law are derived from the literal source
population; neither comparison is supplied as a premise. -/
theorem lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_observableOrDemographicFair
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff)
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
                 mandatory.action reportedPayoff noReportPayoff)
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianAccessPopulationLaw M) publicBase ≠
             condDistrib noAccessOutput
               (lg21ContinuousPopulationBase testFeature)
               (lg21ContinuousGaussianNoAccessPopulationLaw M) publicBase) ∧
          ((lg21ContinuousGaussianAccessPopulationLaw M).map
              (lg21ObservedAccessActualOutput
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                mandatory.action reportedPayoff noReportPayoff) ≠
            (lg21ContinuousGaussianNoAccessPopulationLaw M).map noAccessOutput)) := by
  rcases
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw_exists_gaussianLocationFactorization_with_meanLaw
        M testFeature hpriorVariance hnonTestNoiseVariance with
      ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
        hbaseLaw, hbaseVariance, hbaseMeanVariance, hfactorization,
        hbaseMeanLaw⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  refine ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw,
    hbaseMean, hbaseVariance, hfactorization, hbaseMeanVariance, ?_⟩
  have hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport :=
    lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible
  have haccessOutput :=
    lg21ContinuousGaussianAccessPopulation_actualOutput_eq_d6_ae_of_all_take_report_and_pbo
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfactorization mandatory.action
      reportedPayoff noReportPayoff hall hreportedPBO
  simpa using
    (lg21ContinuousGaussianPopulation_actualPBO_not_observableOrDemographicFair_of_d6_ae
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      baseMeanVariance hbaseVariance hbaseMeanVariance hbaseMeanLaw
      htestNoiseVariance hfactorization
      (lg21ObservedAccessActualOutput
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        mandatory.action reportedPayoff noReportPayoff)
      noAccessOutput haccessOutput hnoAccessPBO)

end

end LG21TestOptionalPolicies
