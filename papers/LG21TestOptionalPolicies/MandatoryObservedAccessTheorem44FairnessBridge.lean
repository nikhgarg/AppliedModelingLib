import LG21TestOptionalPolicies.ObservedAccessConditionalOutputKernel

/-!
# Mandatory observed-access fairness bridge for LG21 Theorem 4.4

This is the literal mandatory-given-access specialization of the common
observed-access output theorem.  Feasibility determines the attained action;
the full-record PBO remains an explicit on-path source-policy premise.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory
open AppliedModelingLib.Probability

/-- Under mandatory-given-access feasibility and the attained full-record PBO,
the literal output is observably fair up to null base fibres and demographically
fair against Definition 6's no-access resampling policy. -/
theorem lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hfullBaseFactorization :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
    (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff) :
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
    letI : IsProbabilityMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure
        (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
    let actualOutput := lg21ObservedAccessActualOutput
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      mandatory.action reportedPayoff noReportPayoff
    (condDistrib actualOutput (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianAccessPopulationLaw M) =ᵐ[
        (lg21ContinuousGaussianAccessPopulationLaw M).map
          (lg21ContinuousPopulationBase testFeature)]
        lg21D6NoAccessResamplingEstimateKernel S) ∧
      ((lg21ContinuousGaussianAccessPopulationLaw M).map actualOutput =
        Measure.bind
          ((lg21ContinuousGaussianNoAccessPopulationLaw M).map
            (lg21ContinuousPopulationBase testFeature))
          (lg21D6NoAccessResamplingEstimateKernel S)) := by
  have hall : ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport :=
    lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible
  exact
    lg21ContinuousGaussianAccessPopulation_observedAccessOutput_observableAndDemographicFair_of_all_take_report_and_pbo
      M haccess hnoAccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hfullBaseFactorization mandatory.action
      reportedPayoff noReportPayoff hall hreportedPBO

end

end LG21TestOptionalPolicies
