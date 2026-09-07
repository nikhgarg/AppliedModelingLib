import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalCoreCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ScoreLocalPatchNoReportComparison

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- In a literal stable hidden-access optional equilibrium, no positive raw
population of access students can withhold a score whose raw Gaussian
posterior is strictly above the incumbent no-report value. -/
theorem lg21HiddenAccess_accessNoReport_rawPosteriorGain_measure_zero_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportStrictGainEvent testFeature E.reportDecision
        E.noReportPayoff
        (lg21OptionalRawGaussianPosteriorMean
          baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ))) = 0 := by
  have hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0 :=
    (lg21HiddenAccess_optional_allTake_and_positiveWithholding_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E hreportBest hstable).1
  have hcomparison :=
    lg21HiddenAccess_scoreLocalPatch_candidateNoReport_le_incumbent_ae
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      hbaseVariance htestNoiseVariance hsourceFactor E hactiveNoTakeZero
  let strictGain := lg21HiddenAccessAccessNoReportStrictGainEvent testFeature
    E.reportDecision E.noReportPayoff
    (lg21OptionalRawGaussianPosteriorMean
      baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
  by_contra hnotZero
  have hpositive : 0 < lg21ContinuousGaussianPopulationLaw M strictGain :=
    pos_iff_ne_zero.mpr hnotZero
  exact
    (lg21HiddenAccess_not_stable_of_positive_rawPosteriorGain_scoreLocalPatch
      M hnoAccess haccess testFeature baseLaw baseMean hbaseMean baseVariance
      (M.noiseVariance testFeature : ℝ) hbaseVariance htestNoiseVariance rfl
      hsourceFactor E hreportBest hactiveNoTakeZero (by simpa [strictGain] using hpositive)
      (by simpa using hcomparison)) hstable

end

end LG21TestOptionalPolicies
