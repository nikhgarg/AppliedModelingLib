import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalThresholdClassification

/-!
# Source closeout for the optional branch of LG21 Theorem 3.1

This is the source-facing optional-reporting portion of the theorem.  The
three conclusions are kept separate in the statement because they live on
their literal action laws: pre-score all-taking is a raw-population fact, the
post-score rule is an access base-score fact, and withholding is a positive
raw-population event.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Literal stable hidden-access optional reporting has the advertised
behavioral form: access students take almost everywhere; reporting is the
finite raw-Gaussian posterior cutoff almost everywhere on the literal access
base-score population; and a positive literal mass of access students
withholds their scores. -/
theorem lg21HiddenAccess_optional_sourceCloseout_of_literalSourceStability
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
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 ∧
      (∀ᵐ publicScore ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
        E.reportDecision publicScore.1 publicScore.2 =
          decide (affineCutoff
            (gaussianSignalPriorWeight baseVariance
              (M.noiseVariance testFeature : ℝ) * baseMean publicScore.1)
            (gaussianSignalWeight baseVariance
              (M.noiseVariance testFeature : ℝ))
            (E.noReportPayoff publicScore.1) ≤ publicScore.2)) ∧
      0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) := by
  have hcore :=
    lg21HiddenAccess_optional_allTake_and_positiveWithholding_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hreportBest hstable
  exact ⟨hcore.1,
    lg21HiddenAccess_optional_reportDecision_eq_rawPosteriorCutoff_ae_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance baseLaw baseMean hbaseMean baseVariance hbaseVariance
      hsourceFactor E hreportBest hstable,
    hcore.2⟩

end

end LG21TestOptionalPolicies
