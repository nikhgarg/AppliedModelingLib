import LG21TestOptionalPolicies.HiddenAccessTheorem31BaseSupport
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReporterFibreBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceLocalCandidateConstruction

/-!
# Literal optional all-taking closeout for LG21 Theorem 3.1

This is the source-population endpoint for the pre-score optional action.
It derives the a.e. conclusion from literal positive-branch PBOs and local
candidate stability, rather than a supplied cutoff or a pointwise completion
of an unattained public action.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- In the hidden-access optional regime, literal stability against every
positive-mass local recalibration makes the pre-score no-take action null.
The only source regularity used here is positive Gaussian variance for the
latent profile and each signal coordinate. -/
theorem lg21HiddenAccess_optional_activeNoTake_measure_zero_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportBest : E.OptionalReportBestResponseAE)
    (hstable : LG21HiddenAccessSourceStableAgainstLocalCandidateEntry E hnoAccess) :
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 := by
  let hentry : ∀ region : Set (LG21NonTestFeature Feature testFeature -> ℝ),
      ∀ hregion : MeasurableSet region,
      ∀ hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region),
      ∀ hzero : lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩
          lg21HiddenAccessActualReportEvent E) = 0,
      LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess :=
    fun region hregion hpositive hzero =>
      lg21HiddenAccess_sourceLocalCandidateEntry_of_zeroReporterBaseRegion
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance E region hregion hpositive hzero
  have hreporterPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) := by
    simpa [lg21HiddenAccessActualReportEvent] using
      (E.actualReportEvent_positive_of_stable hnoAccess hstable hentry)
  rcases
      lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hrawFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have haccessFactor :
    (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    calc
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          (lg21ContinuousGaussianPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
            simpa [lg21HiddenAccessBaseScoreSkillObservation] using
              (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                M haccess testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) :=
        hrawFactor
  have hreporterGain :=
    lg21HiddenAccess_rawReporterBaseStrictGain_ae_of_fullGaussianFactorization
      E hreportBest baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
      haccessFactor hreporterPositive
  apply E.activeNoTakeEvent_measure_zero_of_reporterBaseStrictGain
    hnoAccess hstable hentry
  simpa [lg21HiddenAccessActualReportEvent] using hreporterGain

end

end LG21TestOptionalPolicies
