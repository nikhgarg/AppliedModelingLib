import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralAllTakeCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeWithholdingCloseout

/-!
# Literal optional hidden-access core for LG21 Theorem 3.1

This module composes the two source-law endpoints that do not require a
cutoff representation: access students take almost everywhere, and a positive
literal mass of those students withholds their score.  Both conclusions come
from one literal source population and its actual action/PBO branches.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/-- The source-level behavioral core of hidden-access optional reporting.
Under the source's positive-mass recalibration semantics, literal Gaussian
actions imply all taking almost everywhere and strictly positive score
withholding mass.  No cutoff, affine payoff, or null-history PBO is assumed. -/
theorem lg21HiddenAccess_optional_allTake_and_positiveWithholding_of_literalSourceStability
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
    lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 ∧
      0 < lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) := by
  have hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0 :=
    lg21HiddenAccess_optional_activeNoTake_measure_zero_of_literalSourceStability
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E hreportBest hstable
  rcases
      lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hsourceFactor⟩
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
        hsourceFactor
  refine ⟨hactiveNoTakeZero, ?_⟩
  exact E.accessNoReportEvent_positive_of_allTake hreportBest hnoAccess hactiveNoTakeZero
    baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
    haccessFactor

end

end LG21TestOptionalPolicies
