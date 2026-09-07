import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLocalTailCloseout

/-!
# Positive-taking endpoint for report-required LG21 Theorem 3.1

This is the source-stability exclusion of the zero-taker branch.  It is kept
separate from the all-taker argument so the clean report-required path does
not inherit an optional score-stage reporting deviation.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Literal stability against positive-mass report-required local entries
rules out the all-no-taking endpoint.  The candidate is constructed on the
entire public-base region, so this conclusion does not presume a named
threshold or a positive individual base fibre. -/
theorem lg21HiddenAccess_reportRequired_positiveTake_of_literalSourceStability_clean
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.takeDecision) :
    0 < lg21ContinuousGaussianPopulationLaw M
      {student | student.1 = true ∧
        E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} := by
  by_contra hnotPositive
  let currentTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true ∧
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
  have hcurrentTakeZero : lg21ContinuousGaussianPopulationLaw M
      currentTakeEvent = 0 := by
    exact bot_unique (le_of_not_gt (by simpa [currentTakeEvent] using hnotPositive))
  exact
    (lg21ReportRequired_not_stable_of_globalCurrentTake_zero_of_source
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E.takeDecision E.takeDecision_measurable
      hcurrentTakeZero) hstable

end

end LG21TestOptionalPolicies
