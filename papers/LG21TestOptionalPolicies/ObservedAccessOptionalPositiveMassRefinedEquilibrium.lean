import LG21TestOptionalPolicies.ObservedAccessOptionalSourceTimedCloseout

/-!
# Positive-mass refined optional equilibrium carrier for LG21

This module records the source's optional-reporting actions and attained PBOs
under the approved positive-mass refinement.  It intentionally does not use a
pointwise best-response condition to assign a payoff comparison at a null
history.  Instead, it rules out the two literal positive-mass, recalibrated
entries used in the Section 4 argument.  Each PBO condition is conditional on
the actual action branch having positive mass.

This is a refinement carrier, not an existence theorem and not a claim that a
canonical all-take/all-report profile is a source equilibrium.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open AppliedModelingLib.Probability
open scoped ENNReal ProbabilityTheory

/--
Source-faithful optional-reporting data under the positive-mass recalibrated
stability refinement.

The action rules remain the source-timed `Y` and `X` rules.  Unlike
`LG21ObservedAccessOptionalSourceTimedEquilibrium`, this carrier has no
pointwise report- or take-stage best-response field: an unobserved/null action
history receives no artificial payoff comparison.  The two stability fields
quantify over literal positive-mass candidates whose PBOs are recalibrated
under their own selected action populations.  The remaining PBO fields bind
the school output only on actual positive-mass branches.
-/
structure LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) where
  actions : LG21OptionalSourceTimedActions
    (LG21NonTestFeature Feature testFeature -> ℝ)
  takeDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    actions.takeDecision pair.2 pair.1)
  reportDecision_measurable : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
    actions.reportDecision pair.1 pair.2)
  /-- No local positive-base-mass entry from a branch with zero actual reporter
  mass, evaluated using the candidate's recalibrated branch PBOs. -/
  local_recalibrated_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      actions.testLaw actions.takeDecision actions.reportDecision
  /-- No positive-mass entry that promotes current nonreporters, evaluated
  under the candidate's own positive report and no-report action laws. -/
  recalibrated_report_entry_stable :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntryForTestLaw
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
        ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
          lg21ContinuousPopulationSkill_measurable))
      actions.testLaw actions.takeDecision actions.reportDecision
  test_law_gaussian : ∀ publicBase latentSkill,
    actions.testLaw latentSkill publicBase =
      gaussianReal latentSkill (M.noiseVariance testFeature)
  /-- PBO integrability on the actual `take = report = true` branch, required
  only when that branch has positive source mass. -/
  actual_report_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))
  /-- The reported output is the PBO conditional mean on the actual positive
  `take = report = true` branch. -/
  actual_report_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    (fun student => actions.reportedPayoff
      (lg21ContinuousPopulationBase testFeature student)
      (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            actions.takeDecision actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (fun student =>
              (lg21ContinuousPopulationBase testFeature student,
                lg21ContinuousPopulationFeature testFeature student))
              inferInstance]
  /-- PBO integrability on the actual complement of the full report action,
  required only when that branch has positive source mass. -/
  actual_noReport_integrable : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))
  /-- The no-report output is the PBO conditional mean on the actual positive
  complement of the full report action. -/
  actual_noReport_pbo : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision) ->
    (fun student => actions.noReportPayoff
      (lg21ContinuousPopulationBase testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceNoReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            actions.takeDecision actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          actions.takeDecision actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (lg21ContinuousPopulationBase testFeature)
              inferInstance]

namespace LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium

/-- Forget pointwise best-response requirements from the older source-timed
carrier while retaining its literal action, stability, and attained-PBO data. -/
def ofSourceTimedEquilibrium
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalSourceTimedEquilibrium M haccess testFeature) :
    LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature where
  actions := E.actions
  takeDecision_measurable := E.takeDecision_measurable
  reportDecision_measurable := E.reportDecision_measurable
  local_recalibrated_entry_stable := by
    intro region candidateTake candidateReport candidate _hfixedLaw hentry
    exact E.local_entry_stable region candidateTake candidateReport candidate hentry
  recalibrated_report_entry_stable := by
    intro candidateTake candidateReport candidate _hfixedLaw hentry
    exact E.recalibrated_report_entry_stable
      candidateTake candidateReport candidate hentry
  test_law_gaussian := E.test_law_gaussian
  actual_report_integrable := E.actual_report_integrable
  actual_report_pbo := E.actual_report_pbo
  actual_noReport_integrable := E.actual_noReport_integrable
  actual_noReport_pbo := E.actual_noReport_pbo

end LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium

end

end LG21TestOptionalPolicies
