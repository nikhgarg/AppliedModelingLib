import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium

/-!
# Literal hidden-access report-required source model

The report-required regime has the same literal population, pre-score action,
best-response, and actual-branch PBO semantics as the source-timed optional
model.  Its only additional requirement is that every tester reports the
realized score.  This wrapper deliberately introduces no generic
`estimationConsistent` field and no value for an unattained action branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Literal source equilibrium in the regime where taking entails reporting.
The embedded source carrier supplies the pointwise Definition-1 pre-score best
response and actual conditional-mean PBOs; `report_required` is just the
requirement policy's feasible-action constraint. -/
structure LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) where
  source : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature
  report_required : ∀ publicBase score,
    source.reportDecision publicBase score = true

namespace LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

/-- In the forced-report regime the post-score action is definitionally the
reported action for every literal public record. -/
theorem reportDecision_eq_true
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) (score : ℝ) :
    E.source.reportDecision publicBase score = true :=
  E.report_required publicBase score

/-- The only strategic action remaining after the requirement policy is the
pre-score taking action inherited from the literal source carrier. -/
theorem take_best_response_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature)
      (fun profile => E.source.takeDecision profile.1 profile.2 = true)
      (fun profile => ∫ score,
        E.source.reportedPayoff profile.2 score
          ∂E.source.testLaw profile.1 profile.2)
      (fun profile => E.source.noReportPayoff profile.2) := by
  have hsource := E.source.take_best_response_ae
  constructor
  · filter_upwards [hsource.1] with profile hchosen
    intro htake
    simpa [E.reportDecision_eq_true] using hchosen htake
  · filter_upwards [hsource.2] with profile hunchosen
    intro hnotTake
    simpa [E.reportDecision_eq_true] using hunchosen hnotTake

end LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE

end

end LG21TestOptionalPolicies
