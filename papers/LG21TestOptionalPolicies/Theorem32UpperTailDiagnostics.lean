import LG21TestOptionalPolicies.MainTheorems

/-!
# Theorem 3.2 Upper-Tail Source-Equilibrium Diagnostics

Small diagnostics for the literal fully specified upper-tail source models used
around Theorem 3.2.  These live outside `MainTheorems.lean` so the local proof
loop can stay focused on the upper-tail equilibrium seam.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability

/--
Optional-reporting upper-tail source models fail pointwise source equilibrium at
any reported score below the no-report upper-tail mean.  The existing cutoff
diagnostic is the boundary instance of this stronger interval obstruction.
-/
theorem lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData_not_sourceEquilibrium_of_reported_lt_upper_tail_mean
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (skill : Skill) (base : Base) (actor : ℝ)
    (hreport : decisionThreshold base ≤ actor)
    (hbelowUpper :
      actor <
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (actorLaw base) (decisionThreshold base)) :
    ¬ lg21SourceEquilibrium
      (lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData
        M theta k takeDecision estimationConsistent actorLaw
        decisionThreshold) := by
  classical
  let upper : ℝ :=
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  let E : LG21SourceEquilibriumData Skill Base ℝ :=
    lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData
      M theta k takeDecision estimationConsistent actorLaw decisionThreshold
  intro hEq
  let info : LG21AccessStudentInfo Skill Base ℝ :=
    { skill := skill, base := base, test := actor }
  have hbest :=
    lg21SourceEquilibrium_best_response
      (E := E) hEq info LG21AccessAction.takeAndWithhold
      LG21AccessAction.takeAndWithhold_optionalReporting_feasible
  have hbest' :
      (M base).posteriorMean (Function.update (theta base) k upper) ≤
        (M base).posteriorMean (Function.update (theta base) k actor) := by
    simpa [E, info, upper,
      lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData,
      lg21OptionalReportingBaseSourceEquilibriumData,
      LG21SourceEquilibriumData.toEquilibriumData,
      LG21AccessStudentInfo.chosenAction, hreport] using hbest
  have hposterior_lt :
      (M base).posteriorMean (Function.update (theta base) k actor) <
        (M base).posteriorMean (Function.update (theta base) k upper) :=
    (paper_bayesian_optimal_estimator_strictMono_feature
      (M base) (theta base) k) (by simpa [upper] using hbelowUpper)
  exact (not_lt_of_ge hbest') hposterior_lt

/--
Report-required upper-tail source models fail pointwise source equilibrium at
any latent skill below the upper-tail mean that the cutoff policy asks to take
the test.
-/
theorem lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData_not_sourceEquilibrium_of_taker_lt_upper_tail_mean
    {Base Test : Type*}
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base : Base) (test : Test) (skill : ℝ)
    (htake : decisionThreshold base ≤ skill)
    (hbelowUpper :
      skill <
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (actorLaw base) (decisionThreshold base)) :
    ¬ lg21SourceEquilibrium
      (lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData
        reportDecision estimationConsistent actorLaw decisionThreshold) := by
  classical
  let upper : ℝ :=
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  let E : LG21SourceEquilibriumData ℝ Base Test :=
    lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData
      reportDecision estimationConsistent actorLaw decisionThreshold
  intro hEq
  let info : LG21AccessStudentInfo ℝ Base Test :=
    { skill := skill, base := base, test := test }
  have hbest :=
    lg21SourceEquilibrium_best_response
      (E := E) hEq info LG21AccessAction.noTake
      LG21AccessAction.noTake_reportRequiredAfterTaking_feasible
  have hbest' :
      (1 / 2 : ℝ) ≤ (1 / 2 - upper) + skill := by
    simpa [E, info, upper,
      lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData,
      lg21ReportRequiredBaseSourceEquilibriumData,
      LG21SourceEquilibriumData.toEquilibriumData,
      LG21AccessStudentInfo.chosenAction, htake] using hbest
  have hbelowUpper' : skill < upper := by
    simpa [upper] using hbelowUpper
  linarith

end

end LG21TestOptionalPolicies
