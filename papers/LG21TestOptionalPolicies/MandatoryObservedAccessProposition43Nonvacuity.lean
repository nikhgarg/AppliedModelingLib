import LG21TestOptionalPolicies.ObservedAccessProposition43PolicyEndpoints
import LG21TestOptionalPolicies.ContinuousObservedAccessActualPBOBridge

/-!
# Nonvacuous mandatory Proposition 4.3 witness for LG21

This module supplies the one requirement regime whose literal source action is
forced by feasibility.  It deliberately does not make any claim about the
optional or report-required-after-taking equilibrium carriers.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory

/-- The literal action imposed by the source's reporting-required-given-access
protocol: applicants with access take and report, while applicants without
access cannot take. -/
def lg21MandatoryGivenAccessLiteralAction
    {Feature : Type*} : Bool × (ℝ × (Feature -> ℝ)) -> LG21AccessAction :=
  fun student =>
    if lg21ContinuousPopulationAccess student = true then
      LG21AccessAction.takeAndReport
    else
      LG21AccessAction.noTake

/-- The literal mandatory action is source-feasible on every population point. -/
theorem lg21MandatoryGivenAccessLiteralAction_feasible
    {Feature : Type*} (student : Bool × (ℝ × (Feature -> ℝ))) :
    LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredGivenAccess
      (lg21ContinuousPopulationAccessStatus student)
      (lg21MandatoryGivenAccessLiteralAction student) := by
  by_cases haccess : lg21ContinuousPopulationAccess student = true
  · rw [lg21ContinuousPopulationAccessStatus_eq_access student haccess]
    rw [show lg21MandatoryGivenAccessLiteralAction student =
      LG21AccessAction.takeAndReport by
        simp [lg21MandatoryGivenAccessLiteralAction, haccess]]
    exact
      (LG21RequirementPolicy.feasibleAction_access_reportRequiredGivenAccess_iff
        LG21AccessAction.takeAndReport).2 rfl
  · have hnoAccess : lg21ContinuousPopulationAccess student = false := by
      cases hvalue : lg21ContinuousPopulationAccess student
      · rfl
      · exact False.elim (haccess hvalue)
    rw [lg21ContinuousPopulationAccessStatus_eq_noAccess student hnoAccess]
    rw [show lg21MandatoryGivenAccessLiteralAction student =
      LG21AccessAction.noTake by
        simp [lg21MandatoryGivenAccessLiteralAction, hnoAccess]]
    exact
      (LG21RequirementPolicy.feasibleAction_noAccess_iff
        LG21RequirementPolicy.reportRequiredGivenAccess LG21AccessAction.noTake).2 rfl

/--
The mandatory-given-access regime has an actual PBO witness with the two
Proposition 4.3 fairness failures.  In contrast to the optional and
report-required-after-taking regimes, no off-path behavioral payoff is needed:
the requirement itself fixes the access action.
-/
theorem lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair_exists_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ)) :
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
    ∃ (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
        (reportedPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ)
        (noReportPayoff : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
        (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ),
      LG21ObservedAccessAllReportPBO
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff ∧
        LG21ContinuousGaussianNoAccessPopulationPBO
          M hnoAccess testFeature noAccessOutput ∧
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseMean : Measurable baseMean),
          IsProbabilityMeasure baseLaw ∧
            0 < baseVariance ∧
            lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
                baseLaw ⊗ₘ gaussianLocationKernel
                  baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21ObservedAccessActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  mandatory.action reportedPayoff noReportPayoff)
                noAccessOutput)) ∧
            (¬ LG21ObservedAccessDeterministicDemographicallyFair
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousGaussianNoAccessPopulationLaw M)
              (lg21ObservedAccessDeterministicTwoBranchOutput
                lg21ContinuousPopulationAccess
                (lg21ObservedAccessActualOutput
                  (lg21ContinuousPopulationBase testFeature)
                  (lg21ContinuousPopulationFeature testFeature)
                  mandatory.action reportedPayoff noReportPayoff)
                noAccessOutput)) := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  let mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M :=
    { action := lg21MandatoryGivenAccessLiteralAction
      feasible := fun student => lg21MandatoryGivenAccessLiteralAction_feasible student }
  let reportedPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> ℝ :=
    lg21ContinuousObservedAccessUnselectedPBO M haccess testFeature
  let noReportPayoff :
      (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ := fun _ => 0
  let noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ := fun student =>
    ∫ latentSkill, latentSkill ∂condDistrib
      (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousGaussianNoAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature student)
  have hreportedPBO : LG21ObservedAccessAllReportPBO
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff := by
    simpa [LG21ObservedAccessAllReportPBO, reportedPayoff] using
      (lg21ContinuousObservedAccess_unselectedPBO_eq_condExp_ae
        M haccess testFeature).symm
  have hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      M hnoAccess testFeature noAccessOutput := by
    change noAccessOutput =ᵐ[lg21ContinuousGaussianNoAccessPopulationLaw M]
      fun student => ∫ latentSkill, latentSkill ∂condDistrib
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousGaussianNoAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature student)
    exact Filter.Eventually.of_forall fun _ => rfl
  refine ⟨mandatory, reportedPayoff, noReportPayoff, noAccessOutput,
    hreportedPBO, hnoAccessPBO, ?_⟩
  rcases
      lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory reportedPayoff noReportPayoff hreportedPBO
        noAccessOutput hnoAccessPBO with
    ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseLaw, hbaseMean,
      hbaseVariance, hfactorization, hbaseMeanVariance, hobservable,
      hdemographic⟩
  exact ⟨baseLaw, baseMean, baseVariance, baseMeanVariance, hbaseMean,
    hbaseLaw, hbaseVariance, hfactorization, hbaseMeanVariance, hobservable,
    hdemographic⟩

end

end LG21TestOptionalPolicies
