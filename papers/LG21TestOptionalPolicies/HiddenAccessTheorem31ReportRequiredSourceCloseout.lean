import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredPositiveTakeCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLocalFibreCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLiteralCutoff
import LG21TestOptionalPolicies.HiddenAccessTheorem31SelectedBaseLift
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredAllTakeFibreEndpoint
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredPopulationCloseout

/-!
# Source closeout composition for report-required LG21 Theorem 3.1

This module composes the literal local-entry exclusion, the feasible
pre-score all-take exclusion, the selected Gaussian cutoff argument, and the
selected-base transport.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- Under forced reporting, every positive literal access-taking population
is a positive literal reporter population.  This is only an equality of the
actual action events; it does not assign a payoff to an unreached branch. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.reporter_positive_of_positive_access_taking
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (htakePositive : 0 < lg21ContinuousGaussianPopulationLaw M
      {student | student.1 = true ∧
        E.source.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true}) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
        E.source.reportDecision) := by
  have hreportEvent :
      lg21HiddenAccessOptionalReportEvent testFeature E.source.takeDecision
          E.source.reportDecision =
        {student | student.1 = true ∧
          E.source.takeDecision (lg21ContinuousPopulationSkill student)
            (lg21HiddenAccessStudentBase testFeature student.2) = true} := by
    ext student
    rcases student with ⟨access, primitive⟩
    have hforced : lg21HiddenAccessStudentReport testFeature
        E.source.reportDecision primitive = true := by
      exact E.reportDecision_eq_true
        (lg21HiddenAccessStudentBase testFeature primitive)
        (lg21HiddenAccessStudentScore testFeature primitive)
    cases access <;>
      simp [lg21HiddenAccessOptionalReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21ContinuousPopulationSkill, hforced]
  rw [hreportEvent]
  exact htakePositive

/-- The source equilibrium itself gives positive literal access/no-take mass.
The proof first excludes zero no-take fibres using the feasible pre-score
choice condition, then transports the fibre mass through the raw Gaussian
source law. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.activeNoTake_positive_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    0 < lg21ContinuousGaussianPopulationLaw M E.source.activeNoTakeEvent := by
  apply E.activeNoTake_positive_of_ae_positive_noTakeFibres
    baseLaw baseMean hbaseMean baseVariance hsourceFactor
  exact E.ae_positive_noTakeFibres_of_sourceGaussianFactor hnoAccess baseLaw
    baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance hsourceFactor

/-- The positive literal access/no-take branch is a positive literal
no-report branch under the report-required policy. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.optionalNoReport_positive_of_sourceGaussianFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature E.source.takeDecision
        E.source.reportDecision) := by
  apply E.optionalNoReport_positive_of_activeNoTake_positive
  exact E.activeNoTake_positive_of_sourceGaussianFactor hnoAccess baseLaw
    baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance hsourceFactor

/-- Literal local-tail stability yields the finite source taking cutoff once
the source's feasible pre-score choice condition has supplied the
complementary no-take fibres.  The conclusion is on the original base law,
not merely on the selected reporter law. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.exists_finite_takeCutoff_ae_of_localTailStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.source.takeDecision)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ)) :
    let skillKernel := gaussianLocationKernel
      baseMean hbaseMean baseVariance.toNNReal
    letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
      baseMean hbaseMean baseVariance.toNNReal
    ∀ᵐ publicBase ∂baseLaw,
      ∃ cutoff : ℝ,
        ∀ᵐ latentSkill ∂skillKernel publicBase,
          E.source.takeDecision latentSkill publicBase =
            decide (cutoff ≤ latentSkill) := by
  intro skillKernel
  letI : IsMarkovKernel skillKernel := gaussianLocationKernel_isMarkov
    baseMean hbaseMean baseVariance.toNNReal
  have haeNoTakeFibres := E.ae_positive_noTakeFibres_of_sourceGaussianFactor
    hnoAccess baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance hsourceFactor
  let action : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
    fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
  let actionEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    lg21SourceLatentActionEvent action
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hactionEvent : MeasurableSet actionEvent := by
    simpa [actionEvent] using lg21SourceLatentActionEvent_measurable action haction
  have htakePositiveGlobal :=
    lg21HiddenAccess_reportRequired_positiveTake_of_literalSourceStability_clean
      M E.source.access_positive hnoAccess testFeature hpriorVariance
      hnonTestNoiseVariance htestNoiseVariance E.source hstable
  have hreporterPositive :=
    E.reporter_positive_of_positive_access_taking htakePositiveGlobal
  have htakeFibres : ∀ᵐ publicBase ∂baseLaw,
      selectionMass skillKernel actionEvent publicBase ≠ 0 := by
    simpa [skillKernel, action, actionEvent] using
      (E.ae_positive_takeSelectionMass_of_localTailStability hnoAccess hstable
        baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
        hsourceFactor)
  have hcutoffSelected : ∀ᵐ publicBase ∂
      normalizedSelectedBase baseLaw skillKernel actionEvent,
      ∃ cutoff : ℝ,
        ∀ᵐ latentSkill ∂skillKernel publicBase,
          E.source.takeDecision latentSkill publicBase =
            decide (cutoff ≤ latentSkill) := by
    simpa [skillKernel, action, actionEvent] using
      (E.exists_finite_takeCutoff_ae_by_selectedBase_of_sourceGaussianFactor
        baseLaw baseMean hbaseMean baseVariance hbaseVariance htestNoiseVariance
        hsourceFactor hreporterPositive haeNoTakeFibres)
  exact lg21_ae_base_of_ae_normalizedSelectedBase_of_ae_positiveFibres
    baseLaw skillKernel actionEvent hactionEvent hcutoffSelected htakeFibres

end

end LG21TestOptionalPolicies
