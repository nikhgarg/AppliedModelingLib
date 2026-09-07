import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredActionClassification

/-!
# Population endpoint for report-required LG21 Theorem 3.1

This module turns an almost-everywhere fibre conclusion into the literal
population event used by the paper.  It uses the source factorization rather
than a strategy-name convention or an arbitrary value on an unattained
branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib AppliedModelingLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- A positive conditional event on almost every source fibre has positive
mass in the composed source law. -/
theorem lg21_compProd_positive_of_ae_positive_fibres
    {Base Outcome : Type*} [MeasurableSpace Base] [MeasurableSpace Outcome]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (outcomeKernel : Kernel Base Outcome) [IsMarkovKernel outcomeKernel]
    (event : Set (Base × Outcome)) (hevent : MeasurableSet event)
    (hfibres : ∀ᵐ base ∂baseLaw,
      0 < outcomeKernel base (Prod.mk base ⁻¹' event)) :
    0 < (baseLaw ⊗ₘ outcomeKernel) event := by
  have hmassMeasurable : Measurable
      (fun base => outcomeKernel base (Prod.mk base ⁻¹' event)) :=
    Kernel.measurable_kernel_prodMk_left hevent
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsuppAE : ∀ᵐ base ∂baseLaw,
      base ∈ Function.support
        (fun base => outcomeKernel base (Prod.mk base ⁻¹' event)) := by
    filter_upwards [hfibres] with base hpositive
    exact ne_of_gt hpositive
  have hsuppEq : Function.support
      (fun base => outcomeKernel base (Prod.mk base ⁻¹' event)) =ᵐ[baseLaw]
      Set.univ := by
    filter_upwards [hsuppAE] with base hmember
    apply propext
    constructor
    · intro _
      trivial
    · intro _
      exact hmember
  rw [measure_congr hsuppEq, IsProbabilityMeasure.measure_univ]
  norm_num

/-- The a.e. source-fibre conclusion for literal no-taking has positive raw
access population mass.  The transport explicitly maps the source's
`(skill, base)` decision law into `(base, skill)` order before using the
Gaussian factorization. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.activeNoTake_positive_of_ae_positive_noTakeFibres
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ))
    (haeNoTakeFibres : ∀ᵐ publicBase ∂baseLaw,
      0 < gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal publicBase
        {latentSkill | E.source.takeDecision latentSkill publicBase = false}) :
    0 < lg21ContinuousGaussianPopulationLaw M E.source.activeNoTakeEvent := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let skillKernel := gaussianLocationKernel
    baseMean hbaseMean baseVariance.toNNReal
  let action : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool :=
    fun publicBase latentSkill => E.source.takeDecision latentSkill publicBase
  let noTakeEvent : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    {baseSkill | action baseSkill.1 baseSkill.2 = false}
  let latentBase : Bool × (ℝ × (Feature -> ℝ)) ->
      ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student =>
      (lg21ContinuousPopulationSkill student,
        lg21HiddenAccessStudentBase testFeature student.2)
  let baseSkill : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    lg21HiddenAccessBaseSkillObservation testFeature
  letI : IsMarkovKernel skillKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haction : Measurable (fun baseSkill :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      action baseSkill.1 baseSkill.2) := by
    simpa [action] using
      (E.source.takeDecision_measurable.comp
        (measurable_snd.prodMk measurable_fst))
  have hnoTakeEvent : MeasurableSet noTakeEvent := by
    change MeasurableSet
      ((fun baseSkill : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        action baseSkill.1 baseSkill.2) ⁻¹' ({false} : Set Bool))
    exact (measurableSet_singleton false).preimage haction
  have hcompPositive : 0 < (baseLaw ⊗ₘ skillKernel) noTakeEvent := by
    apply lg21_compProd_positive_of_ae_positive_fibres
      baseLaw skillKernel noTakeEvent hnoTakeEvent
    simpa [noTakeEvent, action] using haeNoTakeFibres
  have hfactor :
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap =
        baseLaw ⊗ₘ skillKernel := by
    simpa [skillKernel] using
      (lg21HiddenAccessAccessLatentBaseLaw_swap_eq_gaussianLocation_of_scoreFactor
        M E.source.access_positive testFeature baseLaw baseMean hbaseMean
        baseVariance (M.noiseVariance testFeature : ℝ) hsourceFactor)
  have hlatentBase : Measurable latentBase := by
    simpa [latentBase] using
      (lg21HiddenAccessLatentBaseObservation_measurable testFeature)
  have hbaseSkill : Measurable baseSkill := by
    simpa [baseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have haccessFactor : accessLaw.map baseSkill = baseLaw ⊗ₘ skillKernel := by
    calc
      accessLaw.map baseSkill = (accessLaw.map latentBase).map Prod.swap := by
        rw [Measure.map_map measurable_swap hlatentBase]
        rfl
      _ = (lg21HiddenAccessAccessLatentBaseLaw M testFeature).map Prod.swap := by
        rfl
      _ = baseLaw ⊗ₘ skillKernel := hfactor
  have hnoTakePreimage : baseSkill ⁻¹' noTakeEvent = E.source.accessNoTakeEvent := by
    ext student
    simp [baseSkill, noTakeEvent, action,
      LG21HiddenAccessLiteralSourceEquilibriumAE.accessNoTakeEvent,
      lg21HiddenAccessBaseSkillObservation,
      lg21HiddenAccessStudentTake, lg21ContinuousPopulationSkill]
  have haccessNoTakePositive : 0 < accessLaw E.source.accessNoTakeEvent := by
    rw [← hnoTakePreimage, ← Measure.map_apply hbaseSkill hnoTakeEvent,
      haccessFactor]
    exact hcompPositive
  have haccessNoTakeMeasurable : MeasurableSet E.source.accessNoTakeEvent :=
    E.source.accessNoTakeEvent_measurable
  have hnormalizedPositive :
      0 < lg21NormalizedRestriction rawLaw accessEvent E.source.accessNoTakeEvent := by
    simpa [rawLaw, accessLaw, accessEvent,
      lg21ContinuousGaussianAccessPopulationLaw] using haccessNoTakePositive
  rw [lg21NormalizedRestriction_apply rawLaw haccessNoTakeMeasurable]
    at hnormalizedPositive
  have hrawIntersectionPositive :
      0 < rawLaw (E.source.accessNoTakeEvent ∩ accessEvent) :=
    (ENNReal.mul_pos_iff.mp hnormalizedPositive).2
  have hactiveEq : E.source.activeNoTakeEvent =
      E.source.accessNoTakeEvent ∩ accessEvent := by
    ext student
    simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
      LG21HiddenAccessLiteralSourceEquilibriumAE.accessNoTakeEvent,
      accessEvent, and_comm]
  simpa [rawLaw, hactiveEq] using hrawIntersectionPositive

/-- In the report-required regime, an access student who does not take has
literal public action `X = 0`.  This is the source text's "access students do
not report" event, expressed without selecting a score-stage action. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.activeNoTake_subset_optionalNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature) :
    E.source.activeNoTakeEvent ⊆
      lg21HiddenAccessOptionalNoReportEvent testFeature E.source.takeDecision
        E.source.reportDecision := by
  rintro ⟨access, primitive⟩ hactive
  have haccess : access = true := hactive.1
  subst access
  have hnoTake : lg21HiddenAccessStudentTake testFeature E.source.takeDecision
      primitive = false := hactive.2
  change lg21HiddenAccessOptionalObservedAction testFeature E.source.takeDecision
    E.source.reportDecision (true, primitive) = false
  simp [lg21HiddenAccessOptionalObservedAction, hnoTake]

/-- Positive literal access/no-take mass therefore supplies the theorem's
positive access-nonreporting population. -/
theorem LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.optionalNoReport_positive_of_activeNoTake_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hactive : 0 < lg21ContinuousGaussianPopulationLaw M E.source.activeNoTakeEvent) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature E.source.takeDecision
        E.source.reportDecision) :=
  lt_of_lt_of_le hactive (measure_mono E.activeNoTake_subset_optionalNoReportEvent)

end

end LG21TestOptionalPolicies
