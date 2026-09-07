import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Continuous strategic-advantage dominance for LG21

The last step of the proof of Theorem 3.1 compares an access student's chosen
estimate with the estimate of an otherwise identical student without access.
This file records the exact measure-theoretic implication: pointwise weak
benefit and positive-mass strict benefit imply upper-tail dominance, a strict
mean improvement, and unequal induced laws.

For optional reporting the comparison is between realized continuation
estimates.  For report-required testing, the student's action is chosen before
the noisy score is drawn, so the corresponding comparison is explicitly
between ex-ante expected estimates.  Keeping these two objects distinct avoids
silently upgrading an expected-payoff inequality to realized stochastic
dominance.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open MeasureTheory

/-- Weak first-order dominance, expressed by every strict upper tail. -/
def LG21FirstOrderEstimateDominates
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ) : Prop :=
  ∀ cutoff,
    studentLaw {student | cutoff < noAccessEstimate student} ≤
      studentLaw {student | cutoff < accessEstimate student}

/--
Strict dominance means weak upper-tail dominance together with genuinely
different induced estimate laws.
-/
def LG21StrictFirstOrderEstimateDominates
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ) : Prop :=
  LG21FirstOrderEstimateDominates
      studentLaw accessEstimate noAccessEstimate ∧
    Measure.map accessEstimate studentLaw ≠
      Measure.map noAccessEstimate studentLaw

/-- Pointwise weak strategic benefit implies every upper-tail inequality. -/
theorem lg21_firstOrderEstimateDominates_of_pointwise_le
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hle : ∀ student, noAccessEstimate student ≤ accessEstimate student) :
    LG21FirstOrderEstimateDominates
      studentLaw accessEstimate noAccessEstimate := by
  intro cutoff
  apply measure_mono
  intro student hstudent
  exact lt_of_lt_of_le hstudent (hle student)

/--
If weak benefit is strict on a positive-mass set, the population mean is
strictly higher.  This is the valid conclusion for the report-required
decision, whose payoff is evaluated before test noise is realized.
-/
theorem lg21_integral_accessEstimate_gt_noAccessEstimate
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hAccessIntegrable : Integrable accessEstimate studentLaw)
    (hNoAccessIntegrable : Integrable noAccessEstimate studentLaw)
    (hle : ∀ student, noAccessEstimate student ≤ accessEstimate student)
    (hstrict :
      studentLaw
          {student | noAccessEstimate student < accessEstimate student} ≠ 0) :
    (∫ student, noAccessEstimate student ∂studentLaw) <
      ∫ student, accessEstimate student ∂studentLaw := by
  have hleAE : noAccessEstimate ≤ᵐ[studentLaw] accessEstimate :=
    Filter.Eventually.of_forall hle
  have hintegral_le :
      (∫ student, noAccessEstimate student ∂studentLaw) ≤
        ∫ student, accessEstimate student ∂studentLaw :=
    integral_mono_ae hNoAccessIntegrable hAccessIntegrable hleAE
  have hintegral_ne :
      (∫ student, noAccessEstimate student ∂studentLaw) ≠
        ∫ student, accessEstimate student ∂studentLaw := by
    intro hintegral_eq
    have hae : noAccessEstimate =ᵐ[studentLaw] accessEstimate :=
      (integral_eq_iff_of_ae_le
        hNoAccessIntegrable hAccessIntegrable hleAE).1 hintegral_eq
    have hzero :
        studentLaw
            {student | noAccessEstimate student ≠ accessEstimate student} = 0 :=
      ae_iff.mp hae
    apply hstrict
    apply measure_mono_null
      (t := {student | noAccessEstimate student ≠ accessEstimate student})
    · intro student hstudent
      exact ne_of_lt hstudent
    · exact hzero
  exact lt_of_le_of_ne hintegral_le hintegral_ne

/--
Two measurable integrable output maps with different expectations induce
different output laws.  This is the appropriate demographic bridge when a
student chooses before a noisy score is realized: an ex-ante strict gain need
not imply pointwise dominance of realized estimates.
-/
theorem lg21_map_ne_of_integral_ne
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hAccessMeasurable : Measurable accessEstimate)
    (hNoAccessMeasurable : Measurable noAccessEstimate)
    (hAccessIntegrable : Integrable accessEstimate studentLaw)
    (hNoAccessIntegrable : Integrable noAccessEstimate studentLaw)
    (hmean :
      (∫ student, accessEstimate student ∂studentLaw) ≠
        ∫ student, noAccessEstimate student ∂studentLaw) :
    Measure.map accessEstimate studentLaw ≠
      Measure.map noAccessEstimate studentLaw := by
  intro hlaw
  have hintegral := congrArg
    (fun law : Measure ℝ => ∫ estimate, estimate ∂law) hlaw
  change
    (∫ estimate : ℝ, id estimate ∂Measure.map accessEstimate studentLaw) =
      ∫ estimate : ℝ, id estimate ∂Measure.map noAccessEstimate studentLaw
    at hintegral
  rw [integral_map_of_stronglyMeasurable
        hAccessMeasurable measurable_id.stronglyMeasurable,
      integral_map_of_stronglyMeasurable
        hNoAccessMeasurable measurable_id.stronglyMeasurable] at hintegral
  simp only [id_eq] at hintegral
  exact hmean hintegral

/-- Strict mean improvement rules out equality of the induced estimate laws. -/
theorem lg21_map_accessEstimate_ne_noAccessEstimate_of_strict_benefit
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hAccessMeasurable : Measurable accessEstimate)
    (hNoAccessMeasurable : Measurable noAccessEstimate)
    (hAccessIntegrable : Integrable accessEstimate studentLaw)
    (hNoAccessIntegrable : Integrable noAccessEstimate studentLaw)
    (hle : ∀ student, noAccessEstimate student ≤ accessEstimate student)
    (hstrict :
      studentLaw
          {student | noAccessEstimate student < accessEstimate student} ≠ 0) :
    Measure.map accessEstimate studentLaw ≠
      Measure.map noAccessEstimate studentLaw := by
  have hmean :=
    lg21_integral_accessEstimate_gt_noAccessEstimate
      studentLaw accessEstimate noAccessEstimate
      hAccessIntegrable hNoAccessIntegrable hle hstrict
  intro hlaw
  have hintegral :=
    congrArg
      (fun law : Measure ℝ => ∫ estimate, estimate ∂law)
      hlaw
  change
    (∫ estimate : ℝ, id estimate ∂Measure.map accessEstimate studentLaw) =
      ∫ estimate : ℝ, id estimate ∂Measure.map noAccessEstimate studentLaw
    at hintegral
  rw [integral_map_of_stronglyMeasurable
        hAccessMeasurable measurable_id.stronglyMeasurable,
      integral_map_of_stronglyMeasurable
        hNoAccessMeasurable measurable_id.stronglyMeasurable] at hintegral
  simp only [id_eq] at hintegral
  exact (ne_of_gt hmean) hintegral

/--
The a.e. form of the strict-benefit argument.  Literal source PBOs are only
identified on attained public histories, so source-facing output comparisons
are naturally almost-everywhere.  This lemma keeps that scope explicit while
still deriving unequal induced laws from a positive strict-gain set.
-/
theorem lg21_map_accessEstimate_ne_noAccessEstimate_of_ae_strict_benefit
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hAccessMeasurable : Measurable accessEstimate)
    (hNoAccessMeasurable : Measurable noAccessEstimate)
    (hAccessIntegrable : Integrable accessEstimate studentLaw)
    (hNoAccessIntegrable : Integrable noAccessEstimate studentLaw)
    (hle : noAccessEstimate ≤ᵐ[studentLaw] accessEstimate)
    (hstrict :
      studentLaw
          {student | noAccessEstimate student < accessEstimate student} ≠ 0) :
    Measure.map accessEstimate studentLaw ≠
      Measure.map noAccessEstimate studentLaw := by
  have hintegral_le :
      (∫ student, noAccessEstimate student ∂studentLaw) ≤
        ∫ student, accessEstimate student ∂studentLaw :=
    integral_mono_ae hNoAccessIntegrable hAccessIntegrable hle
  have hintegral_ne :
      (∫ student, noAccessEstimate student ∂studentLaw) ≠
        ∫ student, accessEstimate student ∂studentLaw := by
    intro hintegral_eq
    have hae : noAccessEstimate =ᵐ[studentLaw] accessEstimate :=
      (integral_eq_iff_of_ae_le
        hNoAccessIntegrable hAccessIntegrable hle).1 hintegral_eq
    have hzero :
        studentLaw
            {student | noAccessEstimate student ≠ accessEstimate student} = 0 :=
      ae_iff.mp hae
    apply hstrict
    apply measure_mono_null
      (t := {student | noAccessEstimate student ≠ accessEstimate student})
    · intro student hstudent
      exact ne_of_lt hstudent
    · exact hzero
  have hmean :
      (∫ student, noAccessEstimate student ∂studentLaw) <
        ∫ student, accessEstimate student ∂studentLaw :=
    lt_of_le_of_ne hintegral_le hintegral_ne
  intro hlaw
  have hintegral :=
    congrArg
      (fun law : Measure ℝ => ∫ estimate, estimate ∂law)
      hlaw
  change
    (∫ estimate : ℝ, id estimate ∂Measure.map accessEstimate studentLaw) =
      ∫ estimate : ℝ, id estimate ∂Measure.map noAccessEstimate studentLaw
    at hintegral
  rw [integral_map_of_stronglyMeasurable
        hAccessMeasurable measurable_id.stronglyMeasurable,
      integral_map_of_stronglyMeasurable
        hNoAccessMeasurable measurable_id.stronglyMeasurable] at hintegral
  simp only [id_eq] at hintegral
  exact (ne_of_gt hmean) hintegral

/--
Formal version of the valid strategic-dominance inference in Theorem 3.1.
-/
theorem paper_theorem3_1_strategic_advantage_strict_dominance
    {Student : Type*} [MeasurableSpace Student]
    (studentLaw : Measure Student)
    (accessEstimate noAccessEstimate : Student → ℝ)
    (hAccessMeasurable : Measurable accessEstimate)
    (hNoAccessMeasurable : Measurable noAccessEstimate)
    (hAccessIntegrable : Integrable accessEstimate studentLaw)
    (hNoAccessIntegrable : Integrable noAccessEstimate studentLaw)
    (hle : ∀ student, noAccessEstimate student ≤ accessEstimate student)
    (hstrict :
      studentLaw
          {student | noAccessEstimate student < accessEstimate student} ≠ 0) :
    LG21StrictFirstOrderEstimateDominates
      studentLaw accessEstimate noAccessEstimate :=
  ⟨lg21_firstOrderEstimateDominates_of_pointwise_le
      studentLaw accessEstimate noAccessEstimate hle,
    lg21_map_accessEstimate_ne_noAccessEstimate_of_strict_benefit
      studentLaw accessEstimate noAccessEstimate
      hAccessMeasurable hNoAccessMeasurable
      hAccessIntegrable hNoAccessIntegrable hle hstrict⟩

/-!
## From induced-law dominance to the three source fairness failures

The source fairness predicates compare estimate laws at three aggregation
levels.  The following endpoint makes the required law identities explicit:
once the access/no-access fields really are the pushforwards of the strategic
estimates, strict dominance at a witness for each aggregation level rules out
all three fairness notions.  This prevents a purely payoff-level comparison
from being silently treated as a statement about unrelated surface fields.
-/

/--
Policy surface whose three access/no-access comparisons are the actual
pushforward laws of the corresponding strategic estimates.  The base-only
and full-feature fields are retained as parameters because Theorem 3.1 uses
only Definitions 2--4.
-/
def lg21InducedStrategicEstimateLawSurface
    {Equilibrium Skill Base Test : Type*}
    {LatentPopulation ObservablePopulation DemographicPopulation : Type*}
    [MeasurableSpace LatentPopulation]
    [MeasurableSpace ObservablePopulation]
    [MeasurableSpace DemographicPopulation]
    (latentPopulationLaw :
      Equilibrium → Skill → Base → Measure LatentPopulation)
    (latentAccessEstimate latentNoAccessEstimate :
      Equilibrium → Skill → Base → LatentPopulation → ℝ)
    (observablePopulationLaw :
      Equilibrium → Base → Measure ObservablePopulation)
    (observableAccessEstimate observableNoAccessEstimate :
      Equilibrium → Base → ObservablePopulation → ℝ)
    (demographicPopulationLaw :
      Equilibrium → Measure DemographicPopulation)
    (demographicAccessEstimate demographicNoAccessEstimate :
      Equilibrium → DemographicPopulation → ℝ)
    (baseOnlyLaw : Equilibrium → Base → Measure ℝ)
    (fullFeatureLaw : Equilibrium → Base → Test → Measure ℝ) :
    LG21SourceLawPolicySurface Skill Base Test (Measure ℝ) where
  Equilibrium := Equilibrium
  latentAccessLaw := fun e skill base ↦
    Measure.map (latentAccessEstimate e skill base)
      (latentPopulationLaw e skill base)
  latentNoAccessLaw := fun e skill base ↦
    Measure.map (latentNoAccessEstimate e skill base)
      (latentPopulationLaw e skill base)
  observableAccessLaw := fun e base ↦
    Measure.map (observableAccessEstimate e base)
      (observablePopulationLaw e base)
  observableNoAccessLaw := fun e base ↦
    Measure.map (observableNoAccessEstimate e base)
      (observablePopulationLaw e base)
  demographicAccessLaw := fun e ↦
    Measure.map (demographicAccessEstimate e)
      (demographicPopulationLaw e)
  demographicNoAccessLaw := fun e ↦
    Measure.map (demographicNoAccessEstimate e)
      (demographicPopulationLaw e)
  baseOnlyLaw := baseOnlyLaw
  fullFeatureLaw := fullFeatureLaw

/--
Strict strategic dominance of the actual induced laws at the latent,
observable, and demographic levels implies failure of all three source
fairness notions.
-/
theorem paper_theorem3_1_all_fairness_fail_of_strict_dominance_law_identities
    {Skill Base Test : Type*}
    {LatentPopulation ObservablePopulation DemographicPopulation : Type*}
    [MeasurableSpace LatentPopulation]
    [MeasurableSpace ObservablePopulation]
    [MeasurableSpace DemographicPopulation]
    {S : LG21SourceLawPolicySurface Skill Base Test (Measure ℝ)}
    (eLat : S.Equilibrium) (skill : Skill) (baseLat : Base)
    (latentPopulationLaw : Measure LatentPopulation)
    (latentAccessEstimate latentNoAccessEstimate : LatentPopulation → ℝ)
    (hLatentAccessLaw :
      S.latentAccessLaw eLat skill baseLat =
        Measure.map latentAccessEstimate latentPopulationLaw)
    (hLatentNoAccessLaw :
      S.latentNoAccessLaw eLat skill baseLat =
        Measure.map latentNoAccessEstimate latentPopulationLaw)
    (hLatentDominance :
      LG21StrictFirstOrderEstimateDominates latentPopulationLaw
        latentAccessEstimate latentNoAccessEstimate)
    (eObs : S.Equilibrium) (baseObs : Base)
    (observablePopulationLaw : Measure ObservablePopulation)
    (observableAccessEstimate observableNoAccessEstimate :
      ObservablePopulation → ℝ)
    (hObservableAccessLaw :
      S.observableAccessLaw eObs baseObs =
        Measure.map observableAccessEstimate observablePopulationLaw)
    (hObservableNoAccessLaw :
      S.observableNoAccessLaw eObs baseObs =
        Measure.map observableNoAccessEstimate observablePopulationLaw)
    (hObservableDominance :
      LG21StrictFirstOrderEstimateDominates observablePopulationLaw
        observableAccessEstimate observableNoAccessEstimate)
    (eDemo : S.Equilibrium)
    (demographicPopulationLaw : Measure DemographicPopulation)
    (demographicAccessEstimate demographicNoAccessEstimate :
      DemographicPopulation → ℝ)
    (hDemographicAccessLaw :
      S.demographicAccessLaw eDemo =
        Measure.map demographicAccessEstimate demographicPopulationLaw)
    (hDemographicNoAccessLaw :
      S.demographicNoAccessLaw eDemo =
        Measure.map demographicNoAccessEstimate demographicPopulationLaw)
    (hDemographicDominance :
      LG21StrictFirstOrderEstimateDominates demographicPopulationLaw
        demographicAccessEstimate demographicNoAccessEstimate) :
    ¬ lg21SourceLawLatentSkillFair S ∧
      ¬ lg21SourceLawObservablyFair S ∧
        ¬ lg21SourceLawDemographicallyFair S := by
  refine ⟨?_, ?_, ?_⟩
  · intro hfair
    apply hLatentDominance.2
    rw [← hLatentAccessLaw, ← hLatentNoAccessLaw]
    exact hfair eLat skill baseLat
  · intro hfair
    apply hObservableDominance.2
    rw [← hObservableAccessLaw, ← hObservableNoAccessLaw]
    exact hfair eObs baseObs
  · intro hfair
    apply hDemographicDominance.2
    rw [← hDemographicAccessLaw, ← hDemographicNoAccessLaw]
    exact hfair eDemo

/--
Constructor-specialized form: when the source surface is built directly from
the induced strategic pushforwards, strict dominance witnesses at the three
aggregation levels immediately give the full Theorem 3.1 unfairness
conclusion.
-/
theorem paper_theorem3_1_induced_strategic_estimate_law_surface_not_fair
    {Equilibrium Skill Base Test : Type*}
    {LatentPopulation ObservablePopulation DemographicPopulation : Type*}
    [MeasurableSpace LatentPopulation]
    [MeasurableSpace ObservablePopulation]
    [MeasurableSpace DemographicPopulation]
    (latentPopulationLaw :
      Equilibrium → Skill → Base → Measure LatentPopulation)
    (latentAccessEstimate latentNoAccessEstimate :
      Equilibrium → Skill → Base → LatentPopulation → ℝ)
    (observablePopulationLaw :
      Equilibrium → Base → Measure ObservablePopulation)
    (observableAccessEstimate observableNoAccessEstimate :
      Equilibrium → Base → ObservablePopulation → ℝ)
    (demographicPopulationLaw :
      Equilibrium → Measure DemographicPopulation)
    (demographicAccessEstimate demographicNoAccessEstimate :
      Equilibrium → DemographicPopulation → ℝ)
    (baseOnlyLaw : Equilibrium → Base → Measure ℝ)
    (fullFeatureLaw : Equilibrium → Base → Test → Measure ℝ)
    (eLat : Equilibrium) (skill : Skill) (baseLat : Base)
    (hLatentDominance :
      LG21StrictFirstOrderEstimateDominates
        (latentPopulationLaw eLat skill baseLat)
        (latentAccessEstimate eLat skill baseLat)
        (latentNoAccessEstimate eLat skill baseLat))
    (eObs : Equilibrium) (baseObs : Base)
    (hObservableDominance :
      LG21StrictFirstOrderEstimateDominates
        (observablePopulationLaw eObs baseObs)
        (observableAccessEstimate eObs baseObs)
        (observableNoAccessEstimate eObs baseObs))
    (eDemo : Equilibrium)
    (hDemographicDominance :
      LG21StrictFirstOrderEstimateDominates
        (demographicPopulationLaw eDemo)
        (demographicAccessEstimate eDemo)
        (demographicNoAccessEstimate eDemo)) :
    let S :=
      lg21InducedStrategicEstimateLawSurface
        latentPopulationLaw latentAccessEstimate latentNoAccessEstimate
        observablePopulationLaw observableAccessEstimate
        observableNoAccessEstimate demographicPopulationLaw
        demographicAccessEstimate demographicNoAccessEstimate
        baseOnlyLaw fullFeatureLaw
    ¬ lg21SourceLawLatentSkillFair S ∧
      ¬ lg21SourceLawObservablyFair S ∧
        ¬ lg21SourceLawDemographicallyFair S := by
  dsimp only
  exact
    paper_theorem3_1_all_fairness_fail_of_strict_dominance_law_identities
      eLat skill baseLat
      (latentPopulationLaw eLat skill baseLat)
      (latentAccessEstimate eLat skill baseLat)
      (latentNoAccessEstimate eLat skill baseLat)
      rfl rfl hLatentDominance
      eObs baseObs
      (observablePopulationLaw eObs baseObs)
      (observableAccessEstimate eObs baseObs)
      (observableNoAccessEstimate eObs baseObs)
      rfl rfl hObservableDominance
      eDemo (demographicPopulationLaw eDemo)
      (demographicAccessEstimate eDemo)
      (demographicNoAccessEstimate eDemo)
      rfl rfl hDemographicDominance

/-! ## Arbitrary supplied sequential equilibria -/

/--
In every supplied optional-reporting equilibrium, the realized chosen estimate
weakly dominates the no-access estimate.  Positive mass of strictly profitable
reports makes the dominance strict.
-/
theorem paper_theorem3_1_arbitrary_optional_equilibrium_strategic_dominance
    {Skill Base Test : Type*} [MeasurableSpace Test]
    {E : LG21OptionalSequentialEquilibriumData Skill Base Test}
    (hEq : lg21OptionalSequentialEquilibrium E)
    (skill : Skill) (base : Base)
    (hContinuationMeasurable :
      Measurable (lg21OptionalSequentialContinuationPayoff E base))
    (hstrict :
      E.testLaw skill base
          {test |
            E.noReportPayoff base <
              lg21OptionalSequentialContinuationPayoff E base test} ≠ 0) :
    LG21StrictFirstOrderEstimateDominates
      (E.testLaw skill base)
      (lg21OptionalSequentialContinuationPayoff E base)
      (fun _test => E.noReportPayoff base) := by
  letI : IsProbabilityMeasure (E.testLaw skill base) :=
    E.testLaw_isProbability skill base
  apply paper_theorem3_1_strategic_advantage_strict_dominance
  · exact hContinuationMeasurable
  · fun_prop
  · exact E.continuationPayoff_integrable skill base
  · exact integrable_const (E.noReportPayoff base)
  · intro test
    by_cases hreport : E.reportDecision base test = true
    · have hbest :=
        (lg21OptionalSequentialEquilibrium_report_bestResponse hEq base).1
          test hreport
      simpa [lg21OptionalSequentialContinuationPayoff, hreport] using hbest
    · have hreportFalse : E.reportDecision base test = false := by
        cases hdecision : E.reportDecision base test
        · rfl
        · exact False.elim (hreport hdecision)
      simp [lg21OptionalSequentialContinuationPayoff, hreportFalse]
  · exact hstrict

/-- Expected estimate actually chosen in the report-required regime. -/
def lg21ReportRequiredChosenExpectedEstimate
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  if E.takeDecision skill base then
    lg21ReportRequiredSequentialTakeExpectedPayoff E skill base
  else
    E.noReportPayoff base

/--
For report-required testing, every supplied equilibrium weakly improves each
type's ex-ante expected estimate, and positive-mass strict improvement gives
strict dominance of those expected estimates.  This theorem deliberately does
not claim pointwise dominance after the Gaussian test noise is realized.
-/
theorem paper_theorem3_1_arbitrary_report_required_equilibrium_expected_strategic_dominance
    {Skill Base Test : Type*}
    [MeasurableSpace Skill] [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (skillLaw : Measure Skill) [IsFiniteMeasure skillLaw] (base : Base)
    (hChosenMeasurable :
      Measurable (fun skill =>
        lg21ReportRequiredChosenExpectedEstimate E skill base))
    (hChosenIntegrable :
      Integrable
        (fun skill =>
          lg21ReportRequiredChosenExpectedEstimate E skill base)
        skillLaw)
    (hstrict :
      skillLaw
          {skill |
            E.noReportPayoff base <
              lg21ReportRequiredChosenExpectedEstimate E skill base} ≠ 0) :
    LG21StrictFirstOrderEstimateDominates
      skillLaw
      (fun skill =>
        lg21ReportRequiredChosenExpectedEstimate E skill base)
      (fun _skill => E.noReportPayoff base) := by
  apply paper_theorem3_1_strategic_advantage_strict_dominance
  · exact hChosenMeasurable
  · fun_prop
  · exact hChosenIntegrable
  · exact integrable_const (E.noReportPayoff base)
  · intro skill
    by_cases htake : E.takeDecision skill base = true
    · have hbest :=
        (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq base).1
          skill htake
      simpa [lg21ReportRequiredChosenExpectedEstimate, htake] using hbest
    · have htakeFalse : E.takeDecision skill base = false := by
        cases hdecision : E.takeDecision skill base
        · rfl
        · exact False.elim (htake hdecision)
      simp [lg21ReportRequiredChosenExpectedEstimate, htakeFalse]
  · exact hstrict

end

end LG21TestOptionalPolicies
