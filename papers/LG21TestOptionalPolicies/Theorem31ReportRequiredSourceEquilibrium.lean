import LG21TestOptionalPolicies.Theorem32AEEquilibrium

/-!
# Theorem 3.1 Report-Required Source-Equilibrium Bridges

This module isolates the report-required analogue of the optional-reporting
source-equilibrium bridge.  It records the pointwise feasibility blocker for
the old report-required base-source data, then uses the repaired a.e.
diagonal-law source model with an endogenous no-take payoff to package the
paper-facing Theorem 3.1 route.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory

/--
Source equilibrium for the current report-required base-source data forces the
chosen taking bit to equal the reporting bit at every information set.  This is
the exact feasibility condition that blocks a nontrivial skill-threshold taking
rule from being packaged as a concrete Definition 1 source equilibrium.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_chosen_feasible_eq_of_sourceEquilibrium
    {Base Test : Type*}
    {takeDecision : ℝ → Base → Bool}
    {reportDecision : Base → Test → Bool}
    {testBenefitProb : Base → ℝ → ℝ}
    {estimationConsistent : Prop}
    (hEq :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision testBenefitProb estimationConsistent)) :
    ∀ skill base test, takeDecision skill base = reportDecision base test := by
  intro skill base test
  let E : LG21SourceEquilibriumData ℝ Base Test :=
    lg21ReportRequiredBaseSourceEquilibriumData
      takeDecision reportDecision testBenefitProb estimationConsistent
  let info : LG21AccessStudentInfo ℝ Base Test :=
    { skill := skill, base := base, test := test }
  have hfeasible :=
    lg21SourceEquilibrium_feasible (E := E) hEq info
  have hrequired :
      LG21AccessAction.reportRequiredAfterTaking
        (LG21AccessStudentInfo.chosenAction takeDecision reportDecision info) :=
    (LG21AccessAction.reportRequiredAfterTaking_feasible_iff
      (LG21AccessStudentInfo.chosenAction takeDecision reportDecision info)).1
      hfeasible
  simpa [E, info, lg21ReportRequiredBaseSourceEquilibriumData,
    LG21SourceEquilibriumData.toEquilibriumData,
    LG21AccessStudentInfo.chosenAction,
    LG21AccessAction.reportRequiredAfterTaking] using hrequired

/--
A nontrivial skill-indexed taking rule cannot satisfy the current
report-required feasibility shape with a report decision that does not see
skill.
-/
theorem lg21ReportRequired_nontrivial_taking_rule_not_report_required_feasible
    {Base Test : Type*} [Nonempty Base] [Nonempty Test]
    (takes : Base → ℝ → Prop)
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (htake_each : ∀ base, ∃ skill, takes base skill)
    (hnottake_each : ∀ base, ∃ skill, ¬ takes base skill)
    (hdecision :
      ∀ base skill, takeDecision skill base = true ↔ takes base skill) :
    ¬ ∀ skill base test, takeDecision skill base = reportDecision base test := by
  intro hfeasible
  classical
  let base : Base := Classical.choice inferInstance
  let test : Test := Classical.choice inferInstance
  rcases htake_each base with ⟨skillTake, htake⟩
  rcases hnottake_each base with ⟨skillNoTake, hnottake⟩
  have htake_true : takeDecision skillTake base = true :=
    (hdecision base skillTake).2 htake
  have hnottake_false : takeDecision skillNoTake base = false := by
    cases htake_decision : takeDecision skillNoTake base
    · rfl
    · exact False.elim (hnottake ((hdecision base skillNoTake).1 htake_decision))
  have hsame : takeDecision skillTake base = takeDecision skillNoTake base := by
    trans reportDecision base test
    · exact hfeasible skillTake base test
    · exact (hfeasible skillNoTake base test).symm
  simp [htake_true, hnottake_false] at hsame

/--
Report-required Theorem 3.1 no-take-mixture feasibility blocker.  The closed
no-take-mixture theorem still supplies the paper's nontrivial lower-cutoff
taking witness, but no current `lg21ReportRequiredBaseSourceEquilibriumData`
source equilibrium can realize that witness as its taking decision when the
test space is nonempty.
-/
theorem paper_theorem3_1_report_required_source_equilibrium_blocker_of_no_take_mixture
    {Base Test : Type*} [Nonempty Base] [Nonempty Test]
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        (∀ base,
          lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
              (fun qBar : ℝ =>
                intercept base + slope base *
                  standardGaussianLowerTailMean (skillLaw base) qBar)
              (takeCutoff base) =
            intercept base + slope base * takeCutoff base) ∧
          (∀ base skill,
            W.takes base skill ↔
              lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                  (fun qBar : ℝ =>
                    intercept base + slope base *
                      standardGaussianLowerTailMean (skillLaw base) qBar)
                  (takeCutoff base) ≤
                intercept base + slope base * skill) ∧
            (∀ base, ∃ qBar : ℝ,
              ∀ skill : ℝ, W.takes base skill ↔ qBar ≤ skill) ∧
              ∀ (testBenefitProb : Base → ℝ → ℝ)
                (takeDecision : ℝ → Base → Bool)
                (reportDecision : Base → Test → Bool)
                (estimationConsistent : Prop),
                (∀ base skill,
                  takeDecision skill base = true ↔ W.takes base skill) →
                ¬ lg21SourceEquilibrium
                    (lg21ReportRequiredBaseSourceEquilibriumData
                      takeDecision reportDecision testBenefitProb
                      estimationConsistent) := by
  rcases
      paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture
        intercept slope hslope accessFraction baseOnlyEstimate skillLaw
        hC_nonneg hC_lt_one with
    ⟨W, takeCutoff, hindiff, htakes, hthreshold⟩
  refine ⟨W, takeCutoff, hindiff, htakes, hthreshold, ?_⟩
  intro testBenefitProb takeDecision reportDecision estimationConsistent
    hdecision hEq
  have hfeasible :
      ∀ skill base test,
        takeDecision skill base = reportDecision base test :=
    lg21ReportRequiredBaseSourceEquilibriumData_chosen_feasible_eq_of_sourceEquilibrium
      (takeDecision := takeDecision)
      (reportDecision := reportDecision)
      (testBenefitProb := testBenefitProb)
      (estimationConsistent := estimationConsistent)
      hEq
  exact
    lg21ReportRequired_nontrivial_taking_rule_not_report_required_feasible
      (takes := W.takes)
      (takeDecision := takeDecision)
      (reportDecision := reportDecision)
      (htake_each :=
        paper_theorem3_1_report_required_take_at_each_base_of_source_witness W)
      (hnottake_each :=
        paper_theorem3_1_report_required_no_take_at_each_base_of_source_witness W)
      hdecision hfeasible

/--
Generalized report-required base-indexed source game with an explicit
base-indexed no-take payoff.  The older `lg21ReportRequiredBaseSourceEquilibriumData`
specializes this idea to a constant outside payoff `1 / 2`; Theorem 3.1's
no-take-mixture fixed point needs the outside payoff to be the endogenous
no-take estimate.
-/
def lg21ReportRequiredBaseNoTakeSourceEquilibriumData
    {Base Test : Type*}
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (takeEstimate : Base → ℝ → ℝ)
    (noTakeEstimate : Base → ℝ)
    (estimationConsistent : Prop) :
    LG21SourceEquilibriumData ℝ Base Test where
  requirement := LG21AccessAction.reportRequiredAfterTaking
  takeDecision := takeDecision
  reportDecision := reportDecision
  payoff := fun info action =>
    if action.takesTest then
      takeEstimate info.base info.skill
    else
      noTakeEstimate info.base
  estimationConsistent := estimationConsistent

/--
Best-response consequence for the generalized report-required source model:
for almost every realized type that takes the test, the endogenous no-take
payoff is weakly below the taking payoff.
-/
theorem lg21ReportRequiredBaseNoTakeSourceEquilibriumData_noTake_le_take_ae
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (takeEstimate : Base → ℝ → ℝ)
    (noTakeEstimate : Base → ℝ)
    (estimationConsistent : Prop)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
          takeDecision reportDecision takeEstimate noTakeEstimate
          estimationConsistent)) :
    ∀ᵐ info ∂μ,
      takeDecision info.skill info.base = true →
        noTakeEstimate info.base ≤ takeEstimate info.base info.skill := by
  have hbest :=
    lg21SourceEquilibriumAE_best_response_ae (E :=
      lg21ReportRequiredBaseNoTakeSourceEquilibriumData
        takeDecision reportDecision takeEstimate noTakeEstimate
        estimationConsistent) hEq
  exact hbest.mono fun info hbest_info htake => by
    have h :=
      hbest_info LG21AccessAction.noTake
        LG21AccessAction.noTake_reportRequiredAfterTaking_feasible
    simpa [lg21ReportRequiredBaseNoTakeSourceEquilibriumData,
      LG21SourceEquilibriumData.toEquilibriumData,
      LG21AccessStudentInfo.chosenAction, htake] using h

/--
Affine specialization for the generalized report-required source model: if the
endogenous no-take payoff is the same affine payoff evaluated at `actorMean`,
then almost every test taker has skill at least `actorMean`.
-/
theorem lg21ReportRequiredBaseNoTakeSourceEquilibriumData_actorMean_le_taker_skill_ae
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (baseTerm base + signalWeight base * actor) / denom base)
          (fun base =>
            (baseTerm base + signalWeight base * actorMean base) /
              denom base)
          estimationConsistent)) :
    ∀ᵐ info ∂μ,
      takeDecision info.skill info.base = true →
        actorMean info.base ≤ info.skill := by
  have hle :=
    lg21ReportRequiredBaseNoTakeSourceEquilibriumData_noTake_le_take_ae
      μ takeDecision reportDecision
      (fun base actor =>
        (baseTerm base + signalWeight base * actor) / denom base)
      (fun base =>
        (baseTerm base + signalWeight base * actorMean base) / denom base)
      estimationConsistent hEq
  exact hle.mono fun info hle_info htake => by
    have hmul :=
      mul_le_mul_of_nonneg_right (hle_info htake)
        (le_of_lt (hdenom info.base))
    have hsimpl :
        baseTerm info.base + signalWeight info.base * actorMean info.base ≤
          baseTerm info.base + signalWeight info.base * info.skill := by
      simpa [div_mul_cancel₀ _ (ne_of_gt (hdenom info.base))] using hmul
    nlinarith [hweight info.base]

/--
The generalized report-required affine a.e. source equilibrium is impossible
if the realized information law assigns positive mass to takers below the
endogenous no-take-payoff mean.
-/
theorem lg21ReportRequiredBaseNoTakeSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_taker_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hpos :
      0 < μ {info |
        takeDecision info.skill info.base = true ∧
          info.skill < actorMean info.base})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (baseTerm base + signalWeight base * actor) / denom base)
          (fun base =>
            (baseTerm base + signalWeight base * actorMean base) /
              denom base)
          estimationConsistent)) : False :=
  lg21_actorMean_le_taker_skill_ae_contradicts_positive_below_mean_taker_mass
    μ takeDecision actorMean
    (lg21ReportRequiredBaseNoTakeSourceEquilibriumData_actorMean_le_taker_skill_ae
      μ takeDecision reportDecision estimationConsistent baseTerm
      signalWeight denom actorMean hweight hdenom hEq)
    hpos

/--
A.e. constructor for the generalized report-required source model.  Feasibility
only has to hold on the realized information law; the binary take/no-take best
response can still be checked pointwise at each base profile.
-/
theorem lg21SourceEquilibriumAE_of_base_report_required_no_take_binary_choice
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (takeEstimate : Base → ℝ → ℝ)
    (noTakeEstimate : Base → ℝ)
    (estimationConsistent : Prop)
    (hchosen_feasible_ae :
      ∀ᵐ info ∂μ, takeDecision info.skill info.base =
        reportDecision info.base info.test)
    (hbest :
      ∀ base,
        lg21NoProfitableBinaryChoiceDeviation
          (fun skill : ℝ => takeDecision skill base = true)
          (takeEstimate base) (fun _skill : ℝ => noTakeEstimate base))
    (hconsistent : estimationConsistent) :
    lg21SourceEquilibriumAE μ
      (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
        takeDecision reportDecision takeEstimate noTakeEstimate
        estimationConsistent) := by
  refine ⟨?_, ?_, hconsistent⟩
  · exact hchosen_feasible_ae.mono fun info hchosen_feasible => by
      apply (LG21AccessAction.reportRequiredAfterTaking_feasible_iff _).2
      simpa [lg21ReportRequiredBaseNoTakeSourceEquilibriumData,
        LG21SourceEquilibriumData.toEquilibriumData,
        LG21AccessStudentInfo.chosenAction,
        LG21AccessAction.reportRequiredAfterTaking] using hchosen_feasible
  · exact Filter.Eventually.of_forall fun info action _haction => by
      dsimp [lg21ReportRequiredBaseNoTakeSourceEquilibriumData,
        LG21SourceEquilibriumData.toEquilibriumData,
        LG21AccessStudentInfo.chosenAction]
      by_cases hchosen : takeDecision info.skill info.base = true
      · by_cases haction : action.takesTest = true
        · simp [hchosen, haction]
        · simpa [hchosen, haction] using
            (hbest info.base).1 info.skill hchosen
      · by_cases haction : action.takesTest = true
        · simpa [hchosen, haction] using
            (hbest info.base).2 info.skill hchosen
        · simp [hchosen, haction]

/--
Report-required Theorem 3.1 source-equilibrium bridge, repaired as an a.e.
source equilibrium on the realized diagonal information law `test = skill`.
The no-take-mixture fixed point supplies the endogenous no-take payoff and the
finite lower skill cutoff; feasibility is required only on the realized
report-required information states.
-/
theorem paper_theorem3_1_report_required_source_equilibriumAE_of_no_take_mixture
    {Base : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        ∃ takeDecision : ℝ → Base → Bool,
          ∃ reportDecision : Base → ℝ → Bool,
          let takeEstimate : Base → ℝ → ℝ := fun base skill =>
            intercept base + slope base * skill
          let noTakeEstimate : Base → ℝ := fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
              (fun qBar : ℝ =>
                intercept base + slope base *
                  standardGaussianLowerTailMean (skillLaw base) qBar)
              (takeCutoff base)
          lg21SourceEquilibriumAE μ
            (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
              takeDecision reportDecision takeEstimate noTakeEstimate
              estimationConsistent) ∧
            (∀ base,
              noTakeEstimate base = takeEstimate base (takeCutoff base)) ∧
              (∀ base skill,
                takeDecision skill base = true ↔
                  noTakeEstimate base ≤ takeEstimate base skill) ∧
                (∀ base, ∃ skill, takeDecision skill base = true) ∧
                  (∀ base, ∃ skill, takeDecision skill base = false) ∧
                    (∀ base, ∃ qBar : ℝ,
                      ∀ skill : ℝ,
                        takeDecision skill base = true ↔ qBar ≤ skill) := by
  rcases
      paper_theorem3_1_report_required_affine_source_witness_of_no_take_mixture
        intercept slope hslope accessFraction baseOnlyEstimate skillLaw
        hC_nonneg hC_lt_one with
    ⟨W, takeCutoff, hindiff, htakes, hthreshold⟩
  classical
  let takeEstimate : Base → ℝ → ℝ := fun base skill =>
    intercept base + slope base * skill
  let noTakeEstimate : Base → ℝ := fun base =>
    lg21OptionalNoReportMixtureEstimate
      (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
      (fun qBar : ℝ =>
        intercept base + slope base *
          standardGaussianLowerTailMean (skillLaw base) qBar)
      (takeCutoff base)
  let takeDecision : ℝ → Base → Bool := fun skill base =>
    if W.takes base skill then true else false
  let reportDecision : Base → ℝ → Bool := fun base test =>
    takeDecision test base
  refine ⟨W, takeCutoff, takeDecision, reportDecision, ?_⟩
  have hdecision_iff_takes :
      ∀ base skill, takeDecision skill base = true ↔ W.takes base skill := by
    intro base skill
    dsimp [takeDecision]
    by_cases h : W.takes base skill
    · simp [h]
    · simp [h]
  have hdecision_payoff :
      ∀ base skill,
        takeDecision skill base = true ↔
          noTakeEstimate base ≤ takeEstimate base skill := by
    intro base skill
    exact (hdecision_iff_takes base skill).trans (htakes base skill)
  have hchosen_feasible_ae :
      ∀ᵐ info ∂μ, takeDecision info.skill info.base =
        reportDecision info.base info.test :=
    hdiag.mono fun info hinfo => by
      dsimp [reportDecision]
      rw [hinfo]
  have hbest :
      ∀ base,
        lg21NoProfitableBinaryChoiceDeviation
          (fun skill : ℝ => takeDecision skill base = true)
          (takeEstimate base) (fun _skill : ℝ => noTakeEstimate base) := by
    intro base
    exact
      AppliedModelingLib.noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
        (fun skill => hdecision_payoff base skill)
  have hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
          takeDecision reportDecision takeEstimate noTakeEstimate
          estimationConsistent) :=
    lg21SourceEquilibriumAE_of_base_report_required_no_take_binary_choice
      μ takeDecision reportDecision takeEstimate noTakeEstimate
      estimationConsistent hchosen_feasible_ae hbest hconsistent
  have htake_each :
      ∀ base, ∃ skill, takeDecision skill base = true := by
    intro base
    rcases
        paper_theorem3_1_report_required_take_at_each_base_of_source_witness
          W base with
      ⟨skill, hskill⟩
    exact ⟨skill, (hdecision_iff_takes base skill).2 hskill⟩
  have hnottake_each :
      ∀ base, ∃ skill, takeDecision skill base = false := by
    intro base
    rcases
        paper_theorem3_1_report_required_no_take_at_each_base_of_source_witness
          W base with
      ⟨skill, hskill⟩
    refine ⟨skill, ?_⟩
    cases hdec : takeDecision skill base
    · rfl
    · exact False.elim (hskill ((hdecision_iff_takes base skill).1 hdec))
  have hdecision_threshold :
      ∀ base, ∃ qBar : ℝ,
        ∀ skill : ℝ, takeDecision skill base = true ↔ qBar ≤ skill := by
    intro base
    rcases hthreshold base with ⟨qBar, hqBar⟩
    refine ⟨qBar, ?_⟩
    intro skill
    exact (hdecision_iff_takes base skill).trans (hqBar skill)
  exact
    ⟨hEq, hindiff, hdecision_payoff, htake_each, hnottake_each,
      hdecision_threshold⟩

/--
Report-required Theorem 3.1 a.e. source-equilibrium bridge in the paper's
Bayesian-optimal threshold notation.  This rewrites the closed affine
no-take-mixture source equilibrium through an abstract `PBO` identified with
the affine skill estimate and exposes the taking decision as a `PBO` threshold
rule.
-/
theorem paper_theorem3_1_report_required_pbo_threshold_source_equilibriumAE_of_no_take_mixture
    {Base : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (PBO : Base → ℝ → ℝ)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        ∃ pboThreshold : Base → ℝ,
          ∃ takeDecision : ℝ → Base → Bool,
            ∃ reportDecision : Base → ℝ → Bool,
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                PBO base skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                  (fun qBar : ℝ =>
                    PBO base (standardGaussianLowerTailMean (skillLaw base) qBar))
                  (takeCutoff base)
              lg21SourceEquilibriumAE μ
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  estimationConsistent) ∧
                (∀ base, pboThreshold base = noTakeEstimate base) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      pboThreshold base ≤ PBO base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔ qBar ≤ skill) := by
  rcases
      paper_theorem3_1_report_required_source_equilibriumAE_of_no_take_mixture
        μ intercept slope hslope accessFraction baseOnlyEstimate skillLaw
        hC_nonneg hC_lt_one estimationConsistent hconsistent hdiag with
    ⟨W, takeCutoff, takeDecision, reportDecision, hEq, hindiff, hdecision,
      htake_each, hnottake_each, hthreshold⟩
  let pboThreshold : Base → ℝ := fun base =>
    lg21OptionalNoReportMixtureEstimate
      (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
      (fun qBar : ℝ =>
        PBO base (standardGaussianLowerTailMean (skillLaw base) qBar))
      (takeCutoff base)
  refine ⟨W, takeCutoff, pboThreshold, takeDecision, reportDecision, ?_⟩
  have hEqPBO :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
          takeDecision reportDecision
          (fun base skill => PBO base skill)
          (fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
              (fun qBar : ℝ =>
                PBO base
                  (standardGaussianLowerTailMean (skillLaw base) qBar))
              (takeCutoff base))
          estimationConsistent) := by
    simpa [hPBO] using hEq
  have hthresholdPBO :
      ∀ base skill,
        takeDecision skill base = true ↔
          pboThreshold base ≤ PBO base skill := by
    intro base skill
    simpa [pboThreshold, hPBO] using hdecision base skill
  exact
    ⟨hEqPBO, (fun base => rfl), hthresholdPBO, htake_each,
      hnottake_each, hthreshold⟩

/--
Report-required Theorem 3.1 a.e. source-equilibrium bridge with the access
fraction instantiated as a finite PMF event share.  Positive complement mass at
each base profile supplies the strict mixture bound `C < 1`; the a.e.
diagonal-law premise supplies report-required feasibility on realized states.
-/
theorem paper_theorem3_1_report_required_source_equilibriumAE_of_event_share_no_take_mixture
    {Base Student : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        ∃ takeDecision : ℝ → Base → Bool,
          ∃ reportDecision : Base → ℝ → Bool,
          let accessFraction : Base → ℝ := fun base =>
            ((@lg21PMFEventShare Student _ _ (studentLaw base)
              (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
          let takeEstimate : Base → ℝ → ℝ := fun base skill =>
            intercept base + slope base * skill
          let noTakeEstimate : Base → ℝ := fun base =>
            lg21OptionalNoReportMixtureEstimate
              (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
              (fun qBar : ℝ =>
                intercept base + slope base *
                  standardGaussianLowerTailMean (skillLaw base) qBar)
              (takeCutoff base)
          lg21SourceEquilibriumAE μ
            (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
              takeDecision reportDecision takeEstimate noTakeEstimate
              estimationConsistent) ∧
            (∀ base,
              noTakeEstimate base = takeEstimate base (takeCutoff base)) ∧
              (∀ base skill,
                takeDecision skill base = true ↔
                  noTakeEstimate base ≤ takeEstimate base skill) ∧
                (∀ base, ∃ skill, takeDecision skill base = true) ∧
                  (∀ base, ∃ skill, takeDecision skill base = false) ∧
                    (∀ base, ∃ qBar : ℝ,
                      ∀ skill : ℝ,
                        takeDecision skill base = true ↔ qBar ≤ skill) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_report_required_source_equilibriumAE_of_no_take_mixture
      μ intercept slope hslope accessFraction baseOnlyEstimate skillLaw
      hC_nonneg hC_lt_one estimationConsistent hconsistent hdiag)

/--
Report-required Theorem 3.1 finite-event-share a.e. source-equilibrium bridge
in the paper's Bayesian-optimal threshold notation.
-/
theorem paper_theorem3_1_report_required_pbo_threshold_source_equilibriumAE_of_event_share_no_take_mixture
    {Base Student : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (PBO : Base → ℝ → ℝ)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
      ∃ takeCutoff : Base → ℝ,
        ∃ pboThreshold : Base → ℝ,
          ∃ takeDecision : ℝ → Base → Bool,
            ∃ reportDecision : Base → ℝ → Bool,
              let accessFraction : Base → ℝ := fun base =>
                ((@lg21PMFEventShare Student _ _ (studentLaw base)
                  (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                PBO base skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                  (fun qBar : ℝ =>
                    PBO base (standardGaussianLowerTailMean (skillLaw base) qBar))
                  (takeCutoff base)
              lg21SourceEquilibriumAE μ
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  estimationConsistent) ∧
                (∀ base, pboThreshold base = noTakeEstimate base) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      pboThreshold base ≤ PBO base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔ qBar ≤ skill) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_report_required_pbo_threshold_source_equilibriumAE_of_no_take_mixture
      (Base := Base) μ PBO intercept slope hslope hPBO accessFraction
      baseOnlyEstimate skillLaw hC_nonneg hC_lt_one estimationConsistent
      hconsistent hdiag)

/--
Report-required Theorem 3.1 Section 3 endpoint with the repaired a.e. source
equilibrium and the concrete source-shaped affine-skill posterior law surface.
The pointwise report-required source data is too strong off support; this
statement uses the realized diagonal information-law condition needed for
`Y = X` while preserving the no-take mixture cutoff and the failures of all
three fairness definitions.
-/
theorem paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
    {Base : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
        ∃ takeCutoff : Base → ℝ,
          ∃ takeDecision : ℝ → Base → Bool,
            ∃ reportDecision : Base → ℝ → Bool,
            let takeEstimate : Base → ℝ → ℝ := fun base skill =>
              intercept base + slope base * skill
            let noTakeEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                (fun qBar : ℝ =>
                  intercept base + slope base *
                    standardGaussianLowerTailMean (skillLaw base) qBar)
                (takeCutoff base)
            lg21SourceEquilibriumAE μ
              (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                takeDecision reportDecision takeEstimate noTakeEstimate
                estimationConsistent) ∧
              (∀ base,
                noTakeEstimate base = takeEstimate base (takeCutoff base)) ∧
                (∀ base skill,
                  takeDecision skill base = true ↔
                    noTakeEstimate base ≤ takeEstimate base skill) ∧
                  (∀ base, ∃ skill, takeDecision skill base = true) ∧
                    (∀ base, ∃ skill, takeDecision skill base = false) ∧
                      (∀ base, ∃ qBar : ℝ,
                        ∀ skill : ℝ,
                          takeDecision skill base = true ↔ qBar ≤ skill) ∧
                        ¬ lg21SourceLawLatentSkillFair
                          (lg21BaseMixedAffineSkillPosteriorLawSurface
                            skillGivenBase baseProfile intercept slope hslope
                            skillLaw baseOnlyEstimate) ∧
                          ¬ lg21SourceLawObservablyFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              skillGivenBase baseProfile intercept slope hslope
                              skillLaw baseOnlyEstimate) ∧
                            ¬ lg21SourceLawDemographicallyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                skillGivenBase baseProfile intercept slope
                                hslope skillLaw baseOnlyEstimate) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · rcases
        paper_theorem3_1_report_required_source_equilibriumAE_of_no_take_mixture
          μ intercept slope hslope accessFraction baseOnlyEstimate skillLaw
          hC_nonneg hC_lt_one estimationConsistent hconsistent hdiag with
      ⟨W, takeCutoff, takeDecision, reportDecision, hsource⟩
    have hfair :=
      paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
        skillGivenBase baseProfile intercept slope
        (fun base => (skillLaw base).scale)
        baseOnlyEstimate hslope
        (fun base => (skillLaw base).scale_pos)
    refine
      ⟨W, takeCutoff, takeDecision, reportDecision,
        hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2.1,
        hsource.2.2.2.2.1, hsource.2.2.2.2.2, ?_, ?_, ?_⟩
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.1
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.2.1
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.2.2

/--
Report-required Theorem 3.1 Section 3 endpoint with the repaired a.e. source
equilibrium and the access fraction instantiated as a finite event share.  This
is the concrete finite-cohort version of the no-take-mixture
source-equilibrium/law-unfairness bridge.
-/
theorem paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_event_share_no_take_mixture
    {Base Student : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
        ∃ takeCutoff : Base → ℝ,
          ∃ takeDecision : ℝ → Base → Bool,
            ∃ reportDecision : Base → ℝ → Bool,
            let accessFraction : Base → ℝ := fun base =>
              ((@lg21PMFEventShare Student _ _ (studentLaw base)
                (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
            let takeEstimate : Base → ℝ → ℝ := fun base skill =>
              intercept base + slope base * skill
            let noTakeEstimate : Base → ℝ := fun base =>
              lg21OptionalNoReportMixtureEstimate
                (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                (fun qBar : ℝ =>
                  intercept base + slope base *
                    standardGaussianLowerTailMean (skillLaw base) qBar)
                (takeCutoff base)
            lg21SourceEquilibriumAE μ
              (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                takeDecision reportDecision takeEstimate noTakeEstimate
                estimationConsistent) ∧
              (∀ base,
                noTakeEstimate base = takeEstimate base (takeCutoff base)) ∧
                (∀ base skill,
                  takeDecision skill base = true ↔
                    noTakeEstimate base ≤ takeEstimate base skill) ∧
                  (∀ base, ∃ skill, takeDecision skill base = true) ∧
                    (∀ base, ∃ skill, takeDecision skill base = false) ∧
                      (∀ base, ∃ qBar : ℝ,
                        ∀ skill : ℝ,
                          takeDecision skill base = true ↔ qBar ≤ skill) ∧
                        ¬ lg21SourceLawLatentSkillFair
                          (lg21BaseMixedAffineSkillPosteriorLawSurface
                            skillGivenBase baseProfile intercept slope hslope
                            skillLaw baseOnlyEstimate) ∧
                          ¬ lg21SourceLawObservablyFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              skillGivenBase baseProfile intercept slope hslope
                              skillLaw baseOnlyEstimate) ∧
                            ¬ lg21SourceLawDemographicallyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                skillGivenBase baseProfile intercept slope
                                hslope skillLaw baseOnlyEstimate) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
      μ skillGivenBase baseProfile intercept slope hslope accessFraction
      baseOnlyEstimate skillLaw hC_nonneg hC_lt_one
      estimationConsistent hconsistent hdiag)

/--
Report-required Theorem 3.1 Section 3 endpoint in affine-skill `P_BO`
threshold notation.  This bundles the repaired a.e. no-take-mixture source
equilibrium with the source-shaped continuous-law unfairness conclusions.
-/
theorem paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
    {Base : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (PBO : Base → ℝ → ℝ)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (accessFraction baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (hC_nonneg : ∀ base, 0 ≤ accessFraction base)
    (hC_lt_one : ∀ base, accessFraction base < 1)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
        ∃ takeCutoff : Base → ℝ,
          ∃ pboThreshold : Base → ℝ,
            ∃ takeDecision : ℝ → Base → Bool,
              ∃ reportDecision : Base → ℝ → Bool,
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                PBO base skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                  (fun qBar : ℝ =>
                    PBO base (standardGaussianLowerTailMean (skillLaw base) qBar))
                  (takeCutoff base)
              lg21SourceEquilibriumAE μ
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  estimationConsistent) ∧
                (∀ base, pboThreshold base = noTakeEstimate base) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      pboThreshold base ≤ PBO base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔ qBar ≤ skill) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              skillGivenBase baseProfile intercept slope hslope
                              skillLaw baseOnlyEstimate) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                skillGivenBase baseProfile intercept slope hslope
                                skillLaw baseOnlyEstimate) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  skillGivenBase baseProfile intercept slope
                                  hslope skillLaw baseOnlyEstimate) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · rcases
        paper_theorem3_1_report_required_pbo_threshold_source_equilibriumAE_of_no_take_mixture
          μ PBO intercept slope hslope hPBO accessFraction baseOnlyEstimate
          skillLaw hC_nonneg hC_lt_one estimationConsistent hconsistent hdiag with
      ⟨W, takeCutoff, pboThreshold, takeDecision, reportDecision, hsource⟩
    have hfair :=
      paper_theorem3_1_base_mixed_one_test_posterior_source_law_not_fair
        skillGivenBase baseProfile intercept slope
        (fun base => (skillLaw base).scale)
        baseOnlyEstimate hslope
        (fun base => (skillLaw base).scale_pos)
    refine
      ⟨W, takeCutoff, pboThreshold, takeDecision, reportDecision,
        hsource.1, hsource.2.1, hsource.2.2.1, hsource.2.2.2.1,
        hsource.2.2.2.2.1, hsource.2.2.2.2.2, ?_, ?_, ?_⟩
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.1
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.2.1
    · simpa [lg21BaseMixedAffineSkillPosteriorLawSurface] using hfair.2.2

/--
Report-required Theorem 3.1 Section 3 finite-event-share endpoint in
affine-skill `P_BO` threshold notation.
-/
theorem paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_event_share_no_take_mixture
    {Base Student : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Base → PMF ℝ) (baseProfile : PMF Base)
    (PBO : Base → ℝ → ℝ)
    (intercept slope : Base → ℝ) (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (studentLaw : Base → PMF Student)
    (accessEvent : Base → Student → Prop)
    (decAccessEvent : ∀ base, DecidablePred (accessEvent base))
    (hnoAccessMass :
      ∀ base, ∃ student, ¬ accessEvent base student ∧
        0 < (studentLaw base student).toReal)
    (baseOnlyEstimate : Base → ℝ)
    (skillLaw : Base → GaussianScaleLaw)
    (estimationConsistent : Prop) (hconsistent : estimationConsistent)
    (hdiag : ∀ᵐ info ∂μ, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
        ∃ takeCutoff : Base → ℝ,
          ∃ pboThreshold : Base → ℝ,
            ∃ takeDecision : ℝ → Base → Bool,
              ∃ reportDecision : Base → ℝ → Bool,
              let accessFraction : Base → ℝ := fun base =>
                ((@lg21PMFEventShare Student _ _ (studentLaw base)
                  (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                PBO base skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate base) (skillLaw base)
                  (fun qBar : ℝ =>
                    PBO base (standardGaussianLowerTailMean (skillLaw base) qBar))
                  (takeCutoff base)
              lg21SourceEquilibriumAE μ
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  estimationConsistent) ∧
                (∀ base, pboThreshold base = noTakeEstimate base) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      pboThreshold base ≤ PBO base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔ qBar ≤ skill) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              skillGivenBase baseProfile intercept slope hslope
                              skillLaw baseOnlyEstimate) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                skillGivenBase baseProfile intercept slope hslope
                                skillLaw baseOnlyEstimate) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  skillGivenBase baseProfile intercept slope
                                  hslope skillLaw baseOnlyEstimate) := by
  let accessFraction : Base → ℝ := fun base =>
    ((@lg21PMFEventShare Student _ _ (studentLaw base)
      (accessEvent base) (decAccessEvent base) : NNReal) : ℝ)
  have hC_nonneg : ∀ base, 0 ≤ accessFraction base := by
    intro base
    dsimp [accessFraction]
    exact pmfProb_nonneg (studentLaw base) (accessEvent base)
  have hC_lt_one : ∀ base, accessFraction base < 1 := by
    intro base
    rcases hnoAccessMass base with ⟨student, hnot, hmass⟩
    have hlt :
        @lg21PMFEventShare Student _ _ (studentLaw base)
            (accessEvent base) (decAccessEvent base) < 1 :=
      lg21PMFEventShare_lt_one_of_mass_not
        (studentLaw base) (accessEvent base) student hnot hmass
    exact_mod_cast hlt
  simpa [accessFraction] using
    (paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
      μ skillGivenBase baseProfile PBO intercept slope hslope hPBO
      accessFraction baseOnlyEstimate skillLaw hC_nonneg hC_lt_one
      estimationConsistent hconsistent hdiag)

/--
Every-equilibrium report-required Theorem 3.1 repaired a.e.
source-equilibrium/law-unfairness endpoint in affine-skill `P_BO` threshold
notation.
-/
theorem paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_for_every_equilibrium_of_no_take_mixture
    {Base Equilibrium : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (PBO : Equilibrium → Base → ℝ → ℝ)
    (intercept slope : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : ∀ e base skill,
      PBO e base skill = intercept e base + slope e base * skill)
    (accessFraction baseOnlyEstimate : Equilibrium → Base → ℝ)
    (skillLaw : Equilibrium → Base → GaussianScaleLaw)
    (hC_nonneg : ∀ e base, 0 ≤ accessFraction e base)
    (hC_lt_one : ∀ e base, accessFraction e base < 1)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e)
    (hdiag : ∀ e, ∀ᵐ info ∂μ e, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
          ∃ takeCutoff : Base → ℝ,
            ∃ pboThreshold : Base → ℝ,
              ∃ takeDecision : ℝ → Base → Bool,
                ∃ reportDecision : Base → ℝ → Bool,
                let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                  PBO e base skill
                let noTakeEstimate : Base → ℝ := fun base =>
                  lg21OptionalNoReportMixtureEstimate
                    (accessFraction e base) (baseOnlyEstimate e base)
                    (skillLaw e base)
                    (fun qBar : ℝ =>
                      PBO e base
                        (standardGaussianLowerTailMean
                          (skillLaw e base) qBar))
                    (takeCutoff base)
                lg21SourceEquilibriumAE (μ e)
                  (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                    takeDecision reportDecision takeEstimate noTakeEstimate
                    (estimationConsistent e)) ∧
                  (∀ base, pboThreshold base = noTakeEstimate base) ∧
                    (∀ base skill,
                      takeDecision skill base = true ↔
                        pboThreshold base ≤ PBO e base skill) ∧
                      (∀ base, ∃ skill, takeDecision skill base = true) ∧
                        (∀ base, ∃ skill, takeDecision skill base = false) ∧
                          (∀ base, ∃ qBar : ℝ,
                            ∀ skill : ℝ,
                              takeDecision skill base = true ↔ qBar ≤ skill) ∧
                            ¬ lg21SourceLawLatentSkillFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e)
                                (intercept e) (slope e) (hslope e)
                                (skillLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawObservablyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e)
                                  (intercept e) (slope e) (hslope e)
                                  (skillLaw e) (baseOnlyEstimate e)) ∧
                                ¬ lg21SourceLawDemographicallyFair
                                  (lg21BaseMixedAffineSkillPosteriorLawSurface
                                    (skillGivenBase e) (baseProfile e)
                                    (intercept e) (slope e) (hslope e)
                                    (skillLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
        (μ e) (skillGivenBase e) (baseProfile e) (PBO e)
        (intercept e) (slope e) (hslope e) (hPBO e)
        (accessFraction e) (baseOnlyEstimate e) (skillLaw e)
        (hC_nonneg e) (hC_lt_one e) (estimationConsistent e)
        (hconsistent e) (hdiag e)).2

/--
Every-equilibrium report-required Theorem 3.1 finite-event-share repaired a.e.
source-equilibrium/law-unfairness endpoint in affine-skill `P_BO` threshold
notation.
-/
theorem paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_for_every_equilibrium_of_event_share_no_take_mixture
    {Base Student Equilibrium : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (PBO : Equilibrium → Base → ℝ → ℝ)
    (intercept slope : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : ∀ e base skill,
      PBO e base skill = intercept e base + slope e base * skill)
    (studentLaw : Equilibrium → Base → PMF Student)
    (accessEvent : Equilibrium → Base → Student → Prop)
    (decAccessEvent : ∀ e base, DecidablePred (accessEvent e base))
    (hnoAccessMass :
      ∀ e base, ∃ student, ¬ accessEvent e base student ∧
        0 < (studentLaw e base student).toReal)
    (baseOnlyEstimate : Equilibrium → Base → ℝ)
    (skillLaw : Equilibrium → Base → GaussianScaleLaw)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e)
    (hdiag : ∀ e, ∀ᵐ info ∂μ e, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
          ∃ takeCutoff : Base → ℝ,
            ∃ pboThreshold : Base → ℝ,
              ∃ takeDecision : ℝ → Base → Bool,
                ∃ reportDecision : Base → ℝ → Bool,
                let accessFraction : Base → ℝ := fun base =>
                  ((@lg21PMFEventShare Student _ _ (studentLaw e base)
                    (accessEvent e base) (decAccessEvent e base) : NNReal) : ℝ)
                let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                  PBO e base skill
                let noTakeEstimate : Base → ℝ := fun base =>
                  lg21OptionalNoReportMixtureEstimate
                    (accessFraction base) (baseOnlyEstimate e base)
                    (skillLaw e base)
                    (fun qBar : ℝ =>
                      PBO e base
                        (standardGaussianLowerTailMean
                          (skillLaw e base) qBar))
                    (takeCutoff base)
                lg21SourceEquilibriumAE (μ e)
                  (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                    takeDecision reportDecision takeEstimate noTakeEstimate
                    (estimationConsistent e)) ∧
                  (∀ base, pboThreshold base = noTakeEstimate base) ∧
                    (∀ base skill,
                      takeDecision skill base = true ↔
                        pboThreshold base ≤ PBO e base skill) ∧
                      (∀ base, ∃ skill, takeDecision skill base = true) ∧
                        (∀ base, ∃ skill, takeDecision skill base = false) ∧
                          (∀ base, ∃ qBar : ℝ,
                            ∀ skill : ℝ,
                              takeDecision skill base = true ↔ qBar ≤ skill) ∧
                            ¬ lg21SourceLawLatentSkillFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e)
                                (intercept e) (slope e) (hslope e)
                                (skillLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawObservablyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e)
                                  (intercept e) (slope e) (hslope e)
                                  (skillLaw e) (baseOnlyEstimate e)) ∧
                                ¬ lg21SourceLawDemographicallyFair
                                  (lg21BaseMixedAffineSkillPosteriorLawSurface
                                    (skillGivenBase e) (baseProfile e)
                                    (intercept e) (slope e) (hslope e)
                                    (skillLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_report_required_pbo_threshold_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_event_share_no_take_mixture
        (μ e) (skillGivenBase e) (baseProfile e) (PBO e)
        (intercept e) (slope e) (hslope e) (hPBO e)
        (studentLaw e) (accessEvent e) (decAccessEvent e) (hnoAccessMass e)
        (baseOnlyEstimate e) (skillLaw e) (estimationConsistent e)
        (hconsistent e) (hdiag e)).2

/--
Every-equilibrium report-required Theorem 3.1 source-equilibrium endpoint,
using the repaired a.e. report-required source model.  For each equilibrium
index, the no-take-mixture fixed point gives a diagonal-law a.e. source
equilibrium, a nontrivial lower skill threshold for taking/reporting, and
failure of all three fairness definitions on the affine-skill posterior law
surface.
-/
theorem paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_for_every_equilibrium_of_no_take_mixture
    {Base Equilibrium : Type*} [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (intercept slope : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (accessFraction baseOnlyEstimate : Equilibrium → Base → ℝ)
    (skillLaw : Equilibrium → Base → GaussianScaleLaw)
    (hC_nonneg : ∀ e base, 0 ≤ accessFraction e base)
    (hC_lt_one : ∀ e base, accessFraction e base < 1)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e)
    (hdiag : ∀ e, ∀ᵐ info ∂μ e, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
          ∃ takeCutoff : Base → ℝ,
            ∃ takeDecision : ℝ → Base → Bool,
              ∃ reportDecision : Base → ℝ → Bool,
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                intercept e base + slope e base * skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction e base) (baseOnlyEstimate e base)
                  (skillLaw e base)
                  (fun qBar : ℝ =>
                    intercept e base + slope e base *
                      standardGaussianLowerTailMean
                        (skillLaw e base) qBar)
                  (takeCutoff base)
              lg21SourceEquilibriumAE (μ e)
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  (estimationConsistent e)) ∧
                (∀ base,
                  noTakeEstimate base = takeEstimate base
                    (takeCutoff base)) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      noTakeEstimate base ≤ takeEstimate base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔
                              qBar ≤ skill) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              (skillGivenBase e) (baseProfile e)
                              (intercept e) (slope e) (hslope e)
                              (skillLaw e) (baseOnlyEstimate e)) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e)
                                (intercept e) (slope e) (hslope e)
                                (skillLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e)
                                  (intercept e) (slope e) (hslope e)
                                  (skillLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_no_take_mixture
        (μ e) (skillGivenBase e) (baseProfile e) (intercept e)
        (slope e) (hslope e) (accessFraction e) (baseOnlyEstimate e)
        (skillLaw e) (hC_nonneg e) (hC_lt_one e)
        (estimationConsistent e) (hconsistent e) (hdiag e)).2

/--
Every-equilibrium report-required Theorem 3.1 source-equilibrium endpoint with
the access fraction instantiated as a finite event share at each
equilibrium/base profile, using the repaired a.e. diagonal source model.
-/
theorem paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_for_every_equilibrium_of_event_share_no_take_mixture
    {Base Student Equilibrium : Type*} [Fintype Student] [DecidableEq Student]
    [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base ℝ)]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base ℝ))
    (skillGivenBase : Equilibrium → Base → PMF ℝ)
    (baseProfile : Equilibrium → PMF Base)
    (intercept slope : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (studentLaw : Equilibrium → Base → PMF Student)
    (accessEvent : Equilibrium → Base → Student → Prop)
    (decAccessEvent : ∀ e base, DecidablePred (accessEvent e base))
    (hnoAccessMass :
      ∀ e base, ∃ student, ¬ accessEvent e base student ∧
        0 < (studentLaw e base student).toReal)
    (baseOnlyEstimate : Equilibrium → Base → ℝ)
    (skillLaw : Equilibrium → Base → GaussianScaleLaw)
    (estimationConsistent : Equilibrium → Prop)
    (hconsistent : ∀ e, estimationConsistent e)
    (hdiag : ∀ e, ∀ᵐ info ∂μ e, info.test = info.skill) :
    (∀ (base : Base) (test : ℝ) (action : LG21AccessAction),
      (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
        none) ∧
      ∀ e : Equilibrium,
        ∃ W : LG21ReportRequiredStrategicWithholdingSourceWitness Base,
          ∃ takeCutoff : Base → ℝ,
            ∃ takeDecision : ℝ → Base → Bool,
              ∃ reportDecision : Base → ℝ → Bool,
              let accessFraction : Base → ℝ := fun base =>
                ((@lg21PMFEventShare Student _ _ (studentLaw e base)
                  (accessEvent e base) (decAccessEvent e base) : NNReal) : ℝ)
              let takeEstimate : Base → ℝ → ℝ := fun base skill =>
                intercept e base + slope e base * skill
              let noTakeEstimate : Base → ℝ := fun base =>
                lg21OptionalNoReportMixtureEstimate
                  (accessFraction base) (baseOnlyEstimate e base)
                  (skillLaw e base)
                  (fun qBar : ℝ =>
                    intercept e base + slope e base *
                      standardGaussianLowerTailMean
                        (skillLaw e base) qBar)
                  (takeCutoff base)
              lg21SourceEquilibriumAE (μ e)
                (lg21ReportRequiredBaseNoTakeSourceEquilibriumData
                  takeDecision reportDecision takeEstimate noTakeEstimate
                  (estimationConsistent e)) ∧
                (∀ base,
                  noTakeEstimate base = takeEstimate base
                    (takeCutoff base)) ∧
                  (∀ base skill,
                    takeDecision skill base = true ↔
                      noTakeEstimate base ≤ takeEstimate base skill) ∧
                    (∀ base, ∃ skill, takeDecision skill base = true) ∧
                      (∀ base, ∃ skill, takeDecision skill base = false) ∧
                        (∀ base, ∃ qBar : ℝ,
                          ∀ skill : ℝ,
                            takeDecision skill base = true ↔
                              qBar ≤ skill) ∧
                          ¬ lg21SourceLawLatentSkillFair
                            (lg21BaseMixedAffineSkillPosteriorLawSurface
                              (skillGivenBase e) (baseProfile e)
                              (intercept e) (slope e) (hslope e)
                              (skillLaw e) (baseOnlyEstimate e)) ∧
                            ¬ lg21SourceLawObservablyFair
                              (lg21BaseMixedAffineSkillPosteriorLawSurface
                                (skillGivenBase e) (baseProfile e)
                                (intercept e) (slope e) (hslope e)
                                (skillLaw e) (baseOnlyEstimate e)) ∧
                              ¬ lg21SourceLawDemographicallyFair
                                (lg21BaseMixedAffineSkillPosteriorLawSurface
                                  (skillGivenBase e) (baseProfile e)
                                  (intercept e) (slope e) (hslope e)
                                  (skillLaw e) (baseOnlyEstimate e)) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro e
    exact
      (paper_theorem3_1_section3_report_required_source_equilibriumAE_and_base_mixed_affine_skill_posterior_law_unfair_of_event_share_no_take_mixture
        (μ e) (skillGivenBase e) (baseProfile e) (intercept e)
        (slope e) (hslope e) (studentLaw e) (accessEvent e)
        (decAccessEvent e) (hnoAccessMass e) (baseOnlyEstimate e)
        (skillLaw e) (estimationConsistent e) (hconsistent e)
        (hdiag e)).2

end

end LG21TestOptionalPolicies
