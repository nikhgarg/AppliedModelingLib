import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# LG21 equilibrium-repair scratch work

This isolated module checks whether the existing Lemma 4.1 source surfaces
are nonvacuous.  It is deliberately not a paper-facing interface.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

/-! ## The finite-threshold Lemma 4.1 surfaces are inconsistent -/

/--
More generally, an optional-reporting source equilibrium with a positive-slope
Gaussian PBO reported payoff and any finite real no-report payoff must have a
withholding score at every base profile.  Hence an all-report Lemma 4.1
conclusion cannot hold for the optional protocol merely by choosing different
finite off-path beliefs.
-/
theorem lg21_equilibrium_repair_optional_pbo_source_equilibrium_has_withholder
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Skill]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (noReportEstimate : ℝ) {estimationConsistent : Prop}
    (hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingSourceEquilibriumData
          takeDecision reportDecision
          (fun score : ℝ => M.posteriorMean (Function.update theta k score))
          noReportEstimate estimationConsistent))
    (base : Base) :
    ∃ score : ℝ, reportDecision base score = false := by
  let skill : Skill := Classical.choice inferInstance
  rcases
      (paper_theorem3_1_optional_reporting_gaussian_best_response_nontrivial
        M theta k
        (lg21NoProfitableBinaryChoiceDeviation_of_optional_reporting_source_model
          hEq skill base)).2 with
    ⟨score, hnotReport⟩
  cases hdecision : reportDecision base score
  · exact ⟨score, hdecision⟩
  · exact False.elim (hnotReport hdecision)

/--
The optional-reporting fully specified Lemma 4.1 surface cannot have a source
equilibrium.  Its existing all-report endpoint conflicts with the finite
posterior threshold at sufficiently low Gaussian scores.
-/
theorem lg21_equilibrium_repair_optional_fully_specified_no_source_equilibrium
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    [Nonempty Skill] [Nonempty Base]
    (C : GaussianLowerTailMeanCertificate)
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (scoreLaw : GaussianScaleLaw)
    (takeDecision : Skill → Base → Bool)
    {reportingBase threshold : ℝ} {estimationConsistent : Prop} :
    ¬ lg21SourceEquilibrium
      (lg21FullySpecifiedOptionalReportingSourceEquilibriumData
        C M theta k scoreLaw takeDecision
        reportingBase threshold estimationConsistent) := by
  intro hEq
  let skill : Skill := Classical.choice inferInstance
  let base : Base := Classical.choice inferInstance
  rcases paper_gaussian_posteriorMean_update_exists_below M theta k threshold with
    ⟨score, hscore⟩
  let info : LG21AccessStudentInfo Skill Base ℝ :=
    { skill := skill, base := base, test := score }
  have haction :=
    paper_lemma4_1_optional_reporting_chosen_action_take_and_report_of_fully_specified_source_model
      C M theta k scoreLaw takeDecision hEq info
  have hreport := congrArg LG21AccessAction.reportsScore haction
  change
    (if threshold ≤ M.posteriorMean (Function.update theta k score) then
      true
    else
      false) = true at hreport
  simp [not_le_of_gt hscore] at hreport

/--
The report-required-after-taking fully specified Lemma 4.1 surface also cannot
have a source equilibrium: the finite lower skill cutoff has a nontaking
type, whereas the existing endpoint derives all taking.
-/
theorem lg21_equilibrium_repair_report_required_fully_specified_no_source_equilibrium
    {Base Test : Type*} [Nonempty Base] [Nonempty Test]
    (C : GaussianLowerTailMeanCertificate)
    (api : StandardGaussianCDFAPI) (skillLaw : GaussianScaleLaw)
    (reportDecision : Base → Test → Bool)
    {qBar testScale : ℝ} (htestScale : 0 < testScale)
    {estimationConsistent : Prop} :
    ¬ lg21SourceEquilibrium
      (lg21FullySpecifiedReportRequiredSourceEquilibriumData
        C api skillLaw reportDecision qBar testScale htestScale
        estimationConsistent) := by
  intro hEq
  let base : Base := Classical.choice inferInstance
  let test : Test := Classical.choice inferInstance
  let info : LG21AccessStudentInfo ℝ Base Test :=
    { skill := qBar - 1, base := base, test := test }
  have haction :=
    paper_lemma4_1_report_required_chosen_action_take_and_report_of_fully_specified_source_model
      C api skillLaw reportDecision htestScale hEq info
  have htake := congrArg LG21AccessAction.takesTest haction
  change (if qBar ≤ qBar - 1 then true else false) = true at htake
  norm_num at htake

/-! ## A correctly timed Theorem 3.1 construction boundary -/

/--
The sequential source game has a nonvacuous all-take construction.  The
cutoff best response and the ex-ante all-take inequality are separate,
explicit obligations; the latter is where the concrete Gaussian/PBO model
must supply its integration and consistency work.
-/
theorem lg21_equilibrium_repair_optional_sequential_equilibrium_of_all_take
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (hTake : ∀ skill base, E.takeDecision skill base = true)
    (hReport :
      ∀ base test,
        E.reportDecision base test = true ↔
          E.noReportPayoff base ≤ E.reportedPayoff base test)
    (hTakePayoff :
      ∀ skill base,
        E.noReportPayoff base ≤
          lg21OptionalSequentialTakeExpectedPayoff E skill base)
    (hconsistent : E.estimationConsistent) :
    lg21OptionalSequentialEquilibrium E := by
  constructor
  · intro base
    constructor
    · intro skill _htake
      exact hTakePayoff skill base
    · intro skill hnotTake
      exact False.elim (hnotTake (hTake skill base))
  constructor
  · intro base
    exact
      AppliedModelingLib.noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
        (hReport base)
  · exact hconsistent

/--
The all-take payoff obligation follows from the pointwise cutoff best response
and the supplied continuation integrability under each probability test law.
-/
theorem lg21_equilibrium_repair_optional_sequential_take_payoff_of_cutoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (hReport :
      ∀ base test,
        E.reportDecision base test = true ↔
          E.noReportPayoff base ≤ E.reportedPayoff base test) :
    ∀ skill base,
      E.noReportPayoff base ≤
        lg21OptionalSequentialTakeExpectedPayoff E skill base := by
  intro skill base
  letI : IsProbabilityMeasure (E.testLaw skill base) :=
    E.testLaw_isProbability skill base
  have hcontInt := E.continuationPayoff_integrable skill base
  have hconstInt : Integrable (fun _test : Test => E.noReportPayoff base)
      (E.testLaw skill base) := integrable_const _
  have hpoint : ∀ test : Test,
      E.noReportPayoff base ≤
        lg21OptionalSequentialContinuationPayoff E base test := by
    intro test
    by_cases hreport : E.reportDecision base test = true
    · simpa [lg21OptionalSequentialContinuationPayoff, hreport] using
        (hReport base test).1 hreport
    · simp [lg21OptionalSequentialContinuationPayoff, hreport]
  have hint := integral_mono_ae hconstInt hcontInt
    (Filter.Eventually.of_forall hpoint)
  simpa [lg21OptionalSequentialTakeExpectedPayoff] using hint

/--
Combining the preceding two lemmas gives a correctly timed optional-reporting
equilibrium from an all-take cutoff policy.  The only unproved source-model
field is the explicitly supplied estimation-consistency certificate.
-/
theorem lg21_equilibrium_repair_optional_sequential_equilibrium_of_cutoff_all_take
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (hTake : ∀ skill base, E.takeDecision skill base = true)
    (hReport :
      ∀ base test,
        E.reportDecision base test = true ↔
          E.noReportPayoff base ≤ E.reportedPayoff base test)
    (hconsistent : E.estimationConsistent) :
    lg21OptionalSequentialEquilibrium E :=
  lg21_equilibrium_repair_optional_sequential_equilibrium_of_all_take
    E hTake hReport
    (lg21_equilibrium_repair_optional_sequential_take_payoff_of_cutoff E hReport)
    hconsistent

/--
Two optional-reporting cutoff equilibria with the same endogenous no-report
payoff and the same reported PBO payoff have identical behavioral profiles.
Thus concrete behavioral uniqueness reduces exactly to uniqueness of the
no-report fixed point, rather than to a theorem about an arbitrarily supplied
equilibrium.
-/
theorem lg21_equilibrium_repair_optional_sequential_behavioral_uniqueness_of_common_payoffs
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E₁ E₂ : LG21OptionalSequentialEquilibriumData Skill Base Test)
    (hTake₁ : ∀ skill base, E₁.takeDecision skill base = true)
    (hTake₂ : ∀ skill base, E₂.takeDecision skill base = true)
    (hReport₁ :
      ∀ base test,
        E₁.reportDecision base test = true ↔
          E₁.noReportPayoff base ≤ E₁.reportedPayoff base test)
    (hReport₂ :
      ∀ base test,
        E₂.reportDecision base test = true ↔
          E₂.noReportPayoff base ≤ E₂.reportedPayoff base test)
    (hNoReport : ∀ base, E₁.noReportPayoff base = E₂.noReportPayoff base)
    (hReported : ∀ base test,
      E₁.reportedPayoff base test = E₂.reportedPayoff base test) :
    (∀ skill base,
      E₁.takeDecision skill base = E₂.takeDecision skill base) ∧
      ∀ base test,
        E₁.reportDecision base test = E₂.reportDecision base test := by
  constructor
  · intro skill base
    exact (hTake₁ skill base).trans (hTake₂ skill base).symm
  · intro base test
    have hiff :
        E₁.reportDecision base test = true ↔
          E₂.reportDecision base test = true := by
      rw [hReport₁, hReport₂, hNoReport base, hReported base test]
    cases h₁ : E₁.reportDecision base test <;>
      cases h₂ : E₂.reportDecision base test
    · rfl
    · have : False := by simpa [h₁, h₂] using hiff
      exact False.elim this
    · have : False := by simpa [h₁, h₂] using hiff
      exact False.elim this
    · rfl

/--
The report-required sequential model similarly becomes an actual equilibrium
once its expected-payoff threshold is supplied explicitly.  In particular,
the noisy test law remains in the expectation rather than being replaced by a
diagonal `test = skill` assumption.
-/
theorem lg21_equilibrium_repair_report_required_sequential_equilibrium_of_cutoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E : LG21ReportRequiredSequentialEquilibriumData Skill Base Test)
    (hTake :
      ∀ skill base,
        E.takeDecision skill base = true ↔
          E.noReportPayoff base ≤
            lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)
    (hconsistent : E.estimationConsistent) :
    lg21ReportRequiredSequentialEquilibrium E := by
  constructor
  · intro base
    exact
      AppliedModelingLib.noProfitableBinaryChoiceDeviation_of_choice_iff_payoff_le
        (hTake · base)
  · exact hconsistent

/--
Two report-required sequential cutoff equilibria have the same taking profile
whenever their endogenous expected-payoff comparisons agree.  Proving that
comparison equality is the remaining fixed-point uniqueness obligation.
-/
theorem lg21_equilibrium_repair_report_required_sequential_behavioral_uniqueness_of_common_comparison
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (E₁ E₂ : LG21ReportRequiredSequentialEquilibriumData Skill Base Test)
    (hTake₁ :
      ∀ skill base,
        E₁.takeDecision skill base = true ↔
          E₁.noReportPayoff base ≤
            lg21ReportRequiredSequentialTakeExpectedPayoff E₁ skill base)
    (hTake₂ :
      ∀ skill base,
        E₂.takeDecision skill base = true ↔
          E₂.noReportPayoff base ≤
            lg21ReportRequiredSequentialTakeExpectedPayoff E₂ skill base)
    (hComparison : ∀ skill base,
      (E₁.noReportPayoff base ≤
          lg21ReportRequiredSequentialTakeExpectedPayoff E₁ skill base) ↔
        (E₂.noReportPayoff base ≤
          lg21ReportRequiredSequentialTakeExpectedPayoff E₂ skill base)) :
    ∀ skill base,
      E₁.takeDecision skill base = E₂.takeDecision skill base := by
  intro skill base
  have hiff :
      E₁.takeDecision skill base = true ↔
        E₂.takeDecision skill base = true :=
    (hTake₁ skill base).trans ((hComparison skill base).trans (hTake₂ skill base).symm)
  cases h₁ : E₁.takeDecision skill base <;>
    cases h₂ : E₂.takeDecision skill base
  · rfl
  · have : False := by simpa [h₁, h₂] using hiff
    exact False.elim this
  · have : False := by simpa [h₁, h₂] using hiff
    exact False.elim this
  · rfl

/-! ## A nonvacuous mandatory-access repair -/

/--
The source's third requirement protocol makes `(Y, X) = (1, 1)` the only
feasible action.  This concrete data has the on-path Gaussian PBO payoff; its
consistency field remains an explicit source-model obligation.
-/
def lg21EquilibriumRepairMandatoryAccessPBOData
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    (estimationConsistent : Prop) :
    LG21SourceEquilibriumData Skill Base ℝ where
  requirement := fun action => action = LG21AccessAction.takeAndReport
  takeDecision := fun _skill _base => true
  reportDecision := fun _base _score => true
  payoff := fun info _action =>
    M.posteriorMean (Function.update theta k info.test)
  estimationConsistent := estimationConsistent

/--
The forced-access PBO surface has an equilibrium once its explicit source
consistency obligation is discharged.  No off-path no-report payoff is needed
because that action is infeasible under this requirement policy.
-/
theorem lg21_equilibrium_repair_mandatory_access_pbo_source_equilibrium
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : GaussianOffsetSignalFamily Feature) (theta : Feature → ℝ) (k : Feature)
    {estimationConsistent : Prop} (hconsistent : estimationConsistent) :
    lg21SourceEquilibrium
      (lg21EquilibriumRepairMandatoryAccessPBOData
        (Skill := Skill) (Base := Base) M theta k estimationConsistent) := by
  rw [lg21SourceEquilibrium_iff]
  refine ⟨?_, ?_, hconsistent⟩
  · intro info
    constructor
    · intro _hreport
      rfl
    · rfl
  · intro info action hfeasible
    have haction : action = LG21AccessAction.takeAndReport := hfeasible.2
    subst haction
    rfl

/--
For the source's mandatory-given-access protocol, any two equilibria have the
same complete action profile, and that profile is `(Y, X) = (1, 1)`.
-/
theorem lg21_equilibrium_repair_mandatory_access_behavioral_uniqueness
    {Skill Base Test : Type*}
    {E₁ E₂ : LG21SourceEquilibriumData Skill Base Test}
    (hreq₁ : E₁.requirement = fun action => action = LG21AccessAction.takeAndReport)
    (hreq₂ : E₂.requirement = fun action => action = LG21AccessAction.takeAndReport)
    (hEq₁ : lg21SourceEquilibrium E₁)
    (hEq₂ : lg21SourceEquilibrium E₂) :
    ∀ info,
      LG21AccessStudentInfo.chosenAction E₁.takeDecision E₁.reportDecision info =
        LG21AccessStudentInfo.chosenAction E₂.takeDecision E₂.reportDecision info := by
  intro info
  have haction₁ := lg21SourceEquilibrium_feasible hEq₁ info
  have haction₂ := lg21SourceEquilibrium_feasible hEq₂ info
  rw [hreq₁] at haction₁
  rw [hreq₂] at haction₂
  exact haction₁.2.trans haction₂.2.symm

end

end LG21TestOptionalPolicies
