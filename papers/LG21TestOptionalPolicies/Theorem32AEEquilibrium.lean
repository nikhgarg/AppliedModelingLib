import LG21TestOptionalPolicies.MainTheorems
import AppliedModelingLib.GameTheory.Choice.EquilibriumAE
import AppliedModelingLib.Foundations.Probability.MeasureInequalities

/-!
# Theorem 3.2 Almost-Everywhere Equilibrium Seam

Measure-indexed source-equilibrium wrappers for continuous type-space arguments
in Theorem 3.2.  These avoid treating boundary or off-support types as
pointwise equilibrium obligations, while still exposing the best-response
inequalities needed on almost every realized type.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory

/-- Definition 1 source equilibrium, but with best response required `μ`-a.e. -/
def lg21SourceEquilibriumAE
    {Skill Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base Test)]
    (μ : Measure (LG21AccessStudentInfo Skill Base Test))
    (E : LG21SourceEquilibriumData Skill Base Test) : Prop := AppliedModelingLib.IsChoiceEquilibriumAE μ E.toEquilibriumData

theorem lg21SourceEquilibriumAE_feasible_ae
    {Skill Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base Test)]
    {μ : Measure (LG21AccessStudentInfo Skill Base Test)}
    {E : LG21SourceEquilibriumData Skill Base Test}
    (hEq : lg21SourceEquilibriumAE μ E) :
    ∀ᵐ info ∂μ,
      LG21AccessAction.feasible E.requirement
        (LG21AccessStudentInfo.chosenAction
          E.takeDecision E.reportDecision info) := AppliedModelingLib.isChoiceEquilibriumAE_feasible_ae hEq

theorem lg21SourceEquilibriumAE_best_response_ae
    {Skill Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base Test)]
    {μ : Measure (LG21AccessStudentInfo Skill Base Test)}
    {E : LG21SourceEquilibriumData Skill Base Test}
    (hEq : lg21SourceEquilibriumAE μ E) :
    ∀ᵐ info ∂μ, ∀ action,
      LG21AccessAction.feasible E.requirement action →
        E.payoff info action ≤
          E.payoff info
            (LG21AccessStudentInfo.chosenAction
              E.takeDecision E.reportDecision info) := AppliedModelingLib.isChoiceEquilibriumAE_best_response_ae hEq

theorem lg21SourceEquilibriumAE_estimationConsistent
    {Skill Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base Test)]
    {μ : Measure (LG21AccessStudentInfo Skill Base Test)}
    {E : LG21SourceEquilibriumData Skill Base Test}
    (hEq : lg21SourceEquilibriumAE μ E) :
    E.estimationConsistent := AppliedModelingLib.isChoiceEquilibriumAE_consistency hEq

/-- A pointwise source equilibrium implies the corresponding a.e. equilibrium. -/
theorem lg21SourceEquilibriumAE_of_sourceEquilibrium
    {Skill Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base Test)]
    {μ : Measure (LG21AccessStudentInfo Skill Base Test)}
    {E : LG21SourceEquilibriumData Skill Base Test}
    (hEq : lg21SourceEquilibrium E) :
    lg21SourceEquilibriumAE μ E := AppliedModelingLib.isChoiceEquilibriumAE_of_pointwise hEq

/--
Optional-reporting a.e. best-response consequence: for almost every realized
type that reports, withholding is not strictly better than reporting.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_noReport_le_report_ae
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (reportedEstimate : Base → ℝ → ℝ)
    (noReportEstimate : Base → ℝ)
    (estimationConsistent : Prop)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision reportedEstimate noReportEstimate
          estimationConsistent)) :
    ∀ᵐ info ∂μ,
      reportDecision info.base info.test = true →
        noReportEstimate info.base ≤ reportedEstimate info.base info.test := by
  have hbest :=
    lg21SourceEquilibriumAE_best_response_ae (E :=
      lg21OptionalReportingBaseSourceEquilibriumData
        takeDecision reportDecision reportedEstimate noReportEstimate
        estimationConsistent) hEq
  exact hbest.mono fun info hbest_info hreport => by
    have h :=
      hbest_info LG21AccessAction.takeAndWithhold
        LG21AccessAction.takeAndWithhold_optionalReporting_feasible
    simpa [lg21OptionalReportingBaseSourceEquilibriumData,
      LG21SourceEquilibriumData.toEquilibriumData,
      LG21AccessStudentInfo.chosenAction, hreport] using h

/--
Optional-reporting affine payoff specialization: if a reported payoff is a
positive-slope affine function of the realized score and the no-report payoff is
the same affine function evaluated at `actorMean`, then almost every reporter
has score at least `actorMean`.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_actorMean_le_reported_score_ae
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) :
    ∀ᵐ info ∂μ,
      reportDecision info.base info.test = true →
        actorMean info.base ≤ info.test := by
  have hle :=
    lg21OptionalReportingBaseSourceEquilibriumData_noReport_le_report_ae
      μ takeDecision reportDecision
      (fun base actor => (baseTerm base + signalWeight base * actor) /
        denom base)
      (fun base => (baseTerm base + signalWeight base * actorMean base) /
        denom base)
      estimationConsistent hEq
  exact AppliedModelingLib.ae_imp_le_of_affine_div_le_affine_div μ
    (fun info => reportDecision info.base info.test = true)
    (fun info => baseTerm info.base)
    (fun info => signalWeight info.base)
    (fun info => denom info.base)
    (fun info => actorMean info.base)
    (fun info => info.test)
    (fun info => hweight info.base)
    (fun info => hdenom info.base)
    hle

/--
Generic a.e. contradiction: an a.e. property cannot fail on a positive-measure
set.
-/
theorem lg21_ae_property_contradicts_positive_failure_mass
    {Info : Type*} [MeasurableSpace Info]
    (μ : Measure Info) (P Q : Info → Prop)
    (hAE : ∀ᵐ info ∂μ, P info)
    (hQ_bad : ∀ info, Q info → ¬ P info)
    (hpos : 0 < μ {info | Q info}) : False :=
    AppliedModelingLib.ae_property_contradicts_positive_failure_mass
      μ P Q hAE hQ_bad hpos

/-- Positive measure is monotone under set inclusion. -/
theorem lg21_measure_pos_of_subset
    {Info : Type*} [MeasurableSpace Info]
    {μ : Measure Info} {A B : Set Info}
    (hAB : A ⊆ B) (hpos : 0 < μ A) : 0 < μ B := AppliedModelingLib.measure_pos_of_subset hAB hpos

/--
Almost every reporter being above the imputed mean contradicts positive mass of
reporters strictly below that mean.
-/
theorem lg21_actorMean_le_reported_score_ae_contradicts_positive_below_mean_reporter_mass
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (reportDecision : Base → ℝ → Bool)
    (actorMean : Base → ℝ)
    (hAE :
      ∀ᵐ info ∂μ,
        reportDecision info.base info.test = true →
          actorMean info.base ≤ info.test)
    (hpos :
      0 < μ {info |
        reportDecision info.base info.test = true ∧
          info.test < actorMean info.base}) : False :=
  AppliedModelingLib.ae_imp_le_contradicts_positive_selected_lt_mass μ
    (fun info => reportDecision info.base info.test = true)
    (fun info => actorMean info.base) (fun info => info.test)
    hAE hpos

/--
Optional-reporting affine a.e. source equilibrium is impossible if the realized
information law assigns positive mass to reporters below the imputed mean.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_reporter_mass
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hpos :
      0 < μ {info |
        reportDecision info.base info.test = true ∧
          info.test < actorMean info.base})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False :=
  lg21_actorMean_le_reported_score_ae_contradicts_positive_below_mean_reporter_mass
    μ reportDecision actorMean
    (lg21OptionalReportingBaseSourceEquilibriumData_actorMean_le_reported_score_ae
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom hEq)
    hpos

/--
Optional-reporting cutoff interval version: if a positive-mass set of realized
types lies between the reporting cutoff and the imputed no-report mean, then
the affine a.e. source-equilibrium conditions are inconsistent.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_cutoff_interval_mass
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean cutoff : Base → ℝ)
    (hreports_above_cutoff :
      ∀ base score, cutoff base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hpos :
      0 < μ {info |
        cutoff info.base ≤ info.test ∧ info.test < actorMean info.base})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False := by
  have hposBelow :
      0 < μ {info |
        reportDecision info.base info.test = true ∧
          info.test < actorMean info.base} :=
    AppliedModelingLib.positive_selected_lt_mass_of_positive_lower_lt_mass
      (selected := fun info : LG21AccessStudentInfo Skill Base ℝ =>
        reportDecision info.base info.test = true)
      (lower := fun info => cutoff info.base)
      (reference := fun info => actorMean info.base)
      (value := fun info => info.test)
      (fun info hcutoff =>
        hreports_above_cutoff info.base info.test hcutoff)
      hpos
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_reporter_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom hposBelow hEq

/--
Optional-reporting base-local cutoff interval version.  A positive-mass interval
inside one base group suffices for the global a.e. instability.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_base_cutoff_interval_mass
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean cutoff : Base → ℝ)
    (base0 : Base)
    (hreports_above_cutoff :
      ∀ base score, cutoff base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hpos :
      0 < μ {info |
        info.base = base0 ∧ cutoff base0 ≤ info.test ∧
          info.test < actorMean base0})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False := by
  have hposInterval :
      0 < μ {info |
        cutoff info.base ≤ info.test ∧ info.test < actorMean info.base} :=
    lg21_measure_pos_of_subset
      (A := {info : LG21AccessStudentInfo Skill Base ℝ |
        info.base = base0 ∧ cutoff base0 ≤ info.test ∧
          info.test < actorMean base0})
      (B := {info : LG21AccessStudentInfo Skill Base ℝ |
        cutoff info.base ≤ info.test ∧ info.test < actorMean info.base})
      (fun (info : LG21AccessStudentInfo Skill Base ℝ) hinfo => by
        rcases hinfo with ⟨hbase, hcutoff, hbelow⟩
        exact ⟨by simpa [hbase], by simpa [hbase] using hbelow⟩)
      hpos
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_cutoff_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean cutoff hreports_above_cutoff hweight hdenom
      hposInterval hEq

/--
Optional-reporting Gaussian upper-tail interval version.  The interval endpoint
is the paper's Gaussian upper-tail conditional mean.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_gaussian_upper_tail_interval_mass
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (hreports_above_threshold :
      ∀ base score,
        decisionThreshold base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hpos :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False := by
  have hpos' :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test < actorMean base0} := by
    simpa [hactorMean] using hpos
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_base_cutoff_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean decisionThreshold base0 hreports_above_threshold hweight
      hdenom hpos' hEq

/--
Optional-reporting Gaussian marginal-law version.  If the base-local realized
score interval `[threshold, upper-tail mean)` has exactly its Gaussian marginal
mass, then the interval has positive mass and the a.e. source-equilibrium
conditions are inconsistent.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (hreports_above_threshold :
      ∀ base score,
        decisionThreshold base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False := by
  have hpos :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} := by
    rw [hmarginal]
    exact
      standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos
        (actorLaw base0) (decisionThreshold base0)
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_gaussian_upper_tail_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean actorLaw decisionThreshold base0 hactorMean
      hreports_above_threshold hweight hdenom hpos hEq

/--
Optional-reporting pointwise source-equilibrium version of the Gaussian
marginal-law instability.  This is the bridge for older paper wrappers that
still state Definition 1 pointwise equilibrium rather than the a.e. repaired
surface.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibrium_of_gaussian_upper_tail_marginal_interval_law
    {Skill Base : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (hreports_above_threshold :
      ∀ base score,
        decisionThreshold base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False :=
  lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
    denom actorMean actorLaw decisionThreshold base0 hactorMean
    hreports_above_threshold hweight hdenom hmarginal
    (lg21SourceEquilibriumAE_of_sourceEquilibrium (μ := μ) hEq)

/--
Optional-reporting fixed-base Gaussian score law version.  For a fixed base,
push the Gaussian score law forward to access-student information records; the
Gaussian interval mass is then derived rather than assumed.
-/
theorem lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibrium_of_single_base_gaussian_score_law
    {Skill Base : Type*}
    (skill0 : Skill)
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (hreports_above_threshold :
      ∀ base score,
        decisionThreshold base ≤ score → reportDecision base score = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          (fun base => (baseTerm base + signalWeight base * actorMean base) /
            denom base)
          estimationConsistent)) : False := by
  let upper : ℝ :=
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base0) (decisionThreshold base0)
  let infoOfScore : ℝ → LG21AccessStudentInfo Skill Base ℝ :=
    fun score => { skill := skill0, base := base0, test := score }
  letI : MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ) :=
    MeasurableSpace.map infoOfScore (inferInstance : MeasurableSpace ℝ)
  let μ : Measure (LG21AccessStudentInfo Skill Base ℝ) :=
    Measure.map infoOfScore (actorLaw base0).toMeasure
  have hinfo_meas : Measurable infoOfScore :=
    Measurable.of_comap_le MeasurableSpace.comap_map_le
  have hset_meas :
      MeasurableSet
        {info : LG21AccessStudentInfo Skill Base ℝ |
          info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
            info.test < upper} := by
    change
      MeasurableSet[MeasurableSpace.map infoOfScore
        (inferInstance : MeasurableSpace ℝ)]
        {info : LG21AccessStudentInfo Skill Base ℝ |
          info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
            info.test < upper}
    rw [MeasurableSpace.map_def]
    have hpre :
        infoOfScore ⁻¹'
          {info : LG21AccessStudentInfo Skill Base ℝ |
            info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
              info.test < upper} =
            Set.Ico (decisionThreshold base0) upper := by
      ext score
      simp [infoOfScore, upper, Set.mem_Ico]
    rw [hpre]
    exact measurableSet_Ico
  have hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))) := by
    change
      μ {info : LG21AccessStudentInfo Skill Base ℝ |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test < upper} =
        (actorLaw base0).toMeasure (Set.Ico (decisionThreshold base0) upper)
    dsimp [μ]
    rw [Measure.map_apply hinfo_meas hset_meas]
    congr 1
    ext score
    simp [infoOfScore, upper, Set.mem_Ico]
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibrium_of_gaussian_upper_tail_marginal_interval_law
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean actorLaw decisionThreshold base0 hactorMean
      hreports_above_threshold hweight hdenom hmarginal hEq

/--
Optional-reporting source-shaped Gaussian posterior payoff version of the
fixed-base Gaussian score-law contradiction.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_not_sourceEquilibrium_of_single_base_gaussian_score_law
    {Feature Skill Base : Type*} [Fintype Feature] [DecidableEq Feature]
    (skill0 : Skill)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hthreshold :
      ∀ base score, reportDecision base score = true ↔
        decisionThreshold base ≤ score)
    (hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base) (decisionThreshold base))))
          estimationConsistent)) : False := by
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  have hEqAffine :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actor) / 1)
          (fun base =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actorMean base) / 1)
          estimationConsistent) := by
    have hreported_eq :
        (fun base actor =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actor) / 1) =
          (fun base actor =>
            (M base).posteriorMean
              (Function.update (theta base) k actor)) := by
      funext base actor
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k actor).symm
    have hnoReport_eq :
        (fun base =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actorMean base) / 1) =
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base) (decisionThreshold base)))) := by
      funext base
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k (actorMean base)).symm
    rw [hreported_eq, hnoReport_eq]
    exact hEq
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibrium_of_single_base_gaussian_score_law
      skill0 takeDecision reportDecision estimationConsistent
      (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
      (fun base => (M base).centeredFamily.signalWeight k)
      (fun _base => (1 : ℝ)) actorMean actorLaw decisionThreshold base0
      (by intro base; rfl)
      (fun base score hscore => (hthreshold base score).2 hscore)
      (fun base => (M base).centeredFamily.signalWeight_pos k)
      (fun _base => by norm_num) hEqAffine

/--
Optional-reporting indexed source-shaped Gaussian posterior payoff version:
over nonempty equilibrium, skill, and base domains, the upper-tail source
equilibrium hypotheses are inconsistent.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_family_not_sourceEquilibrium_of_nonempty
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Nonempty Skill] [Nonempty Base] [Nonempty Equilibrium]
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Equilibrium → Skill → Base → Bool)
    (reportDecision : Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (decisionThreshold : Equilibrium → Base → ℝ)
    (hthreshold :
      ∀ e base score, reportDecision e base score = true ↔
        decisionThreshold e base ≤ score)
    (hEq :
      ∀ e,
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base) (decisionThreshold e base))))
            (estimationConsistent e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  exact
    lg21OptionalReportingGaussianPosteriorPBO_not_sourceEquilibrium_of_single_base_gaussian_score_law
      (Classical.choice (inferInstance : Nonempty Skill))
      M theta k (takeDecision e0) (reportDecision e0)
      (estimationConsistent e0) (actorLaw e0) (decisionThreshold e0)
      (Classical.choice (inferInstance : Nonempty Base))
      (hthreshold e0) (hEq e0)

/--
Report-required a.e. best-response consequence: for almost every realized type
that takes the test, not taking is not strictly better than taking/reporting.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_noTake_le_take_ae
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (testBenefitProb : Base → ℝ → ℝ)
    (estimationConsistent : Prop)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision testBenefitProb estimationConsistent)) :
    ∀ᵐ info ∂μ,
      takeDecision info.skill info.base = true →
        (1 / 2 : ℝ) ≤ testBenefitProb info.base info.skill := by
  have hbest :=
    lg21SourceEquilibriumAE_best_response_ae (E :=
      lg21ReportRequiredBaseSourceEquilibriumData
        takeDecision reportDecision testBenefitProb estimationConsistent) hEq
  exact hbest.mono fun info hbest_info htake => by
    have h :=
      hbest_info LG21AccessAction.noTake
        LG21AccessAction.noTake_reportRequiredAfterTaking_feasible
    simpa [lg21ReportRequiredBaseSourceEquilibriumData,
      LG21SourceEquilibriumData.toEquilibriumData,
      LG21AccessStudentInfo.chosenAction, htake] using h

/--
Report-required affine payoff specialization: if taking payoff is a
positive-slope affine function of skill and the outside payoff equals that
affine payoff at `actorMean`, then almost every test taker has skill at least
`actorMean`.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_actorMean_le_taker_skill_ae
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) :
    ∀ᵐ info ∂μ,
      takeDecision info.skill info.base = true →
        actorMean info.base ≤ info.skill := by
  have hle :=
    lg21ReportRequiredBaseSourceEquilibriumData_noTake_le_take_ae
      μ takeDecision reportDecision
      (fun base actor => (baseTerm base + signalWeight base * actor) /
        denom base)
      estimationConsistent hEq
  have hle_affine :
      ∀ᵐ info ∂μ,
        takeDecision info.skill info.base = true →
        (baseTerm info.base + signalWeight info.base * actorMean info.base) /
            denom info.base ≤
          (baseTerm info.base + signalWeight info.base * info.skill) /
            denom info.base :=
    hle.mono fun info hle_info htake => by
      simpa [houtside info.base] using hle_info htake
  exact AppliedModelingLib.ae_imp_le_of_affine_div_le_affine_div μ
    (fun info => takeDecision info.skill info.base = true)
    (fun info => baseTerm info.base)
    (fun info => signalWeight info.base)
    (fun info => denom info.base)
    (fun info => actorMean info.base)
    (fun info => info.skill)
    (fun info => hweight info.base)
    (fun info => hdenom info.base)
    hle_affine

/--
Almost every test taker being above the imputed mean contradicts positive mass
of test takers strictly below that mean.
-/
theorem lg21_actorMean_le_taker_skill_ae_contradicts_positive_below_mean_taker_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (actorMean : Base → ℝ)
    (hAE :
      ∀ᵐ info ∂μ,
        takeDecision info.skill info.base = true →
          actorMean info.base ≤ info.skill)
    (hpos :
      0 < μ {info |
        takeDecision info.skill info.base = true ∧
          info.skill < actorMean info.base}) : False :=
  AppliedModelingLib.ae_imp_le_contradicts_positive_selected_lt_mass μ
    (fun info => takeDecision info.skill info.base = true)
    (fun info => actorMean info.base) (fun info => info.skill)
    hAE hpos

/--
Report-required affine a.e. source equilibrium is impossible if the realized
information law assigns positive mass to takers below the imputed mean.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_taker_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hpos :
      0 < μ {info |
        takeDecision info.skill info.base = true ∧
          info.skill < actorMean info.base})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False :=
  lg21_actorMean_le_taker_skill_ae_contradicts_positive_below_mean_taker_mass
    μ takeDecision actorMean
    (lg21ReportRequiredBaseSourceEquilibriumData_actorMean_le_taker_skill_ae
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom houtside hEq)
    hpos

/--
Report-required cutoff interval version: positive mass between the taking
cutoff and the imputed outside-option mean contradicts the affine a.e. source
equilibrium conditions.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_cutoff_interval_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean cutoff : Base → ℝ)
    (htakes_above_cutoff :
      ∀ base skill, cutoff base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hpos :
      0 < μ {info |
        cutoff info.base ≤ info.skill ∧ info.skill < actorMean info.base})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False := by
  have hposBelow :
      0 < μ {info |
        takeDecision info.skill info.base = true ∧
          info.skill < actorMean info.base} :=
    AppliedModelingLib.positive_selected_lt_mass_of_positive_lower_lt_mass
      (selected := fun info : LG21AccessStudentInfo ℝ Base Test =>
        takeDecision info.skill info.base = true)
      (lower := fun info => cutoff info.base)
      (reference := fun info => actorMean info.base)
      (value := fun info => info.skill)
      (fun info hcutoff =>
        htakes_above_cutoff info.base info.skill hcutoff)
      hpos
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_taker_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom houtside hposBelow hEq

/--
Report-required base-local cutoff interval version.  A positive-mass interval
inside one base group suffices for the global a.e. instability.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_base_cutoff_interval_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean cutoff : Base → ℝ)
    (base0 : Base)
    (htakes_above_cutoff :
      ∀ base skill, cutoff base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hpos :
      0 < μ {info |
        info.base = base0 ∧ cutoff base0 ≤ info.skill ∧
          info.skill < actorMean base0})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False := by
  have hposInterval :
      0 < μ {info |
        cutoff info.base ≤ info.skill ∧ info.skill < actorMean info.base} :=
    lg21_measure_pos_of_subset
      (A := {info : LG21AccessStudentInfo ℝ Base Test |
        info.base = base0 ∧ cutoff base0 ≤ info.skill ∧
          info.skill < actorMean base0})
      (B := {info : LG21AccessStudentInfo ℝ Base Test |
        cutoff info.base ≤ info.skill ∧ info.skill < actorMean info.base})
      (fun (info : LG21AccessStudentInfo ℝ Base Test) hinfo => by
        rcases hinfo with ⟨hbase, hcutoff, hbelow⟩
        exact ⟨by simpa [hbase], by simpa [hbase] using hbelow⟩)
      hpos
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_cutoff_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean cutoff htakes_above_cutoff hweight hdenom houtside
      hposInterval hEq

/--
Report-required Gaussian upper-tail interval version.  The interval endpoint is
the paper's Gaussian upper-tail conditional mean.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_gaussian_upper_tail_interval_mass
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (htakes_above_threshold :
      ∀ base skill,
        decisionThreshold base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hpos :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)})
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False := by
  have hpos' :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill < actorMean base0} := by
    simpa [hactorMean] using hpos
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_base_cutoff_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean decisionThreshold base0 htakes_above_threshold hweight
      hdenom houtside hpos' hEq

/--
Report-required Gaussian marginal-law version.  If the base-local realized
skill interval `[threshold, upper-tail mean)` has exactly its Gaussian marginal
mass, then the interval has positive mass and the a.e. source-equilibrium
conditions are inconsistent.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (htakes_above_threshold :
      ∀ base skill,
        decisionThreshold base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False := by
  have hpos :
      0 < μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} := by
    rw [hmarginal]
    exact
      standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos
        (actorLaw base0) (decisionThreshold base0)
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_gaussian_upper_tail_interval_mass
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean actorLaw decisionThreshold base0 hactorMean
      htakes_above_threshold hweight hdenom houtside hpos hEq

/--
Report-required pointwise source-equilibrium version of the Gaussian
marginal-law instability.  This is the bridge for older paper wrappers that
still state Definition 1 pointwise equilibrium rather than the a.e. repaired
surface.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibrium_of_gaussian_upper_tail_marginal_interval_law
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (htakes_above_threshold :
      ∀ base skill,
        decisionThreshold base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False :=
  lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
    denom actorMean actorLaw decisionThreshold base0 hactorMean
    htakes_above_threshold hweight hdenom houtside hmarginal
    (lg21SourceEquilibriumAE_of_sourceEquilibrium (μ := μ) hEq)

/--
Report-required fixed-base Gaussian skill law version.  For a fixed base, push
the Gaussian skill law forward to access-student information records; the
Gaussian interval mass is then derived rather than assumed.
-/
theorem lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibrium_of_single_base_gaussian_skill_law
    {Base Test : Type*}
    (test0 : Test)
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (baseTerm signalWeight denom actorMean : Base → ℝ)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base))
    (htakes_above_threshold :
      ∀ base skill,
        decisionThreshold base ≤ skill → takeDecision skill base = true)
    (hweight : ∀ base, 0 < signalWeight base)
    (hdenom : ∀ base, 0 < denom base)
    (houtside :
      ∀ base, (1 / 2 : ℝ) =
        (baseTerm base + signalWeight base * actorMean base) / denom base)
    (hEq :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor => (baseTerm base + signalWeight base * actor) /
            denom base)
          estimationConsistent)) : False := by
  let upper : ℝ :=
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base0) (decisionThreshold base0)
  let infoOfSkill : ℝ → LG21AccessStudentInfo ℝ Base Test :=
    fun skill => { skill := skill, base := base0, test := test0 }
  letI : MeasurableSpace (LG21AccessStudentInfo ℝ Base Test) :=
    MeasurableSpace.map infoOfSkill (inferInstance : MeasurableSpace ℝ)
  let μ : Measure (LG21AccessStudentInfo ℝ Base Test) :=
    Measure.map infoOfSkill (actorLaw base0).toMeasure
  have hinfo_meas : Measurable infoOfSkill :=
    Measurable.of_comap_le MeasurableSpace.comap_map_le
  have hset_meas :
      MeasurableSet
        {info : LG21AccessStudentInfo ℝ Base Test |
          info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
            info.skill < upper} := by
    change
      MeasurableSet[MeasurableSpace.map infoOfSkill
        (inferInstance : MeasurableSpace ℝ)]
        {info : LG21AccessStudentInfo ℝ Base Test |
          info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
            info.skill < upper}
    rw [MeasurableSpace.map_def]
    have hpre :
        infoOfSkill ⁻¹'
          {info : LG21AccessStudentInfo ℝ Base Test |
            info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
              info.skill < upper} =
            Set.Ico (decisionThreshold base0) upper := by
      ext skill
      simp [infoOfSkill, upper, Set.mem_Ico]
    rw [hpre]
    exact measurableSet_Ico
  have hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))) := by
    change
      μ {info : LG21AccessStudentInfo ℝ Base Test |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill < upper} =
        (actorLaw base0).toMeasure (Set.Ico (decisionThreshold base0) upper)
    dsimp [μ]
    rw [Measure.map_apply hinfo_meas hset_meas]
    congr 1
    ext skill
    simp [infoOfSkill, upper, Set.mem_Ico]
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibrium_of_gaussian_upper_tail_marginal_interval_law
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean actorLaw decisionThreshold base0 hactorMean
      htakes_above_threshold hweight hdenom houtside hmarginal hEq

/--
Report-required source-shaped unit-centered affine payoff version of the
fixed-base Gaussian skill-law contradiction.
-/
theorem lg21ReportRequiredUnitCenteredPBO_not_sourceEquilibrium_of_single_base_gaussian_skill_law
    {Base Test : Type*}
    (test0 : Test)
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (htakes_above_threshold :
      ∀ base skill, decisionThreshold base ≤ skill →
        takeDecision skill base = true)
    (hEq :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw base) (decisionThreshold base)) +
                actor)
          estimationConsistent)) : False := by
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  have hEqAffine :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (((1 / 2 : ℝ) - actorMean base) + 1 * actor) / 1)
          estimationConsistent) := by
    simpa [actorMean, div_one] using hEq
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibrium_of_single_base_gaussian_skill_law
      test0 takeDecision reportDecision estimationConsistent
      (fun base => (1 / 2 : ℝ) - actorMean base)
      (fun _base => (1 : ℝ)) (fun _base => (1 : ℝ))
      actorMean actorLaw decisionThreshold base0
      (by intro base; rfl) htakes_above_threshold
      (fun _base => by norm_num) (fun _base => by norm_num)
      (fun base => by simp [actorMean]) hEqAffine

/--
Report-required indexed source-shaped unit-centered payoff version: over
nonempty equilibrium, base, and test domains, the upper-tail source equilibrium
hypotheses are inconsistent.
-/
theorem lg21ReportRequiredUnitCenteredPBO_family_not_sourceEquilibrium_of_nonempty
    {Base Test Equilibrium : Type*}
    [Nonempty Base] [Nonempty Test] [Nonempty Equilibrium]
    (takeDecision : Equilibrium → ℝ → Base → Bool)
    (reportDecision : Equilibrium → Base → Test → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (decisionThreshold : Equilibrium → Base → ℝ)
    (htakes_above_threshold :
      ∀ e base skill, decisionThreshold e base ≤ skill →
        takeDecision e skill base = true)
    (hEq :
      ∀ e,
        lg21SourceEquilibrium
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base) (decisionThreshold e base)) +
                  actor)
            (estimationConsistent e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  exact
    lg21ReportRequiredUnitCenteredPBO_not_sourceEquilibrium_of_single_base_gaussian_skill_law
      (Classical.choice (inferInstance : Nonempty Test))
      (takeDecision e0) (reportDecision e0) (estimationConsistent e0)
      (actorLaw e0) (decisionThreshold e0)
      (Classical.choice (inferInstance : Nonempty Base))
      (htakes_above_threshold e0) (hEq e0)

/--
Optional-reporting paper-threshold version: the paper's Gaussian posterior
`P_BO` threshold rule induces the score cutoff used by the source-shaped
Gaussian posterior contradiction.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_threshold_family_not_sourceEquilibrium_of_nonempty
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Nonempty Skill] [Nonempty Base] [Nonempty Equilibrium]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Equilibrium → Skill → Base → Bool)
    (reportDecision : Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hEq :
      ∀ e,
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e))) : False := by
  let decisionThreshold : Equilibrium → Base → ℝ :=
    lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
  have hthreshold :
      ∀ e base actor, reportDecision e base actor = true ↔
        decisionThreshold e base ≤ actor := by
    intro e base actor
    calc
      reportDecision e base actor = true ↔
          pboThreshold e base ≤
            PBO base (Function.update (theta base) k actor) :=
        hreportPBO e base actor
      _ ↔ decisionThreshold e base ≤ actor := by
        simpa [decisionThreshold] using
          (lg21GaussianPosteriorMeanPBO_threshold_iff_cutoff
            PBO M theta k pboThreshold hPBO e base actor)
  have hEq' :
      ∀ e,
        lg21SourceEquilibrium
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base) (decisionThreshold e base))))
            (estimationConsistent e)) := by
    intro e
    simpa [decisionThreshold] using hEq e
  exact
    lg21OptionalReportingGaussianPosteriorPBO_family_not_sourceEquilibrium_of_nonempty
      M theta k takeDecision reportDecision estimationConsistent actorLaw
      decisionThreshold hthreshold hEq'

/--
Report-required paper-threshold version: an affine-skill `P_BO` threshold rule
induces the skill cutoff used by the source-shaped unit-centered contradiction.
-/
theorem lg21ReportRequiredAffineSkillPBO_threshold_family_not_sourceEquilibrium_of_nonempty
    {Base Test Equilibrium : Type*}
    [Nonempty Base] [Nonempty Test] [Nonempty Equilibrium]
    (PBO : Equilibrium → Base → ℝ → ℝ)
    (takeDecision : Equilibrium → ℝ → Base → Bool)
    (reportDecision : Equilibrium → Base → Test → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hEq :
      ∀ e,
        lg21SourceEquilibrium
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e))) : False := by
  let decisionThreshold : Equilibrium → Base → ℝ :=
    lg21AffineSkillPBOCutoff intercept slope pboThreshold
  have htakes_above_threshold :
      ∀ e base skill, decisionThreshold e base ≤ skill →
        takeDecision e skill base = true := by
    intro e base skill hskill
    exact
      (htakePBO e base skill).2
        ((lg21AffineSkillPBO_threshold_iff_cutoff
          PBO intercept slope pboThreshold hslope hPBO e base skill).mpr
          (by simpa [decisionThreshold] using hskill))
  have hEq' :
      ∀ e,
        lg21SourceEquilibrium
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base) (decisionThreshold e base)) +
                  actor)
            (estimationConsistent e)) := by
    intro e
    simpa [decisionThreshold] using hEq e
  exact
    lg21ReportRequiredUnitCenteredPBO_family_not_sourceEquilibrium_of_nonempty
      takeDecision reportDecision estimationConsistent actorLaw decisionThreshold
      htakes_above_threshold hEq'

/--
Optional-reporting a.e. paper-threshold family version: a Gaussian posterior
`P_BO` threshold rule, the corresponding Gaussian marginal interval law, and an
a.e. source equilibrium are jointly inconsistent.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    [Nonempty Base] [Nonempty Equilibrium]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Equilibrium → Skill → Base → Bool)
    (reportDecision : Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hmarginal :
      ∀ e base0,
        μ e {info |
          info.base = base0 ∧
            lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base0 ≤
              info.test ∧
            info.test <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base0)} =
          (actorLaw e base0).toMeasure
            (Set.Ico
              (lg21GaussianPosteriorMeanPBOCutoff
                M theta k pboThreshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base0))))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  let base0 : Base := Classical.choice (inferInstance : Nonempty Base)
  let decisionThreshold : Equilibrium → Base → ℝ :=
    lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw e0 base) (decisionThreshold e0 base)
  have hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e0 base) (decisionThreshold e0 base) := by
    intro base
    rfl
  have hthreshold :
      ∀ e base actor, reportDecision e base actor = true ↔
        decisionThreshold e base ≤ actor := by
    intro e base actor
    calc
      reportDecision e base actor = true ↔
          pboThreshold e base ≤
            PBO base (Function.update (theta base) k actor) :=
        hreportPBO e base actor
      _ ↔ decisionThreshold e base ≤ actor := by
        simpa [decisionThreshold] using
          (lg21GaussianPosteriorMeanPBO_threshold_iff_cutoff
            PBO M theta k pboThreshold hPBO e base actor)
  have hEqAffine :
      lg21SourceEquilibriumAE (μ e0)
        (lg21OptionalReportingBaseSourceEquilibriumData
          (takeDecision e0) (reportDecision e0)
          (fun base actor =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actor) / 1)
          (fun base =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actorMean base) / 1)
          (estimationConsistent e0)) := by
    have hreported_eq :
        (fun base actor =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actor) / 1) =
          (fun base actor =>
            (M base).posteriorMean
              (Function.update (theta base) k actor)) := by
      funext base actor
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k actor).symm
    have hnoReport_eq :
        (fun base =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actorMean base) / 1) =
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e0 base) (decisionThreshold e0 base)))) := by
      funext base
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k (actorMean base)).symm
    rw [hreported_eq, hnoReport_eq]
    exact hEq e0
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (μ e0) (takeDecision e0) (reportDecision e0)
      (estimationConsistent e0)
      (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
      (fun base => (M base).centeredFamily.signalWeight k)
      (fun _base => (1 : ℝ)) actorMean (actorLaw e0)
      (decisionThreshold e0) base0 hactorMean
      (fun base score hscore => (hthreshold e0 base score).2 hscore)
      (fun base => (M base).centeredFamily.signalWeight_pos k)
      (fun _base => by norm_num)
      (by simpa [decisionThreshold, base0] using hmarginal e0 base0)
      hEqAffine

/--
Report-required a.e. paper-threshold family version: an affine-skill `P_BO`
threshold rule, the corresponding Gaussian marginal interval law, and an a.e.
source equilibrium are jointly inconsistent.
-/
theorem lg21ReportRequiredAffineSkillPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Base Test Equilibrium : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    [Nonempty Base] [Nonempty Equilibrium]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (PBO : Equilibrium → Base → ℝ → ℝ)
    (takeDecision : Equilibrium → ℝ → Base → Bool)
    (reportDecision : Equilibrium → Base → Test → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hmarginal :
      ∀ e base0,
        μ e {info |
          info.base = base0 ∧
            lg21AffineSkillPBOCutoff intercept slope pboThreshold e base0 ≤
              info.skill ∧
            info.skill <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0)
                (lg21AffineSkillPBOCutoff
                  intercept slope pboThreshold e base0)} =
          (actorLaw e base0).toMeasure
            (Set.Ico
              (lg21AffineSkillPBOCutoff
                intercept slope pboThreshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0)
                (lg21AffineSkillPBOCutoff
                  intercept slope pboThreshold e base0))))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  let base0 : Base := Classical.choice (inferInstance : Nonempty Base)
  let decisionThreshold : Equilibrium → Base → ℝ :=
    lg21AffineSkillPBOCutoff intercept slope pboThreshold
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw e0 base) (decisionThreshold e0 base)
  have hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e0 base) (decisionThreshold e0 base) := by
    intro base
    rfl
  have htakes_above_threshold :
      ∀ base skill, decisionThreshold e0 base ≤ skill →
        takeDecision e0 skill base = true := by
    intro base skill hskill
    exact
      (htakePBO e0 base skill).2
        ((lg21AffineSkillPBO_threshold_iff_cutoff
          PBO intercept slope pboThreshold hslope hPBO e0 base skill).mpr
          (by simpa [decisionThreshold] using hskill))
  have houtside :
      ∀ base, (1 / 2 : ℝ) =
        (((1 / 2 : ℝ) - actorMean base) + (1 : ℝ) * actorMean base) / 1 := by
    intro base
    ring
  have hEqAffine :
      lg21SourceEquilibriumAE (μ e0)
        (lg21ReportRequiredBaseSourceEquilibriumData
          (takeDecision e0) (reportDecision e0)
          (fun base actor =>
            (((1 / 2 : ℝ) - actorMean base) + (1 : ℝ) * actor) / 1)
          (estimationConsistent e0)) := by
    simpa [actorMean, decisionThreshold, div_one] using hEq e0
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (μ e0) (takeDecision e0) (reportDecision e0)
      (estimationConsistent e0)
      (fun base => (1 / 2 : ℝ) - actorMean base)
      (fun _base => (1 : ℝ)) (fun _base => (1 : ℝ)) actorMean
      (actorLaw e0) (decisionThreshold e0) base0 hactorMean
      htakes_above_threshold (fun _base => by norm_num)
      (fun _base => by norm_num) houtside
      (by simpa [decisionThreshold, base0] using hmarginal e0 base0)
      hEqAffine

/--
Optional-reporting realized type law used by finite-base Theorem 3.2 a.e.
routes: for each base profile, push the Gaussian reported-score law into
student-information records, then sum over the finite base domain.
-/
noncomputable def lg21OptionalReportingGaussianInfoMeasure
    {Skill Base : Type*} [Fintype Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (referenceSkill : Base → Skill)
    (actorLaw : Base → GaussianScaleLaw) :
    Measure (LG21AccessStudentInfo Skill Base ℝ) :=
  ∑ base : Base,
    Measure.map
      (fun score : ℝ =>
        ({ skill := referenceSkill base, base := base, test := score } :
          LG21AccessStudentInfo Skill Base ℝ))
      (actorLaw base).toMeasure

/--
The optional-reporting finite-base Gaussian information law has the intended
base-local Gaussian interval marginal.
-/
theorem lg21OptionalReportingGaussianInfoMeasure_marginal_interval
    {Skill Base : Type*} [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (referenceSkill : Base → Skill)
    (actorLaw : Base → GaussianScaleLaw)
    (lo hi : Base → ℝ) (base0 : Base)
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun score : ℝ =>
            ({ skill := referenceSkill base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)))
    (htarget_meas :
      MeasurableSet
        {info : LG21AccessStudentInfo Skill Base ℝ |
          info.base = base0 ∧ lo base0 ≤ info.test ∧ info.test < hi base0}) :
    lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw
        {info |
          info.base = base0 ∧ lo base0 ≤ info.test ∧ info.test < hi base0} =
      (actorLaw base0).toMeasure (Set.Ico (lo base0) (hi base0)) := by
  classical
  dsimp [lg21OptionalReportingGaussianInfoMeasure]
  rw [Measure.finset_sum_apply
    (I := (Finset.univ : Finset Base))
    (μ := fun base : Base =>
      (Measure.map
        (fun score : ℝ =>
          ({ skill := referenceSkill base, base := base, test := score } :
            LG21AccessStudentInfo Skill Base ℝ))
        (actorLaw base).toMeasure :
        Measure (LG21AccessStudentInfo Skill Base ℝ)))]
  trans
    ((Measure.map
      (fun score : ℝ =>
        ({ skill := referenceSkill base0, base := base0, test := score } :
          LG21AccessStudentInfo Skill Base ℝ))
      (actorLaw base0).toMeasure)
      {info : LG21AccessStudentInfo Skill Base ℝ |
        info.base = base0 ∧ lo base0 ≤ info.test ∧ info.test < hi base0})
  · refine
      Fintype.sum_eq_single (M := ENNReal)
        (f := fun base : Base =>
          (Measure.map
            (fun score : ℝ =>
              ({ skill := referenceSkill base, base := base, test := score } :
                LG21AccessStudentInfo Skill Base ℝ))
            (actorLaw base).toMeasure)
            {info : LG21AccessStudentInfo Skill Base ℝ |
              info.base = base0 ∧ lo base0 ≤ info.test ∧
                info.test < hi base0})
        base0 ?_
    intro base hne
    change
      (Measure.map
        (fun score : ℝ =>
          ({ skill := referenceSkill base, base := base, test := score } :
            LG21AccessStudentInfo Skill Base ℝ))
        (actorLaw base).toMeasure)
        {info : LG21AccessStudentInfo Skill Base ℝ |
          info.base = base0 ∧ lo base0 ≤ info.test ∧
            info.test < hi base0} = 0
    rw [Measure.map_apply (hinfo_meas base) htarget_meas]
    have hpre :
        (fun score : ℝ =>
            ({ skill := referenceSkill base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)) ⁻¹'
            {info : LG21AccessStudentInfo Skill Base ℝ |
              info.base = base0 ∧ lo base0 ≤ info.test ∧ info.test < hi base0} =
          (∅ : Set ℝ) := by
      ext score
      simp [hne]
    rw [hpre]
    simp
  · rw [Measure.map_apply (hinfo_meas base0) htarget_meas]
    congr 1
    ext score
    simp [Set.mem_Ico]

/--
Report-required realized type law used by finite-base Theorem 3.2 a.e. routes:
for each base profile, push the Gaussian latent-skill law into
student-information records, then sum over the finite base domain.
-/
noncomputable def lg21ReportRequiredGaussianInfoMeasure
    {Base Test : Type*} [Fintype Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (referenceTest : Base → Test)
    (actorLaw : Base → GaussianScaleLaw) :
    Measure (LG21AccessStudentInfo ℝ Base Test) :=
  ∑ base : Base,
    Measure.map
      (fun skill : ℝ =>
        ({ skill := skill, base := base, test := referenceTest base } :
          LG21AccessStudentInfo ℝ Base Test))
      (actorLaw base).toMeasure

/--
The report-required finite-base Gaussian information law has the intended
base-local Gaussian interval marginal.
-/
theorem lg21ReportRequiredGaussianInfoMeasure_marginal_interval
    {Base Test : Type*} [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (referenceTest : Base → Test)
    (actorLaw : Base → GaussianScaleLaw)
    (lo hi : Base → ℝ) (base0 : Base)
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest base } :
              LG21AccessStudentInfo ℝ Base Test)))
    (htarget_meas :
      MeasurableSet
        {info : LG21AccessStudentInfo ℝ Base Test |
          info.base = base0 ∧ lo base0 ≤ info.skill ∧ info.skill < hi base0}) :
    lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw
        {info |
          info.base = base0 ∧ lo base0 ≤ info.skill ∧ info.skill < hi base0} =
      (actorLaw base0).toMeasure (Set.Ico (lo base0) (hi base0)) := by
  classical
  dsimp [lg21ReportRequiredGaussianInfoMeasure]
  rw [Measure.finset_sum_apply
    (I := (Finset.univ : Finset Base))
    (μ := fun base : Base =>
      (Measure.map
        (fun skill : ℝ =>
          ({ skill := skill, base := base, test := referenceTest base } :
            LG21AccessStudentInfo ℝ Base Test))
        (actorLaw base).toMeasure :
        Measure (LG21AccessStudentInfo ℝ Base Test)))]
  trans
    ((Measure.map
      (fun skill : ℝ =>
        ({ skill := skill, base := base0, test := referenceTest base0 } :
          LG21AccessStudentInfo ℝ Base Test))
      (actorLaw base0).toMeasure)
      {info : LG21AccessStudentInfo ℝ Base Test |
        info.base = base0 ∧ lo base0 ≤ info.skill ∧ info.skill < hi base0})
  · refine
      Fintype.sum_eq_single (M := ENNReal)
        (f := fun base : Base =>
          (Measure.map
            (fun skill : ℝ =>
              ({ skill := skill, base := base, test := referenceTest base } :
                LG21AccessStudentInfo ℝ Base Test))
            (actorLaw base).toMeasure)
            {info : LG21AccessStudentInfo ℝ Base Test |
              info.base = base0 ∧ lo base0 ≤ info.skill ∧
                info.skill < hi base0})
        base0 ?_
    intro base hne
    change
      (Measure.map
        (fun skill : ℝ =>
          ({ skill := skill, base := base, test := referenceTest base } :
            LG21AccessStudentInfo ℝ Base Test))
        (actorLaw base).toMeasure)
        {info : LG21AccessStudentInfo ℝ Base Test |
          info.base = base0 ∧ lo base0 ≤ info.skill ∧
            info.skill < hi base0} = 0
    rw [Measure.map_apply (hinfo_meas base) htarget_meas]
    have hpre :
        (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest base } :
              LG21AccessStudentInfo ℝ Base Test)) ⁻¹'
            {info : LG21AccessStudentInfo ℝ Base Test |
              info.base = base0 ∧ lo base0 ≤ info.skill ∧ info.skill < hi base0} =
          (∅ : Set ℝ) := by
      ext skill
      simp [hne]
    rw [hpre]
    simp
  · rw [Measure.map_apply (hinfo_meas base0) htarget_meas]
    congr 1
    ext skill
    simp [Set.mem_Ico]

/--
Optional-reporting finite-base Gaussian information law: the paper's Gaussian
posterior `P_BO` upper-tail source game is not an a.e. source equilibrium for
any single threshold profile.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_not_sourceEquilibriumAE_finite_base_gaussian_info_law
    {Feature Skill Base : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base] [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (pboThreshold : Base → ℝ)
    (referenceSkill : Base → Skill)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ base actor, reportDecision base actor = true ↔
        pboThreshold base ≤ PBO base (Function.update (theta base) k actor))
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun score : ℝ =>
            ({ skill := referenceSkill base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)))
    (hset_meas :
      ∀ base,
        MeasurableSet
          {info : LG21AccessStudentInfo Skill Base ℝ |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff
                M theta k (fun _ : PUnit => pboThreshold) PUnit.unit base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k (fun _ : PUnit => pboThreshold) PUnit.unit
                    base)})
    (hEq :
      lg21SourceEquilibriumAE
        (lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw)
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k (fun _ : PUnit => pboThreshold) PUnit.unit
                    base))))
          estimationConsistent)) :
    False := by
  let threshold : PUnit → Base → ℝ := fun _ base => pboThreshold base
  have hreport' :
      ∀ e base actor, reportDecision base actor = true ↔
        threshold e base ≤ PBO base (Function.update (theta base) k actor) := by
    intro e base actor
    simpa [threshold] using hreportPBO base actor
  have hmarginal :
      ∀ e base0,
        lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw
          {info |
            info.base = base0 ∧
              lg21GaussianPosteriorMeanPBOCutoff M theta k threshold e base0 ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base0)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k threshold e base0)} =
          (actorLaw base0).toMeasure
            (Set.Ico
              (lg21GaussianPosteriorMeanPBOCutoff
                M theta k threshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw base0)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k threshold e base0))) := by
    intro e base0
    exact
      lg21OptionalReportingGaussianInfoMeasure_marginal_interval
        referenceSkill actorLaw
        (fun base =>
          lg21GaussianPosteriorMeanPBOCutoff M theta k threshold e base)
        (fun base =>
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base)
            (lg21GaussianPosteriorMeanPBOCutoff
              M theta k threshold e base))
        base0 hinfo_meas (by simpa [threshold] using hset_meas base0)
  have hEq' :
      ∀ e : PUnit,
        lg21SourceEquilibriumAE
          (lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw)
          (lg21OptionalReportingBaseSourceEquilibriumData
            takeDecision reportDecision
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k threshold e base))))
            estimationConsistent) := by
    intro e
    simpa [threshold] using hEq
  exact
    lg21OptionalReportingGaussianPosteriorPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (Equilibrium := PUnit)
      (fun _ =>
        lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw)
      PBO M theta k
      (fun _ => takeDecision) (fun _ => reportDecision)
      (fun _ => estimationConsistent) (fun _ => actorLaw) threshold
      hPBO hreport' hmarginal hEq'

/--
Report-required finite-base Gaussian information law: the paper's affine-skill
`P_BO` upper-tail source game is not an a.e. source equilibrium for any single
threshold profile.
-/
theorem lg21ReportRequiredAffineSkillPBO_not_sourceEquilibriumAE_finite_base_gaussian_info_law
    {Base Test : Type*}
    [Fintype Base] [DecidableEq Base] [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (PBO : Base → ℝ → ℝ)
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (intercept slope pboThreshold : Base → ℝ)
    (referenceTest : Base → Test)
    (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (htakePBO :
      ∀ base skill, takeDecision skill base = true ↔
        pboThreshold base ≤ PBO base skill)
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest base } :
              LG21AccessStudentInfo ℝ Base Test)))
    (hset_meas :
      ∀ base,
        MeasurableSet
          {info : LG21AccessStudentInfo ℝ Base Test |
            info.base = base ∧
              lg21AffineSkillPBOCutoff
                (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                (fun _ : PUnit => pboThreshold) PUnit.unit base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21AffineSkillPBOCutoff
                    (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                    (fun _ : PUnit => pboThreshold) PUnit.unit base)})
    (hEq :
      lg21SourceEquilibriumAE
        (lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw)
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw base)
                    (lg21AffineSkillPBOCutoff
                      (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                      (fun _ : PUnit => pboThreshold) PUnit.unit base)) +
                actor)
          estimationConsistent)) :
    False := by
  let PBO' : PUnit → Base → ℝ → ℝ := fun _ base skill => PBO base skill
  let intercept' : PUnit → Base → ℝ := fun _ base => intercept base
  let slope' : PUnit → Base → ℝ := fun _ base => slope base
  let threshold : PUnit → Base → ℝ := fun _ base => pboThreshold base
  have hslope' : ∀ e base, 0 < slope' e base := by
    intro e base
    simpa [slope'] using hslope base
  have hPBO' : lg21AffineSkillPBOFormula PBO' intercept' slope' := by
    intro e base skill
    simpa [PBO', intercept', slope'] using hPBO base skill
  have htake' :
      ∀ e base skill, takeDecision skill base = true ↔
        threshold e base ≤ PBO' e base skill := by
    intro e base skill
    simpa [PBO', threshold] using htakePBO base skill
  have hmarginal :
      ∀ e base0,
        lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw
          {info |
            info.base = base0 ∧
              lg21AffineSkillPBOCutoff intercept' slope' threshold e base0 ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base0)
                  (lg21AffineSkillPBOCutoff
                    intercept' slope' threshold e base0)} =
          (actorLaw base0).toMeasure
            (Set.Ico
              (lg21AffineSkillPBOCutoff intercept' slope' threshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw base0)
                (lg21AffineSkillPBOCutoff
                  intercept' slope' threshold e base0))) := by
    intro e base0
    exact
      lg21ReportRequiredGaussianInfoMeasure_marginal_interval
        referenceTest actorLaw
        (fun base => lg21AffineSkillPBOCutoff intercept' slope' threshold e base)
        (fun base =>
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base)
            (lg21AffineSkillPBOCutoff intercept' slope' threshold e base))
        base0 hinfo_meas
        (by simpa [intercept', slope', threshold] using hset_meas base0)
  have hEq' :
      ∀ e : PUnit,
        lg21SourceEquilibriumAE
          (lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw)
          (lg21ReportRequiredBaseSourceEquilibriumData
            takeDecision reportDecision
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw base)
                      (lg21AffineSkillPBOCutoff
                        intercept' slope' threshold e base)) +
                  actor)
            estimationConsistent) := by
    intro e
    simpa [intercept', slope', threshold] using hEq
  exact
    lg21ReportRequiredAffineSkillPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (Equilibrium := PUnit)
      (fun _ =>
        lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw)
      PBO' (fun _ => takeDecision) (fun _ => reportDecision)
      (fun _ => estimationConsistent) (fun _ => actorLaw)
      intercept' slope' threshold hslope' hPBO' htake' hmarginal hEq'

/--
Pointwise Definition 1 form of the optional-reporting finite-base Gaussian
information-law contradiction.
-/
theorem lg21OptionalReportingGaussianPosteriorPBO_not_sourceEquilibrium_finite_base_gaussian_info_law
    {Feature Skill Base : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base] [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (reportDecision : Base → ℝ → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (pboThreshold : Base → ℝ)
    (referenceSkill : Base → Skill)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ base actor, reportDecision base actor = true ↔
        pboThreshold base ≤ PBO base (Function.update (theta base) k actor))
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun score : ℝ =>
            ({ skill := referenceSkill base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)))
    (hset_meas :
      ∀ base,
        MeasurableSet
          {info : LG21AccessStudentInfo Skill Base ℝ |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff
                M theta k (fun _ : PUnit => pboThreshold) PUnit.unit base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k (fun _ : PUnit => pboThreshold) PUnit.unit
                    base)})
    (hEq :
      lg21SourceEquilibrium
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k (fun _ : PUnit => pboThreshold) PUnit.unit
                    base))))
          estimationConsistent)) :
    False :=
  lg21OptionalReportingGaussianPosteriorPBO_not_sourceEquilibriumAE_finite_base_gaussian_info_law
    PBO M theta k takeDecision reportDecision estimationConsistent actorLaw
    pboThreshold referenceSkill hPBO hreportPBO hinfo_meas hset_meas
    (lg21SourceEquilibriumAE_of_sourceEquilibrium
      (μ := lg21OptionalReportingGaussianInfoMeasure referenceSkill actorLaw)
      hEq)

/--
Pointwise Definition 1 form of the report-required finite-base Gaussian
information-law contradiction.
-/
theorem lg21ReportRequiredAffineSkillPBO_not_sourceEquilibrium_finite_base_gaussian_info_law
    {Base Test : Type*}
    [Fintype Base] [DecidableEq Base] [Nonempty Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (PBO : Base → ℝ → ℝ)
    (takeDecision : ℝ → Base → Bool)
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (intercept slope pboThreshold : Base → ℝ)
    (referenceTest : Base → Test)
    (hslope : ∀ base, 0 < slope base)
    (hPBO : ∀ base skill, PBO base skill = intercept base + slope base * skill)
    (htakePBO :
      ∀ base skill, takeDecision skill base = true ↔
        pboThreshold base ≤ PBO base skill)
    (hinfo_meas :
      ∀ base,
        Measurable
          (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest base } :
              LG21AccessStudentInfo ℝ Base Test)))
    (hset_meas :
      ∀ base,
        MeasurableSet
          {info : LG21AccessStudentInfo ℝ Base Test |
            info.base = base ∧
              lg21AffineSkillPBOCutoff
                (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                (fun _ : PUnit => pboThreshold) PUnit.unit base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw base)
                  (lg21AffineSkillPBOCutoff
                    (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                    (fun _ : PUnit => pboThreshold) PUnit.unit base)})
    (hEq :
      lg21SourceEquilibrium
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw base)
                    (lg21AffineSkillPBOCutoff
                      (fun _ : PUnit => intercept) (fun _ : PUnit => slope)
                      (fun _ : PUnit => pboThreshold) PUnit.unit base)) +
                actor)
          estimationConsistent)) :
    False :=
  lg21ReportRequiredAffineSkillPBO_not_sourceEquilibriumAE_finite_base_gaussian_info_law
    PBO takeDecision reportDecision estimationConsistent actorLaw intercept slope
    pboThreshold referenceTest hslope hPBO htakePBO hinfo_meas hset_meas
    (lg21SourceEquilibriumAE_of_sourceEquilibrium
      (μ := lg21ReportRequiredGaussianInfoMeasure referenceTest actorLaw)
      hEq)

/--
Fully specified optional-reporting upper-tail source model, repaired a.e.
version.  If the realized score law has the paper's Gaussian marginal interval
law at a base profile, the fully specified upper-tail source game cannot be an
a.e. source equilibrium.
-/
theorem lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Feature Skill Base : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (μ : Measure (LG21AccessStudentInfo Skill Base ℝ))
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Skill → Base → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData
          M theta k takeDecision estimationConsistent actorLaw
          decisionThreshold)) : False := by
  let reportDecision : Base → ℝ → Bool := fun base actor =>
    if decisionThreshold base ≤ actor then true else false
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  have hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base) := by
    intro base
    rfl
  have hreports_above_threshold :
      ∀ base score,
        decisionThreshold base ≤ score → reportDecision base score = true := by
    intro base score hscore
    simp [reportDecision, hscore]
  have hEqAffine :
      lg21SourceEquilibriumAE μ
        (lg21OptionalReportingBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actor) / 1)
          (fun base =>
            ((M base).posteriorMean (Function.update (theta base) k 0) +
              (M base).centeredFamily.signalWeight k * actorMean base) / 1)
          estimationConsistent) := by
    have hreported_eq :
        (fun base actor =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actor) / 1) =
        (fun base actor =>
          (M base).posteriorMean (Function.update (theta base) k actor)) := by
      funext base actor
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k actor).symm
    have hnoReport_eq :
        (fun base =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actorMean base) / 1) =
        (fun base =>
          (M base).posteriorMean
            (Function.update (theta base) k
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw base) (decisionThreshold base)))) := by
      funext base
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k (actorMean base)).symm
    rw [hreported_eq, hnoReport_eq]
    simpa [reportDecision,
      lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData] using
      hEq
  exact
    lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      μ takeDecision reportDecision estimationConsistent
      (fun base => (M base).posteriorMean (Function.update (theta base) k 0))
      (fun base => (M base).centeredFamily.signalWeight k)
      (fun _base => (1 : ℝ)) actorMean actorLaw decisionThreshold base0
      hactorMean hreports_above_threshold
      (fun base => (M base).centeredFamily.signalWeight_pos k)
      (fun _base => by norm_num) hmarginal hEqAffine

/--
Family form of the repaired a.e. fully specified optional-reporting upper-tail
source-model contradiction.
-/
theorem lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    [Nonempty Base] [Nonempty Equilibrium]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : Equilibrium → Skill → Base → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (decisionThreshold : Equilibrium → Base → ℝ)
    (hmarginal :
      ∀ e base0,
        μ e {info |
          info.base = base0 ∧ decisionThreshold e base0 ≤ info.test ∧
            info.test <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0) (decisionThreshold e base0)} =
          (actorLaw e base0).toMeasure
            (Set.Ico (decisionThreshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0) (decisionThreshold e base0))))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData
            M theta k (takeDecision e) (estimationConsistent e)
            (actorLaw e) (decisionThreshold e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  let base0 : Base := Classical.choice (inferInstance : Nonempty Base)
  exact
    lg21FullySpecifiedOptionalReportingUpperTailSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (μ e0) M theta k (takeDecision e0) (estimationConsistent e0)
      (actorLaw e0) (decisionThreshold e0) base0 (hmarginal e0 base0)
      (hEq e0)

/--
Fully specified report-required upper-tail source model, repaired a.e. version.
If the realized skill law has the paper's Gaussian marginal interval law at a
base profile, the fully specified upper-tail source game cannot be an a.e.
source equilibrium.
-/
theorem lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Base Test : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (μ : Measure (LG21AccessStudentInfo ℝ Base Test))
    (reportDecision : Base → Test → Bool)
    (estimationConsistent : Prop)
    (actorLaw : Base → GaussianScaleLaw)
    (decisionThreshold : Base → ℝ)
    (base0 : Base)
    (hmarginal :
      μ {info |
        info.base = base0 ∧ decisionThreshold base0 ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0)} =
        (actorLaw base0).toMeasure
          (Set.Ico (decisionThreshold base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw base0) (decisionThreshold base0))))
    (hEq :
      lg21SourceEquilibriumAE μ
        (lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData
          reportDecision estimationConsistent actorLaw decisionThreshold)) :
    False := by
  let takeDecision : ℝ → Base → Bool := fun actor base =>
    if decisionThreshold base ≤ actor then true else false
  let actorMean : Base → ℝ := fun base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw base) (decisionThreshold base)
  have hactorMean :
      ∀ base,
        actorMean base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw base) (decisionThreshold base) := by
    intro base
    rfl
  have htakes_above_threshold :
      ∀ base skill,
        decisionThreshold base ≤ skill → takeDecision skill base = true := by
    intro base skill hskill
    simp [takeDecision, hskill]
  have houtside :
      ∀ base, (1 / 2 : ℝ) =
        (((1 / 2 : ℝ) - actorMean base) + (1 : ℝ) * actorMean base) / 1 := by
    intro base
    ring
  have hEqAffine :
      lg21SourceEquilibriumAE μ
        (lg21ReportRequiredBaseSourceEquilibriumData
          takeDecision reportDecision
          (fun base actor =>
            (((1 / 2 : ℝ) - actorMean base) + (1 : ℝ) * actor) / 1)
          estimationConsistent) := by
    simpa [takeDecision, actorMean,
      lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData, div_one]
      using hEq
  exact
    lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      μ takeDecision reportDecision estimationConsistent
      (fun base => (1 / 2 : ℝ) - actorMean base)
      (fun _base => (1 : ℝ)) (fun _base => (1 : ℝ)) actorMean
      actorLaw decisionThreshold base0 hactorMean htakes_above_threshold
      (fun _base => by norm_num) (fun _base => by norm_num) houtside
      hmarginal hEqAffine

/--
Family form of the repaired a.e. fully specified report-required upper-tail
source-model contradiction.
-/
theorem lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    {Base Test Equilibrium : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    [Nonempty Base] [Nonempty Equilibrium]
    (μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (reportDecision : Equilibrium → Base → Test → Bool)
    (estimationConsistent : Equilibrium → Prop)
    (actorLaw : Equilibrium → Base → GaussianScaleLaw)
    (decisionThreshold : Equilibrium → Base → ℝ)
    (hmarginal :
      ∀ e base0,
        μ e {info |
          info.base = base0 ∧ decisionThreshold e base0 ≤ info.skill ∧
            info.skill <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0) (decisionThreshold e base0)} =
          (actorLaw e base0).toMeasure
            (Set.Ico (decisionThreshold e base0)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base0) (decisionThreshold e base0))))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData
            (reportDecision e) (estimationConsistent e)
            (actorLaw e) (decisionThreshold e))) : False := by
  let e0 : Equilibrium := Classical.choice (inferInstance : Nonempty Equilibrium)
  let base0 : Base := Classical.choice (inferInstance : Nonempty Base)
  exact
    lg21FullySpecifiedReportRequiredUpperTailSourceEquilibriumData_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (μ e0) (reportDecision e0) (estimationConsistent e0)
      (actorLaw e0) (decisionThreshold e0) base0 (hmarginal e0 base0)
      (hEq e0)

/--
Theorem 3.2 optional-reporting Section 3 law-level route through the repaired
a.e. equilibrium seam.  The source proof's remaining source-specific work is
isolated in `hpositive_of_nonblank`: every nonblank test use yields positive
mass of reporting types below the imputed no-report mean.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
    {Skill Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean : S.Equilibrium → Base → ℝ)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (fun base =>
              (baseTerm e base + signalWeight e base * actorMean e base) /
                denom e base)
            (estimationConsistent e)))
    (hpositive_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          0 < μ e {info |
            reportDecision e info.base info.test = true ∧
              info.test < actorMean e info.base}) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _ e base test
    by_contra hne
    exact
      lg21OptionalReportingBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_reporter_mass
        (μ e) (takeDecision e) (reportDecision e) (estimationConsistent e)
        (baseTerm e) (signalWeight e) (denom e) (actorMean e)
        (hweight e) (hdenom e)
        (hpositive_of_nonblank e base test hne) (hEq e)

/--
No-relevance form of the optional-reporting repaired a.e. Section 3 law-level
route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_source_equilibriumAE_positive_below_mean
    {Skill Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean : S.Equilibrium → Base → ℝ)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (fun base =>
              (baseTerm e base + signalWeight e base * actorMean e base) /
                denom e base)
            (estimationConsistent e)))
    (hpositive_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          0 < μ e {info |
            reportDecision e info.base info.test = true ∧
              info.test < actorMean e info.base})
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
      μ takeDecision reportDecision estimationConsistent baseTerm
      signalWeight denom actorMean hweight hdenom hEq
      hpositive_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Theorem 3.2 report-required Section 3 law-level route through the repaired
a.e. equilibrium seam.  The source-specific witness says every nonblank test
use yields positive mass of takers below the imputed outside-option mean.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean : S.Equilibrium → Base → ℝ)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (houtside :
      ∀ e base, (1 / 2 : ℝ) =
        (baseTerm e base + signalWeight e base * actorMean e base) /
          denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (estimationConsistent e)))
    (hpositive_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          0 < μ e {info |
            takeDecision e info.skill info.base = true ∧
              info.skill < actorMean e info.base}) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _ e base test
    by_contra hne
    exact
      lg21ReportRequiredBaseSourceEquilibriumData_not_sourceEquilibriumAE_of_positive_below_mean_taker_mass
        (μ e) (takeDecision e) (reportDecision e) (estimationConsistent e)
        (baseTerm e) (signalWeight e) (denom e) (actorMean e)
        (hweight e) (hdenom e) (houtside e)
        (hpositive_of_nonblank e base test hne) (hEq e)

/--
No-relevance form of the report-required repaired a.e. Section 3 law-level
route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_source_equilibriumAE_positive_below_mean
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean : S.Equilibrium → Base → ℝ)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (houtside :
      ∀ e base, (1 / 2 : ℝ) =
        (baseTerm e base + signalWeight e base * actorMean e base) /
          denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (estimationConsistent e)))
    (hpositive_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          0 < μ e {info |
            takeDecision e info.skill info.base = true ∧
              info.skill < actorMean e info.base})
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
      μ takeDecision reportDecision estimationConsistent baseTerm
      signalWeight denom actorMean hweight hdenom houtside hEq
      hpositive_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Optional-reporting Section 3 law-level route with the source proof's Gaussian
upper-tail marginal law.  A nonblank profile supplies the base-local Gaussian
interval law on `[cutoff, upper-tail mean)`, so the previous positive
below-mean a.e. route applies.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
    {Skill Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean cutoff : S.Equilibrium → Base → ℝ)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base))
    (hreports_above_cutoff :
      ∀ e base score, cutoff e base ≤ score →
        reportDecision e base score = true)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (fun base =>
              (baseTerm e base + signalWeight e base * actorMean e base) /
                denom e base)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧ cutoff e base ≤ info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico (cutoff e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine
    paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom hEq ?_
  intro e base test hne
  have hposLocal :
      0 < μ e {info |
        info.base = base ∧ cutoff e base ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base) (cutoff e base)} := by
    rw [hmarginal_of_nonblank e base test hne]
    exact
      standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos
        (actorLaw e base) (cutoff e base)
  exact
    lg21_measure_pos_of_subset
      (A := {info : LG21AccessStudentInfo Skill Base ℝ |
        info.base = base ∧ cutoff e base ≤ info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base) (cutoff e base)})
      (B := {info : LG21AccessStudentInfo Skill Base ℝ |
        reportDecision e info.base info.test = true ∧
          info.test < actorMean e info.base})
      (fun info hinfo => by
        rcases hinfo with ⟨hbase, hcut, hlt⟩
        constructor
        · simpa [hbase] using
            hreports_above_cutoff e base info.test hcut
        · have hlt_actor : info.test < actorMean e base := by
            simpa [hactorMean e base] using hlt
          simpa [hbase] using hlt_actor)
      hposLocal

/--
No-relevance form of the optional-reporting Gaussian upper-tail marginal-law
a.e. route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
    {Skill Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean cutoff : S.Equilibrium → Base → ℝ)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base))
    (hreports_above_cutoff :
      ∀ e base score, cutoff e base ≤ score →
        reportDecision e base score = true)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (fun base =>
              (baseTerm e base + signalWeight e base * actorMean e base) /
                denom e base)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧ cutoff e base ≤ info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico (cutoff e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base))))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean cutoff actorLaw hactorMean hreports_above_cutoff
      hweight hdenom hEq hmarginal_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Report-required Section 3 law-level route with the source proof's Gaussian
upper-tail marginal law.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean cutoff : S.Equilibrium → Base → ℝ)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base))
    (htakes_above_cutoff :
      ∀ e base skill, cutoff e base ≤ skill →
        takeDecision e skill base = true)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (houtside :
      ∀ e base, (1 / 2 : ℝ) =
        (baseTerm e base + signalWeight e base * actorMean e base) /
          denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧ cutoff e base ≤ info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico (cutoff e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine
    paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_positive_below_mean
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean hweight hdenom houtside hEq ?_
  intro e base test hne
  have hposLocal :
      0 < μ e {info |
        info.base = base ∧ cutoff e base ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base) (cutoff e base)} := by
    rw [hmarginal_of_nonblank e base test hne]
    exact
      standardGaussian_toMeasure_Ico_threshold_normalUpperTailMean_pos
        (actorLaw e base) (cutoff e base)
  exact
    lg21_measure_pos_of_subset
      (A := {info : LG21AccessStudentInfo ℝ Base Test |
        info.base = base ∧ cutoff e base ≤ info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base) (cutoff e base)})
      (B := {info : LG21AccessStudentInfo ℝ Base Test |
        takeDecision e info.skill info.base = true ∧
          info.skill < actorMean e info.base})
      (fun info hinfo => by
        rcases hinfo with ⟨hbase, hcut, hlt⟩
        constructor
        · simpa [hbase] using
            htakes_above_cutoff e base info.skill hcut
        · have hlt_actor : info.skill < actorMean e base := by
            simpa [hactorMean e base] using hlt
          simpa [hbase] using hlt_actor)
      hposLocal

/--
No-relevance form of the report-required Gaussian upper-tail marginal-law
a.e. route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (baseTerm signalWeight denom actorMean cutoff : S.Equilibrium → Base → ℝ)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base))
    (htakes_above_cutoff :
      ∀ e base skill, cutoff e base ≤ skill →
        takeDecision e skill base = true)
    (hweight : ∀ e base, 0 < signalWeight e base)
    (hdenom : ∀ e base, 0 < denom e base)
    (houtside :
      ∀ e base, (1 / 2 : ℝ) =
        (baseTerm e base + signalWeight e base * actorMean e base) /
          denom e base)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (baseTerm e base + signalWeight e base * actor) /
                denom e base)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧ cutoff e base ≤ info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico (cutoff e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base) (cutoff e base))))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
      μ takeDecision reportDecision estimationConsistent baseTerm signalWeight
      denom actorMean cutoff actorLaw hactorMean htakes_above_cutoff
      hweight hdenom houtside hEq hmarginal_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Optional-reporting Section 3 law-level route specialized to the paper's
Gaussian posterior `P_BO` threshold rule.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_gaussian_marginal_law
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : S.Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base)))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  let cutoff : S.Equilibrium → Base → ℝ :=
    lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold
  let actorMean : S.Equilibrium → Base → ℝ := fun e base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw e base) (cutoff e base)
  have hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base) := by
    intro e base
    rfl
  have hreports_above_cutoff :
      ∀ e base score, cutoff e base ≤ score →
        reportDecision e base score = true := by
    intro e base score hscore
    exact
      (hreportPBO e base score).2
        ((lg21GaussianPosteriorMeanPBO_threshold_iff_cutoff
          PBO M theta k pboThreshold hPBO e base score).mpr
          (by simpa [cutoff] using hscore))
  have hEqAffine :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((M base).posteriorMean (Function.update (theta base) k 0) +
                (M base).centeredFamily.signalWeight k * actor) / 1)
            (fun base =>
              ((M base).posteriorMean (Function.update (theta base) k 0) +
                (M base).centeredFamily.signalWeight k * actorMean e base) / 1)
            (estimationConsistent e)) := by
    intro e
    have hreported_eq :
        (fun base actor =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actor) / 1) =
        (fun base actor =>
          (M base).posteriorMean (Function.update (theta base) k actor)) := by
      funext base actor
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k actor).symm
    have hnoReport_eq :
        (fun base =>
          ((M base).posteriorMean (Function.update (theta base) k 0) +
            (M base).centeredFamily.signalWeight k * actorMean e base) / 1) =
        (fun base =>
          (M base).posteriorMean
            (Function.update (theta base) k
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)))) := by
      funext base
      rw [div_one]
      exact
        ((M base).posteriorMean_update_eq_base_add_weight_mul
          (theta base) k (actorMean e base)).symm
    rw [hreported_eq, hnoReport_eq]
    exact hEq e
  exact
    paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
      μ takeDecision reportDecision estimationConsistent
      (fun _e base =>
        (M base).posteriorMean (Function.update (theta base) k 0))
      (fun _e base => (M base).centeredFamily.signalWeight k)
      (fun _e _base => (1 : ℝ)) actorMean cutoff actorLaw hactorMean
      hreports_above_cutoff
      (fun _e base => (M base).centeredFamily.signalWeight_pos k)
      (fun _e _base => by norm_num) hEqAffine
      (by
        intro e base test hne
        simpa [cutoff] using hmarginal_of_nonblank e base test hne)

/--
No-relevance form of the optional-reporting Gaussian posterior `P_BO` repaired
a.e. route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_gaussian_posterior_pbo_source_equilibriumAE_gaussian_marginal_law
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ))
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : S.Equilibrium → Base → ℝ)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base))))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_gaussian_marginal_law
      μ PBO M theta k takeDecision reportDecision estimationConsistent
      actorLaw pboThreshold hPBO hreportPBO hEq hmarginal_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Report-required Section 3 law-level route specialized to the paper's affine
skill `P_BO` threshold rule.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_gaussian_marginal_law
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (PBO : S.Equilibrium → Base → ℝ → ℝ)
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : S.Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧
              lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico
                (lg21AffineSkillPBOCutoff intercept slope pboThreshold e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base)))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  let cutoff : S.Equilibrium → Base → ℝ :=
    lg21AffineSkillPBOCutoff intercept slope pboThreshold
  let actorMean : S.Equilibrium → Base → ℝ := fun e base =>
    GaussianHazardCertificate.normalUpperTailMean
      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
      (actorLaw e base) (cutoff e base)
  have hactorMean :
      ∀ e base,
        actorMean e base =
          GaussianHazardCertificate.normalUpperTailMean
            standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
            (actorLaw e base) (cutoff e base) := by
    intro e base
    rfl
  have htakes_above_cutoff :
      ∀ e base skill, cutoff e base ≤ skill →
        takeDecision e skill base = true := by
    intro e base skill hskill
    exact
      (htakePBO e base skill).2
        ((lg21AffineSkillPBO_threshold_iff_cutoff
          PBO intercept slope pboThreshold hslope hPBO e base skill).mpr
          (by simpa [cutoff] using hskill))
  have houtside :
      ∀ e base, (1 / 2 : ℝ) =
        (((1 / 2 : ℝ) - actorMean e base) + (1 : ℝ) * actorMean e base) / 1 := by
    intro e base
    ring
  have hEqAffine :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (((1 / 2 : ℝ) - actorMean e base) + (1 : ℝ) * actor) / 1)
            (estimationConsistent e)) := by
    intro e
    simpa [actorMean, cutoff, div_one] using hEq e
  exact
    paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_source_equilibriumAE_gaussian_upper_tail_marginal_law
      μ takeDecision reportDecision estimationConsistent
      (fun e base => (1 / 2 : ℝ) - actorMean e base)
      (fun _e _base => (1 : ℝ)) (fun _e _base => (1 : ℝ))
      actorMean cutoff actorLaw hactorMean htakes_above_cutoff
      (fun _e _base => by norm_num) (fun _e _base => by norm_num)
      houtside hEqAffine
      (by
        intro e base test hne
        simpa [cutoff] using hmarginal_of_nonblank e base test hne)

/--
No-relevance form of the report-required affine `P_BO` repaired a.e. route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_affine_pbo_source_equilibriumAE_gaussian_marginal_law
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test))
    (PBO : S.Equilibrium → Base → ℝ → ℝ)
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : S.Equilibrium → Base → ℝ)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE (μ e)
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e)))
    (hmarginal_of_nonblank :
      ∀ e base test,
        S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
          μ e {info |
            info.base = base ∧
              lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base)} =
            (actorLaw e base).toMeasure
              (Set.Ico
                (lg21AffineSkillPBOCutoff intercept slope pboThreshold e base)
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base))))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_gaussian_marginal_law
      μ PBO takeDecision reportDecision estimationConsistent actorLaw
      intercept slope pboThreshold hslope hPBO htakePBO hEq
      hmarginal_of_nonblank).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Optional-reporting Section 3 law-level route for the paper's Gaussian
posterior `P_BO`, with the realized a.e. type law specialized to the finite
sum of base-local Gaussian reported-score laws.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_finite_base_gaussian_info_law
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : S.Equilibrium → Base → ℝ)
    (referenceSkill : S.Equilibrium → Base → Skill)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hinfo_meas :
      ∀ e base,
        Measurable
          (fun score : ℝ =>
            ({ skill := referenceSkill e base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)))
    (hset_meas :
      ∀ e base,
        MeasurableSet
          {info : LG21AccessStudentInfo Skill Base ℝ |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base)})
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE
          (lg21OptionalReportingGaussianInfoMeasure
            (referenceSkill e) (actorLaw e))
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine
    paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_gaussian_marginal_law
      (fun e =>
        lg21OptionalReportingGaussianInfoMeasure
          (referenceSkill e) (actorLaw e))
      PBO M theta k takeDecision reportDecision estimationConsistent actorLaw
      pboThreshold hPBO hreportPBO hEq ?_
  intro e base test _hne
  exact
    lg21OptionalReportingGaussianInfoMeasure_marginal_interval
      (referenceSkill e) (actorLaw e)
      (fun base =>
        lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base)
      (fun base =>
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (actorLaw e base)
          (lg21GaussianPosteriorMeanPBOCutoff
            M theta k pboThreshold e base))
      base (hinfo_meas e) (hset_meas e base)

/--
No-relevance form of the optional-reporting finite-base Gaussian information
law route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_gaussian_posterior_pbo_source_equilibriumAE_finite_base_gaussian_info_law
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature)
    (takeDecision : S.Equilibrium → Skill → Base → Bool)
    (reportDecision : S.Equilibrium → Base → ℝ → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (pboThreshold : S.Equilibrium → Base → ℝ)
    (referenceSkill : S.Equilibrium → Base → Skill)
    (hPBO : ∀ base obs, PBO base obs = (M base).posteriorMean obs)
    (hreportPBO :
      ∀ e base actor, reportDecision e base actor = true ↔
        pboThreshold e base ≤ PBO base (Function.update (theta base) k actor))
    (hinfo_meas :
      ∀ e base,
        Measurable
          (fun score : ℝ =>
            ({ skill := referenceSkill e base, base := base, test := score } :
              LG21AccessStudentInfo Skill Base ℝ)))
    (hset_meas :
      ∀ e base,
        MeasurableSet
          {info : LG21AccessStudentInfo Skill Base ℝ |
            info.base = base ∧
              lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
                info.test ∧
              info.test <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base)})
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE
          (lg21OptionalReportingGaussianInfoMeasure
            (referenceSkill e) (actorLaw e))
          (lg21OptionalReportingBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              (M base).posteriorMean (Function.update (theta base) k actor))
            (fun base =>
              (M base).posteriorMean
                (Function.update (theta base) k
                  (GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21GaussianPosteriorMeanPBOCutoff
                      M theta k pboThreshold e base))))
            (estimationConsistent e)))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_finite_base_gaussian_info_law
      PBO M theta k takeDecision reportDecision estimationConsistent actorLaw
      pboThreshold referenceSkill hPBO hreportPBO hinfo_meas hset_meas hEq).2
      hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Report-required Section 3 law-level route for the paper's affine-skill `P_BO`,
with the realized a.e. type law specialized to the finite sum of base-local
Gaussian skill laws.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_finite_base_gaussian_info_law
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (PBO : S.Equilibrium → Base → ℝ → ℝ)
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : S.Equilibrium → Base → ℝ)
    (referenceTest : S.Equilibrium → Base → Test)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hinfo_meas :
      ∀ e base,
        Measurable
          (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest e base } :
              LG21AccessStudentInfo ℝ Base Test)))
    (hset_meas :
      ∀ e base,
        MeasurableSet
          {info : LG21AccessStudentInfo ℝ Base Test |
            info.base = base ∧
              lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base)})
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE
          (lg21ReportRequiredGaussianInfoMeasure
            (referenceTest e) (actorLaw e))
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e))) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine
    paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_gaussian_marginal_law
      (fun e =>
        lg21ReportRequiredGaussianInfoMeasure
          (referenceTest e) (actorLaw e))
      PBO takeDecision reportDecision estimationConsistent actorLaw intercept
      slope pboThreshold hslope hPBO htakePBO hEq ?_
  intro e base test _hne
  exact
    lg21ReportRequiredGaussianInfoMeasure_marginal_interval
      (referenceTest e) (actorLaw e)
      (fun base =>
        lg21AffineSkillPBOCutoff intercept slope pboThreshold e base)
      (fun base =>
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (actorLaw e base)
          (lg21AffineSkillPBOCutoff intercept slope pboThreshold e base))
      base (hinfo_meas e) (hset_meas e base)

/--
No-relevance form of the report-required finite-base Gaussian information law
route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_affine_pbo_source_equilibriumAE_finite_base_gaussian_info_law
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    (PBO : S.Equilibrium → Base → ℝ → ℝ)
    (takeDecision : S.Equilibrium → ℝ → Base → Bool)
    (reportDecision : S.Equilibrium → Base → Test → Bool)
    (estimationConsistent : S.Equilibrium → Prop)
    (actorLaw : S.Equilibrium → Base → GaussianScaleLaw)
    (intercept slope pboThreshold : S.Equilibrium → Base → ℝ)
    (referenceTest : S.Equilibrium → Base → Test)
    (hslope : ∀ e base, 0 < slope e base)
    (hPBO : lg21AffineSkillPBOFormula PBO intercept slope)
    (htakePBO :
      ∀ e base skill, takeDecision e skill base = true ↔
        pboThreshold e base ≤ PBO e base skill)
    (hinfo_meas :
      ∀ e base,
        Measurable
          (fun skill : ℝ =>
            ({ skill := skill, base := base, test := referenceTest e base } :
              LG21AccessStudentInfo ℝ Base Test)))
    (hset_meas :
      ∀ e base,
        MeasurableSet
          {info : LG21AccessStudentInfo ℝ Base Test |
            info.base = base ∧
              lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
                info.skill ∧
              info.skill <
                GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21AffineSkillPBOCutoff
                    intercept slope pboThreshold e base)})
    (hEq :
      ∀ e,
        lg21SourceEquilibriumAE
          (lg21ReportRequiredGaussianInfoMeasure
            (referenceTest e) (actorLaw e))
          (lg21ReportRequiredBaseSourceEquilibriumData
            (takeDecision e) (reportDecision e)
            (fun base actor =>
              ((1 / 2 : ℝ) -
                    GaussianHazardCertificate.normalUpperTailMean
                      standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                      (actorLaw e base)
                      (lg21AffineSkillPBOCutoff
                        intercept slope pboThreshold e base)) +
                  actor)
            (estimationConsistent e)))
    (hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  have hblank :
      lg21SourceLawTestBlank S :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_finite_base_gaussian_info_law
      PBO takeDecision reportDecision estimationConsistent actorLaw intercept
      slope pboThreshold referenceTest hslope hPBO htakePBO hinfo_meas
      hset_meas hEq).2 hfair
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro hrel
    rcases hrel with ⟨e, base, test, hne⟩
    exact hne (hblank e base test)

/--
Compact a.e. certificate for the optional-reporting Gaussian posterior `P_BO`
upper-tail contradiction when the realized type law is the finite sum of
base-local Gaussian reported-score laws.
-/
structure LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature) where
  takeDecision : Equilibrium → Skill → Base → Bool
  reportDecision : Equilibrium → Base → ℝ → Bool
  estimationConsistent : Equilibrium → Prop
  actorLaw : Equilibrium → Base → GaussianScaleLaw
  pboThreshold : Equilibrium → Base → ℝ
  referenceSkill : Equilibrium → Base → Skill
  pbo_eq : ∀ base obs, PBO base obs = (M base).posteriorMean obs
  report_threshold :
    ∀ e base actor, reportDecision e base actor = true ↔
      pboThreshold e base ≤ PBO base (Function.update (theta base) k actor)
  info_meas :
    ∀ e base,
      Measurable
        (fun score : ℝ =>
          ({ skill := referenceSkill e base, base := base, test := score } :
            LG21AccessStudentInfo Skill Base ℝ))
  interval_meas :
    ∀ e base,
      MeasurableSet
        {info : LG21AccessStudentInfo Skill Base ℝ |
          info.base = base ∧
            lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
              info.test ∧
            info.test <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)}
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE
        (lg21OptionalReportingGaussianInfoMeasure
          (referenceSkill e) (actorLaw e))
        (lg21OptionalReportingBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base))))
          (estimationConsistent e))

/--
The optional-reporting finite-base a.e. Gaussian posterior `P_BO` certificate is
inconsistent on nonempty domains.
-/
theorem LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate.false_of_nonempty
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    [Nonempty Base] [Nonempty Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := Equilibrium) PBO M theta k) :
    False := by
  refine
    lg21OptionalReportingGaussianPosteriorPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (fun e =>
        lg21OptionalReportingGaussianInfoMeasure
          (C.referenceSkill e) (C.actorLaw e))
      PBO M theta k C.takeDecision C.reportDecision C.estimationConsistent
      C.actorLaw C.pboThreshold C.pbo_eq C.report_threshold ?_
      C.sourceEquilibriumAE
  intro e base0
  exact
    lg21OptionalReportingGaussianInfoMeasure_marginal_interval
      (C.referenceSkill e) (C.actorLaw e)
      (fun base =>
        lg21GaussianPosteriorMeanPBOCutoff M theta k C.pboThreshold e base)
      (fun base =>
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (C.actorLaw e base)
          (lg21GaussianPosteriorMeanPBOCutoff
            M theta k C.pboThreshold e base))
      base0 (C.info_meas e) (C.interval_meas e base0)

/--
Compact a.e. certificate for the report-required affine-skill `P_BO`
upper-tail contradiction when the realized type law is the finite sum of
base-local Gaussian latent-skill laws.
-/
structure LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
    {Base Test Equilibrium : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (PBO : Equilibrium → Base → ℝ → ℝ) where
  takeDecision : Equilibrium → ℝ → Base → Bool
  reportDecision : Equilibrium → Base → Test → Bool
  estimationConsistent : Equilibrium → Prop
  actorLaw : Equilibrium → Base → GaussianScaleLaw
  intercept : Equilibrium → Base → ℝ
  slope : Equilibrium → Base → ℝ
  pboThreshold : Equilibrium → Base → ℝ
  referenceTest : Equilibrium → Base → Test
  slope_pos : ∀ e base, 0 < slope e base
  pbo_eq : lg21AffineSkillPBOFormula PBO intercept slope
  take_threshold :
    ∀ e base skill, takeDecision e skill base = true ↔
      pboThreshold e base ≤ PBO e base skill
  info_meas :
    ∀ e base,
      Measurable
        (fun skill : ℝ =>
          ({ skill := skill, base := base, test := referenceTest e base } :
            LG21AccessStudentInfo ℝ Base Test))
  interval_meas :
    ∀ e base,
      MeasurableSet
        {info : LG21AccessStudentInfo ℝ Base Test |
          info.base = base ∧
            lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
              info.skill ∧
            info.skill <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21AffineSkillPBOCutoff
                  intercept slope pboThreshold e base)}
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE
        (lg21ReportRequiredGaussianInfoMeasure
          (referenceTest e) (actorLaw e))
        (lg21ReportRequiredBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21AffineSkillPBOCutoff
                      intercept slope pboThreshold e base)) +
                actor)
          (estimationConsistent e))

/--
The report-required finite-base a.e. affine-skill `P_BO` certificate is
inconsistent on nonempty domains.
-/
theorem LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate.false_of_nonempty
    {Base Test Equilibrium : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    [Nonempty Base] [Nonempty Equilibrium]
    {PBO : Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := Equilibrium) PBO) :
    False := by
  refine
    lg21ReportRequiredAffineSkillPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
      (fun e =>
        lg21ReportRequiredGaussianInfoMeasure
          (C.referenceTest e) (C.actorLaw e))
      PBO C.takeDecision C.reportDecision C.estimationConsistent C.actorLaw
      C.intercept C.slope C.pboThreshold C.slope_pos C.pbo_eq
      C.take_threshold ?_ C.sourceEquilibriumAE
  intro e base0
  exact
    lg21ReportRequiredGaussianInfoMeasure_marginal_interval
      (C.referenceTest e) (C.actorLaw e)
      (fun base =>
        lg21AffineSkillPBOCutoff C.intercept C.slope C.pboThreshold e base)
      (fun base =>
        GaussianHazardCertificate.normalUpperTailMean
          standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
          (C.actorLaw e base)
          (lg21AffineSkillPBOCutoff
            C.intercept C.slope C.pboThreshold e base))
      base0 (C.info_meas e) (C.interval_meas e base0)

/--
Section 3 optional-reporting fairness-impossibility wrapper from the repaired
finite-base a.e. Gaussian posterior `P_BO` certificate route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_finite_base_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hfair
    exact False.elim
      (LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate.false_of_nonempty
        C)

/--
No-relevance form of the optional-reporting finite-base a.e. certificate route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_finite_base_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k)
    (_hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hrel
    exact
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate.false_of_nonempty
        C

/--
Package the optional-reporting finite-base a.e. Gaussian posterior `P_BO` route
as a reusable continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_finite_base_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_finite_base_gaussian_posterior_pbo_ae_certificate
      (S := S) C).2

/--
Iff form of the optional-reporting finite-base a.e. Gaussian posterior `P_BO`
route using the named law-level observable-identity certificate.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_iff_no_test_relevance_of_finite_base_gaussian_posterior_pbo_ae_certificate_observableIdentities
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingFiniteBaseGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k)
    (I : LG21LawFullFeatureBaseOnlyObservableIdentities S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_finite_base_gaussian_posterior_pbo_ae_certificate
      (S := S) C)
    I

/--
Section 3 report-required fairness-impossibility wrapper from the repaired
finite-base a.e. affine-skill `P_BO` certificate route.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_finite_base_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hfair
    exact False.elim
      (LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate.false_of_nonempty
        C)

/--
No-relevance form of the report-required finite-base a.e. certificate route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_finite_base_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO)
    (_hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hrel
    exact
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate.false_of_nonempty
        C

/--
Package the report-required finite-base a.e. affine-skill `P_BO` route as a
reusable continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_finite_base_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_finite_base_affine_skill_pbo_ae_certificate
      (S := S) C).2

/--
Iff form of the report-required finite-base a.e. affine-skill `P_BO` route
using the named law-level observable-identity certificate.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_iff_no_test_relevance_of_finite_base_affine_skill_pbo_ae_certificate_observableIdentities
    {Base Test Law : Type*}
    [Fintype Base] [DecidableEq Base]
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredFiniteBaseAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO)
    (I : LG21LawFullFeatureBaseOnlyObservableIdentities S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_finite_base_affine_skill_pbo_ae_certificate
      (S := S) C)
    I

/--
Compact a.e. certificate for the optional-reporting Gaussian posterior `P_BO`
upper-tail contradiction.  Unlike the older pointwise source-equilibrium
certificate, this records the realized type law and the Gaussian marginal law
needed by the repaired Theorem 3.2 route.
-/
structure LG21OptionalReportingGaussianPosteriorPBOAECertificate
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature) where
  μ : Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ)
  takeDecision : Equilibrium → Skill → Base → Bool
  reportDecision : Equilibrium → Base → ℝ → Bool
  estimationConsistent : Equilibrium → Prop
  actorLaw : Equilibrium → Base → GaussianScaleLaw
  pboThreshold : Equilibrium → Base → ℝ
  pbo_eq : ∀ base obs, PBO base obs = (M base).posteriorMean obs
  report_threshold :
    ∀ e base actor, reportDecision e base actor = true ↔
      pboThreshold e base ≤ PBO base (Function.update (theta base) k actor)
  gaussian_marginal :
    ∀ e base0,
      μ e {info |
        info.base = base0 ∧
          lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base0 ≤
            info.test ∧
          info.test <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base0)
              (lg21GaussianPosteriorMeanPBOCutoff
                M theta k pboThreshold e base0)} =
        (actorLaw e base0).toMeasure
          (Set.Ico
            (lg21GaussianPosteriorMeanPBOCutoff
              M theta k pboThreshold e base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base0)
              (lg21GaussianPosteriorMeanPBOCutoff
                M theta k pboThreshold e base0)))
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE (μ e)
        (lg21OptionalReportingBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base))))
          (estimationConsistent e))

/-- The optional-reporting a.e. Gaussian posterior `P_BO` certificate is inconsistent on nonempty domains. -/
theorem LG21OptionalReportingGaussianPosteriorPBOAECertificate.false_of_nonempty
    {Feature Skill Base Equilibrium : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    [Nonempty Base] [Nonempty Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := Equilibrium) PBO M theta k) :
    False :=
  lg21OptionalReportingGaussianPosteriorPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    C.μ PBO M theta k C.takeDecision C.reportDecision
    C.estimationConsistent C.actorLaw C.pboThreshold C.pbo_eq
    C.report_threshold C.gaussian_marginal C.sourceEquilibriumAE

/--
Section 3 optional-reporting fairness-impossibility wrapper from the repaired
generic a.e. Gaussian posterior `P_BO` certificate route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hfair
    exact False.elim
      (LG21OptionalReportingGaussianPosteriorPBOAECertificate.false_of_nonempty
        C)

/--
No-relevance form of the optional-reporting generic a.e. Gaussian posterior
`P_BO` certificate route.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_no_test_relevance_of_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k)
    (_hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hrel
    exact
      LG21OptionalReportingGaussianPosteriorPBOAECertificate.false_of_nonempty
        C

/--
Package the optional-reporting generic a.e. Gaussian posterior `P_BO` route as
the reusable continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_gaussian_posterior_pbo_ae_certificate
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_ae_certificate
      (S := S) C).2

/--
Iff form of the optional-reporting generic a.e. Gaussian posterior `P_BO`
route using the named law-level observable-identity certificate.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_iff_no_test_relevance_of_gaussian_posterior_pbo_ae_certificate_observableIdentities
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (C :
      LG21OptionalReportingGaussianPosteriorPBOAECertificate
        (Skill := Skill) (Equilibrium := S.Equilibrium) PBO M theta k)
    (I : LG21LawFullFeatureBaseOnlyObservableIdentities S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_gaussian_posterior_pbo_ae_certificate
      (S := S) C)
    I

/--
Compact a.e. certificate for the report-required affine-skill `P_BO` upper-tail
contradiction.
-/
structure LG21ReportRequiredAffineSkillPBOAECertificate
    {Base Test Equilibrium : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (PBO : Equilibrium → Base → ℝ → ℝ) where
  μ : Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test)
  takeDecision : Equilibrium → ℝ → Base → Bool
  reportDecision : Equilibrium → Base → Test → Bool
  estimationConsistent : Equilibrium → Prop
  actorLaw : Equilibrium → Base → GaussianScaleLaw
  intercept : Equilibrium → Base → ℝ
  slope : Equilibrium → Base → ℝ
  pboThreshold : Equilibrium → Base → ℝ
  slope_pos : ∀ e base, 0 < slope e base
  pbo_eq : lg21AffineSkillPBOFormula PBO intercept slope
  take_threshold :
    ∀ e base skill, takeDecision e skill base = true ↔
      pboThreshold e base ≤ PBO e base skill
  gaussian_marginal :
    ∀ e base0,
      μ e {info |
        info.base = base0 ∧
          lg21AffineSkillPBOCutoff intercept slope pboThreshold e base0 ≤
            info.skill ∧
          info.skill <
            GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base0)
              (lg21AffineSkillPBOCutoff
                intercept slope pboThreshold e base0)} =
        (actorLaw e base0).toMeasure
          (Set.Ico
            (lg21AffineSkillPBOCutoff intercept slope pboThreshold e base0)
            (GaussianHazardCertificate.normalUpperTailMean
              standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
              (actorLaw e base0)
              (lg21AffineSkillPBOCutoff
                intercept slope pboThreshold e base0)))
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE (μ e)
        (lg21ReportRequiredBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21AffineSkillPBOCutoff
                      intercept slope pboThreshold e base)) +
                actor)
          (estimationConsistent e))

/-- The report-required a.e. affine-skill `P_BO` certificate is inconsistent on nonempty domains. -/
theorem LG21ReportRequiredAffineSkillPBOAECertificate.false_of_nonempty
    {Base Test Equilibrium : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    [Nonempty Base] [Nonempty Equilibrium]
    {PBO : Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := Equilibrium) PBO) :
    False :=
  lg21ReportRequiredAffineSkillPBO_threshold_family_not_sourceEquilibriumAE_of_gaussian_upper_tail_marginal_interval_law
    C.μ PBO C.takeDecision C.reportDecision C.estimationConsistent
    C.actorLaw C.intercept C.slope C.pboThreshold C.slope_pos C.pbo_eq
    C.take_threshold C.gaussian_marginal C.sourceEquilibriumAE

/--
Section 3 report-required fairness-impossibility wrapper from the repaired
generic a.e. affine-skill `P_BO` certificate route.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      (lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S →
        lg21SourceLawTestBlank S) := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hfair
    exact False.elim
      (LG21ReportRequiredAffineSkillPBOAECertificate.false_of_nonempty C)

/--
No-relevance form of the report-required generic a.e. affine-skill `P_BO`
certificate route.
-/
theorem paper_theorem3_2_section3_law_report_required_no_test_relevance_of_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO)
    (_hfair :
      lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test := by
  refine ⟨?_, ?_⟩
  · intro base test action
    exact
      LG21SchoolInformationSet.fromAccessAction_accessStatus_of_unobserved
        base test action
  · intro _hrel
    exact
      LG21ReportRequiredAffineSkillPBOAECertificate.false_of_nonempty C

/--
Package the report-required generic a.e. affine-skill `P_BO` route as the
reusable continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_affine_skill_pbo_ae_certificate
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_skill_pbo_ae_certificate
      (S := S) C).2

/--
Iff form of the report-required generic a.e. affine-skill `P_BO` route using
the named law-level observable-identity certificate.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_iff_no_test_relevance_of_affine_skill_pbo_ae_certificate_observableIdentities
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    [Nonempty Base] [Nonempty S.Equilibrium]
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (C :
      LG21ReportRequiredAffineSkillPBOAECertificate
        (Base := Base) (Test := Test) (Equilibrium := S.Equilibrium) PBO)
    (I : LG21LawFullFeatureBaseOnlyObservableIdentities S) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_affine_skill_pbo_ae_certificate
      (S := S) C)
    I

/--
Optional-reporting source-law model for the repaired a.e. Gaussian posterior
`P_BO` route.  Unlike the compact contradiction certificate, the Gaussian
upper-tail marginal-law field is required only at nonblank base/test profiles,
which matches the Theorem 3.2 proof by contradiction.
-/
structure LG21OptionalReportingGaussianPosteriorPBOAESourceLawModel
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    (S : LG21SourceLawPolicySurface Skill Base Test Law)
    (PBO : Base → (Feature → ℝ) → ℝ)
    (M : Base → GaussianOffsetSignalFamily Feature)
    (theta : Base → Feature → ℝ) (k : Feature) where
  μ : S.Equilibrium → Measure (LG21AccessStudentInfo Skill Base ℝ)
  takeDecision : S.Equilibrium → Skill → Base → Bool
  reportDecision : S.Equilibrium → Base → ℝ → Bool
  estimationConsistent : S.Equilibrium → Prop
  actorLaw : S.Equilibrium → Base → GaussianScaleLaw
  pboThreshold : S.Equilibrium → Base → ℝ
  pbo_eq : ∀ base obs, PBO base obs = (M base).posteriorMean obs
  report_threshold :
    ∀ e base actor, reportDecision e base actor = true ↔
      pboThreshold e base ≤ PBO base (Function.update (theta base) k actor)
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE (μ e)
        (lg21OptionalReportingBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            (M base).posteriorMean (Function.update (theta base) k actor))
          (fun base =>
            (M base).posteriorMean
              (Function.update (theta base) k
                (GaussianHazardCertificate.normalUpperTailMean
                  standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                  (actorLaw e base)
                  (lg21GaussianPosteriorMeanPBOCutoff
                    M theta k pboThreshold e base))))
          (estimationConsistent e))
  gaussian_marginal_of_nonblank :
    ∀ e base test,
      S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
        μ e {info |
          info.base = base ∧
            lg21GaussianPosteriorMeanPBOCutoff M theta k pboThreshold e base ≤
              info.test ∧
            info.test <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)} =
          (actorLaw e base).toMeasure
            (Set.Ico
              (lg21GaussianPosteriorMeanPBOCutoff
                M theta k pboThreshold e base)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21GaussianPosteriorMeanPBOCutoff
                  M theta k pboThreshold e base)))
  observableIdentities :
    LG21LawFullFeatureBaseOnlyObservableIdentities S

/--
The optional-reporting repaired a.e. Gaussian `P_BO` source-law model packages
the continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_optional_reporting_gaussian_posterior_pbo_ae_source_law_model
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (B :
      LG21OptionalReportingGaussianPosteriorPBOAESourceLawModel
        S PBO M theta k) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_optional_reporting_fairness_impossibility_of_gaussian_posterior_pbo_source_equilibriumAE_gaussian_marginal_law
      B.μ PBO M theta k B.takeDecision B.reportDecision
      B.estimationConsistent B.actorLaw B.pboThreshold B.pbo_eq
      B.report_threshold B.sourceEquilibriumAE
      B.gaussian_marginal_of_nonblank).2

/--
Section 3 optional-reporting Theorem 3.2 from a single repaired a.e.
source-law model: hidden access holds, and fairness is equivalent to no test
relevance.
-/
theorem paper_theorem3_2_section3_law_optional_reporting_fairness_iff_no_test_relevance_of_gaussian_posterior_pbo_ae_source_law_model
    {Feature Skill Base Test Law : Type*}
    [Fintype Feature] [DecidableEq Feature]
    [MeasurableSpace (LG21AccessStudentInfo Skill Base ℝ)]
    {S : LG21SourceLawPolicySurface Skill Base Test Law}
    {PBO : Base → (Feature → ℝ) → ℝ}
    {M : Base → GaussianOffsetSignalFamily Feature}
    {theta : Base → Feature → ℝ} {k : Feature}
    (B :
      LG21OptionalReportingGaussianPosteriorPBOAESourceLawModel
        S PBO M theta k) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_optional_reporting_gaussian_posterior_pbo_ae_source_law_model
      B)
    B.observableIdentities

/--
Report-required source-law model for the repaired a.e. affine-skill `P_BO`
route, again requiring the Gaussian upper-tail marginal law only at nonblank
base/test profiles.
-/
structure LG21ReportRequiredAffineSkillPBOAESourceLawModel
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    (S : LG21SourceLawPolicySurface ℝ Base Test Law)
    (PBO : S.Equilibrium → Base → ℝ → ℝ) where
  μ : S.Equilibrium → Measure (LG21AccessStudentInfo ℝ Base Test)
  takeDecision : S.Equilibrium → ℝ → Base → Bool
  reportDecision : S.Equilibrium → Base → Test → Bool
  estimationConsistent : S.Equilibrium → Prop
  actorLaw : S.Equilibrium → Base → GaussianScaleLaw
  intercept : S.Equilibrium → Base → ℝ
  slope : S.Equilibrium → Base → ℝ
  pboThreshold : S.Equilibrium → Base → ℝ
  slope_pos : ∀ e base, 0 < slope e base
  pbo_eq : lg21AffineSkillPBOFormula PBO intercept slope
  take_threshold :
    ∀ e base skill, takeDecision e skill base = true ↔
      pboThreshold e base ≤ PBO e base skill
  sourceEquilibriumAE :
    ∀ e,
      lg21SourceEquilibriumAE (μ e)
        (lg21ReportRequiredBaseSourceEquilibriumData
          (takeDecision e) (reportDecision e)
          (fun base actor =>
            ((1 / 2 : ℝ) -
                  GaussianHazardCertificate.normalUpperTailMean
                    standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                    (actorLaw e base)
                    (lg21AffineSkillPBOCutoff
                      intercept slope pboThreshold e base)) +
                actor)
          (estimationConsistent e))
  gaussian_marginal_of_nonblank :
    ∀ e base test,
      S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test →
        μ e {info |
          info.base = base ∧
            lg21AffineSkillPBOCutoff intercept slope pboThreshold e base ≤
              info.skill ∧
            info.skill <
              GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21AffineSkillPBOCutoff
                  intercept slope pboThreshold e base)} =
          (actorLaw e base).toMeasure
            (Set.Ico
              (lg21AffineSkillPBOCutoff intercept slope pboThreshold e base)
              (GaussianHazardCertificate.normalUpperTailMean
                standardGaussianHazardInverseCertificate.toGaussianHazardCertificate
                (actorLaw e base)
                (lg21AffineSkillPBOCutoff
                  intercept slope pboThreshold e base)))
  observableIdentities :
    LG21LawFullFeatureBaseOnlyObservableIdentities S

/--
The report-required repaired a.e. affine-skill `P_BO` source-law model
packages the continuous-law Theorem 3.2 fairness-impossibility certificate.
-/
def paper_theorem3_2_law_fairness_impossibility_certificate_of_report_required_affine_skill_pbo_ae_source_law_model
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (B : LG21ReportRequiredAffineSkillPBOAESourceLawModel S PBO) :
    LG21LawFairnessImpossibilityCertificate S where
  latent_or_observable_implies_test_blank :=
    (paper_theorem3_2_section3_law_report_required_fairness_impossibility_of_affine_pbo_source_equilibriumAE_gaussian_marginal_law
      B.μ PBO B.takeDecision B.reportDecision B.estimationConsistent
      B.actorLaw B.intercept B.slope B.pboThreshold B.slope_pos B.pbo_eq
      B.take_threshold B.sourceEquilibriumAE
      B.gaussian_marginal_of_nonblank).2

/--
Section 3 report-required Theorem 3.2 from a single repaired a.e. source-law
model: hidden access holds, and fairness is equivalent to no test relevance.
-/
theorem paper_theorem3_2_section3_law_report_required_fairness_iff_no_test_relevance_of_affine_skill_pbo_ae_source_law_model
    {Base Test Law : Type*}
    [MeasurableSpace (LG21AccessStudentInfo ℝ Base Test)]
    {S : LG21SourceLawPolicySurface ℝ Base Test Law}
    {PBO : S.Equilibrium → Base → ℝ → ℝ}
    (B : LG21ReportRequiredAffineSkillPBOAESourceLawModel S PBO) :
    (∀ (base : Base) (test : Test) (action : LG21AccessAction),
        (LG21SchoolInformationSet.fromAccessAction false base test action).accessStatus =
          none) ∧
      ((lg21SourceLawLatentSkillFair S ∨ lg21SourceLawObservablyFair S) ↔
        ¬ ∃ e base test, S.baseOnlyLaw e base ≠ S.fullFeatureLaw e base test) :=
  paper_theorem3_2_section3_law_fairness_iff_no_test_relevance_of_certificate_and_observableIdentities
    (paper_theorem3_2_law_fairness_impossibility_certificate_of_report_required_affine_skill_pbo_ae_source_law_model
      B)
    B.observableIdentities

end

end LG21TestOptionalPolicies
