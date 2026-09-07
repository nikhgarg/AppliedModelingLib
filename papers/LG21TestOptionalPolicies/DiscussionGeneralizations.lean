import LG21TestOptionalPolicies.ContinuousPopulation
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Discussion generalizations for LG21

The paper makes two mathematical claims outside the named theorem sequence:

* every fairness result can instead condition on observed reporting `X` rather
  than latent access `Z`; and
* replacing expected-estimate utility by admission-probability utility leaves
  the results unchanged under appropriate tie-breaking, except in the
  report-required-after-testing regime where downside risk can change the
  taking decision.

This file makes the exact transport content explicit.  Reporting-conditioned
law surfaces are isomorphic to the access-conditioned law surface after
renaming the two comparison groups.  Admission objectives preserve every
choice equilibrium exactly when the tie-broken admission payoff preserves and
reflects the action ordering at each information state.  The latter condition
deliberately does not cover the source's stated downside-risk exception.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib

/-! ## Conditioning on reporting instead of access -/

/--
The source Definitions 2--5 with the comparison groups indexed by observed
reporting `X` rather than access `Z`.
-/
structure LG21ReportingConditionedLawPolicySurface
    (Skill Base Test Law : Type*) where
  Equilibrium : Type*
  latentReporterLaw : Equilibrium → Skill → Base → Law
  latentNonreporterLaw : Equilibrium → Skill → Base → Law
  observableReporterLaw : Equilibrium → Base → Law
  observableNonreporterLaw : Equilibrium → Base → Law
  demographicReporterLaw : Equilibrium → Law
  demographicNonreporterLaw : Equilibrium → Law
  baseOnlyLaw : Equilibrium → Base → Law
  fullFeatureLaw : Equilibrium → Base → Test → Law

/-- Rename reporter/nonreporter laws as the two groups of the generic source surface. -/
def LG21ReportingConditionedLawPolicySurface.toSourceLawSurface
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) :
    LG21SourceLawPolicySurface Skill Base Test Law where
  Equilibrium := R.Equilibrium
  latentAccessLaw := R.latentReporterLaw
  latentNoAccessLaw := R.latentNonreporterLaw
  observableAccessLaw := R.observableReporterLaw
  observableNoAccessLaw := R.observableNonreporterLaw
  demographicAccessLaw := R.demographicReporterLaw
  demographicNoAccessLaw := R.demographicNonreporterLaw
  baseOnlyLaw := R.baseOnlyLaw
  fullFeatureLaw := R.fullFeatureLaw

/-- Rename the two groups of a generic source law surface as reporter/nonreporter. -/
def LG21ReportingConditionedLawPolicySurface.ofSourceLawSurface
    {Skill Base Test Law : Type*}
    (S : LG21SourceLawPolicySurface Skill Base Test Law) :
    LG21ReportingConditionedLawPolicySurface Skill Base Test Law where
  Equilibrium := S.Equilibrium
  latentReporterLaw := S.latentAccessLaw
  latentNonreporterLaw := S.latentNoAccessLaw
  observableReporterLaw := S.observableAccessLaw
  observableNonreporterLaw := S.observableNoAccessLaw
  demographicReporterLaw := S.demographicAccessLaw
  demographicNonreporterLaw := S.demographicNoAccessLaw
  baseOnlyLaw := S.baseOnlyLaw
  fullFeatureLaw := S.fullFeatureLaw

/--
Replacing conditioning on `Z` by conditioning on `X` is an exact isomorphism
of the law-level theorem surface, so every result stated solely through
Definitions 2--5 transports without an additional mathematical premise.
-/
def paper_reporting_conditioned_all_law_results_surface_equiv
    (Skill Base Test Law : Type*) :
    LG21ReportingConditionedLawPolicySurface Skill Base Test Law ≃
      LG21SourceLawPolicySurface Skill Base Test Law where
  toFun := LG21ReportingConditionedLawPolicySurface.toSourceLawSurface
  invFun := LG21ReportingConditionedLawPolicySurface.ofSourceLawSurface
  left_inv := by
    intro R
    cases R
    rfl
  right_inv := by
    intro S
    cases S
    rfl

/-- Definition 2 with conditioning on reporting. -/
def lg21ReportingConditionedLatentSkillFair
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e skill base,
    R.latentReporterLaw e skill base = R.latentNonreporterLaw e skill base

/-- Definition 3 with conditioning on reporting. -/
def lg21ReportingConditionedObservablyFair
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base,
    R.observableReporterLaw e base = R.observableNonreporterLaw e base

/-- Definition 4 with conditioning on reporting. -/
def lg21ReportingConditionedDemographicallyFair
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e, R.demographicReporterLaw e = R.demographicNonreporterLaw e

/-- Definition 5 is unchanged by which group variable is used for fairness. -/
def lg21ReportingConditionedTestBlank
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) : Prop :=
  ∀ e base test, R.baseOnlyLaw e base = R.fullFeatureLaw e base test

/-- Exact transport of Definition 2 under the reporting/access surface isomorphism. -/
theorem paper_reporting_conditioned_latent_skill_fair_iff
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) :
    lg21ReportingConditionedLatentSkillFair R ↔
      lg21SourceLawLatentSkillFair R.toSourceLawSurface := by
  rfl

/-- Exact transport of Definition 3 under the reporting/access surface isomorphism. -/
theorem paper_reporting_conditioned_observably_fair_iff
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) :
    lg21ReportingConditionedObservablyFair R ↔
      lg21SourceLawObservablyFair R.toSourceLawSurface := by
  rfl

/-- Exact transport of Definition 4 under the reporting/access surface isomorphism. -/
theorem paper_reporting_conditioned_demographically_fair_iff
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) :
    lg21ReportingConditionedDemographicallyFair R ↔
      lg21SourceLawDemographicallyFair R.toSourceLawSurface := by
  rfl

/-- Exact transport of Definition 5 under the reporting/access surface isomorphism. -/
theorem paper_reporting_conditioned_test_blank_iff
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law) :
    lg21ReportingConditionedTestBlank R ↔
      lg21SourceLawTestBlank R.toSourceLawSurface := by
  rfl

/--
The corresponding reporting-conditioned fairness failures follow directly
from one unequal law at each of the three conditioning levels.
-/
theorem paper_reporting_conditioned_all_fairness_fail_of_law_witnesses
    {Skill Base Test Law : Type*}
    (R : LG21ReportingConditionedLawPolicySurface Skill Base Test Law)
    (hlatent :
      ∃ e skill base,
        R.latentReporterLaw e skill base ≠ R.latentNonreporterLaw e skill base)
    (hobservable :
      ∃ e base,
        R.observableReporterLaw e base ≠ R.observableNonreporterLaw e base)
    (hdemographic :
      ∃ e, R.demographicReporterLaw e ≠ R.demographicNonreporterLaw e) :
    ¬ lg21ReportingConditionedLatentSkillFair R ∧
      ¬ lg21ReportingConditionedObservablyFair R ∧
        ¬ lg21ReportingConditionedDemographicallyFair R := by
  rcases hlatent with ⟨e, skill, base, hne⟩
  rcases hobservable with ⟨eObs, baseObs, hneObs⟩
  rcases hdemographic with ⟨eDemo, hneDemo⟩
  exact
    ⟨fun hfair => hne (hfair e skill base),
      fun hfair => hneObs (hfair eObs baseObs),
      fun hfair => hneDemo (hfair eDemo)⟩

/-! ## Admission-probability objective -/

/-- Replace only the payoff of a static source choice problem. -/
def lg21ChoiceProblemWithAdmissionPayoff
    {Info Action : Type*}
    (E : ChoiceEquilibriumData Info Action)
    (admissionPayoff : Info → Action → ℝ) :
    ChoiceEquilibriumData Info Action where
  actionFeasible := E.actionFeasible
  chosenAction := E.chosenAction
  payoff := admissionPayoff
  consistency := E.consistency

/--
Formal meaning of the Discussion's “appropriate tie-breaking”: at each
information state, admission-probability payoff preserves and reflects the
weak ordering of every pair of feasible actions by expected estimate.
-/
def lg21AdmissionPayoffOrderEquivalent
    {Info Action : Type*}
    (E : ChoiceEquilibriumData Info Action)
    (admissionPayoff : Info → Action → ℝ) : Prop :=
  ∀ info left right,
    admissionPayoff info left ≤ admissionPayoff info right ↔
      E.payoff info left ≤ E.payoff info right

/--
Under order-equivalent tie-breaking, changing the student objective from
expected estimate to admission probability preserves the entire equilibrium
set.  Thus every result quantified over equilibria transfers unchanged in the
source regimes where this order equivalence holds.  The theorem intentionally
does not assume it for report-required-after-testing, the downside-risk
exception identified by the paper.
-/
theorem paper_admission_probability_objective_preserves_equilibria
    {Info Action : Type*}
    (E : ChoiceEquilibriumData Info Action)
    (admissionPayoff : Info → Action → ℝ)
    (horder : lg21AdmissionPayoffOrderEquivalent E admissionPayoff) :
    IsChoiceEquilibrium
        (lg21ChoiceProblemWithAdmissionPayoff E admissionPayoff) ↔
      IsChoiceEquilibrium E := by
  constructor
  · rintro ⟨hfeasible, hbest, hconsistency⟩
    refine ⟨hfeasible, ?_, hconsistency⟩
    intro info action haction
    exact
      (horder info action (E.chosenAction info)).1
        (hbest info action haction)
  · rintro ⟨hfeasible, hbest, hconsistency⟩
    refine ⟨hfeasible, ?_, hconsistency⟩
    intro info action haction
    exact
      (horder info action (E.chosenAction info)).2
        (hbest info action haction)

end

end LG21TestOptionalPolicies
