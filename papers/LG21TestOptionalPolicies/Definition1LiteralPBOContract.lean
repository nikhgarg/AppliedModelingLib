import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium
import LG21TestOptionalPolicies.ObservedAccessVoluntarySelfEnforcingCandidates
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43Nonvacuity

/-!
# Literal Definition 1 PBO contracts for LG21

The old static `LG21SourceEquilibriumData` interface stored estimation
consistency in an arbitrary proposition.  This file supplies the source-facing
replacement used by review: the source-timed actions, feasibility, actual
conditional-expectation semantics, and response obligations are all written
as Lean propositions.  In particular, there is no generic consistency slot.

The source has two observation regimes.  Section 3 hides access and therefore
uses a PBO on the literal whole population.  Section 4 conditions on the
literal access population; its optional-reporting contract uses the approved
positive-mass operational convention, so it never evaluates a no-report PBO
or a cross-branch payoff at an unattained branch.

These are PBO contracts.  They do not claim to formalize every arbitrary
randomized non-Bayesian policy mentioned in the paper, and the Section 4
contract does not claim that bare static-RCD Definition 1 implies the
operational active-branch selection.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Section 3: hidden access -/

/-- Interpret the literal Boolean access coordinate in the source action
model. -/
def lg21HiddenAccessActualStatus
    {Feature : Type*}
    (student : Bool × (ℝ × (Feature → ℝ))) : LG21AccessStatus :=
  if student.1 = true then LG21AccessStatus.access else LG21AccessStatus.noAccess

/-- The literal action actually observed in the hidden-access optional
protocol.  Reporting is gated by both access and the pre-score taking action,
so `Z >= Y >= X` is a theorem of the construction rather than an assumption
about independently supplied Boolean functions. -/
def lg21HiddenAccessOptionalActualAction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) : LG21AccessAction where
  takesTest :=
    if student.1 = true then
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)
    else false
  reportsScore :=
    lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
      E.reportDecision student

/-- Feasibility of the actual hidden-access action under the optional policy.
This is pointwise because the action constructor itself gates reporting by
taking and gives no-access students the no-take action. -/
theorem lg21HiddenAccessOptionalActualAction_feasible
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) :
    LG21RequirementPolicy.feasibleAction LG21RequirementPolicy.noRequirements
      (lg21HiddenAccessActualStatus student)
      (lg21HiddenAccessOptionalActualAction E student) := by
  cases haccess : student.1 with
  | false =>
      have hnotAccess : student.1 ≠ true := by simp [haccess]
      rw [lg21HiddenAccessActualStatus, if_neg hnotAccess]
      refine (LG21RequirementPolicy.feasibleAction_noAccess_iff
        LG21RequirementPolicy.noRequirements
        (lg21HiddenAccessOptionalActualAction E student)).2 ?_
      simpa [lg21HiddenAccessOptionalActualAction,
        lg21HiddenAccessOptionalObservedAction, haccess, hnotAccess,
        LG21AccessAction.noTake]
  | true =>
      rw [lg21HiddenAccessActualStatus, if_pos haccess]
      refine (LG21RequirementPolicy.feasibleAction_access_noRequirements_iff
        (lg21HiddenAccessOptionalActualAction E student)).2 ?_
      refine (LG21AccessAction.optionalReporting_feasible_iff_reportImpliesTake
        (lg21HiddenAccessOptionalActualAction E student)).2 ?_
      intro hreport
      change lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
        E.reportDecision student = true at hreport
      simp [lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake,
        haccess] at hreport
      simpa [lg21HiddenAccessOptionalActualAction,
        lg21ContinuousPopulationSkill, haccess] using hreport.1

/--
Section 3's literal PBO form of Definition 1, read almost everywhere on the
continuous realized source population.  The two student decisions are kept at
their source times.  The public PBO is conditioned on precisely
`(base, X, score-if-X)` and hence does not reveal access; the no-report PBO is
available only after proving positive mass of the actual `X = 0` population.
-/
def LG21HiddenAccessOptionalPBODefinition1AE
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) : Prop :=
  0 < M.accessLaw {true} ∧
    Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      E.takeDecision pair.1 pair.2) ∧
      Measurable (fun pair :
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
        E.reportDecision pair.1 pair.2) ∧
        (∀ skill base, IsProbabilityMeasure (E.testLaw skill base)) ∧
          (∀ skill base,
            Integrable (fun score =>
              if E.reportDecision base score then E.reportedPayoff base score
              else E.noReportPayoff base) (E.testLaw skill base)) ∧
            (∀ student,
              LG21RequirementPolicy.feasibleAction
                LG21RequirementPolicy.noRequirements
                (lg21HiddenAccessActualStatus student)
                (lg21HiddenAccessOptionalActualAction E student)) ∧
              NoProfitableBinaryChoiceDeviationAE
                (lg21HiddenAccessAccessLatentBaseLaw M testFeature)
                (fun profile => E.takeDecision profile.1 profile.2 = true)
                (fun profile => ∫ score,
                  if E.reportDecision profile.2 score then
                    E.reportedPayoff profile.2 score
                  else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2)
                (fun profile => E.noReportPayoff profile.2) ∧
                NoProfitableBinaryChoiceDeviationAE
                  (lg21HiddenAccessAccessBaseScoreLaw M testFeature)
                  (fun profile => E.reportDecision profile.1 profile.2 = true)
                  (fun profile => E.reportedPayoff profile.1 profile.2)
                  (fun profile => E.noReportPayoff profile.1) ∧
                  LG21HiddenAccessActualPublicPBO M testFeature
                    E.takeDecision E.reportDecision E.reportedPayoff
                    E.noReportPayoff ∧
                    LG21HiddenAccessActualNoReportPBO M testFeature
                      E.takeDecision E.reportDecision E.noReportPayoff

/-- The literal hidden-access carrier plus the optional score-stage response
obligation realizes the explicit Definition 1 contract above. -/
theorem lg21HiddenAccessLiteralSourceEquilibriumAE_satisfies_definition1PBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreport : E.OptionalReportBestResponseAE) :
    LG21HiddenAccessOptionalPBODefinition1AE E := by
  refine ⟨E.access_positive, E.takeDecision_measurable,
    E.reportDecision_measurable, E.testLaw_isProbability,
    E.continuationPayoff_integrable, ?_, E.take_best_response_ae,
    E.optionalReportBestResponse_ae hreport, E.public_pbo, E.noReport_pbo⟩
  intro student
  exact lg21HiddenAccessOptionalActualAction_feasible E student

theorem LG21HiddenAccessOptionalPBODefinition1AE.feasible
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature}
    (h : LG21HiddenAccessOptionalPBODefinition1AE E) :
    ∀ student,
      LG21RequirementPolicy.feasibleAction
        LG21RequirementPolicy.noRequirements
        (lg21HiddenAccessActualStatus student)
        (lg21HiddenAccessOptionalActualAction E student) := by
  rcases h with ⟨_, _, _, _, _, hfeasible, _, _, _, _⟩
  exact hfeasible

theorem LG21HiddenAccessOptionalPBODefinition1AE.take_best_response_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature}
    (h : LG21HiddenAccessOptionalPBODefinition1AE E) :
    NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessLatentBaseLaw M testFeature)
      (fun profile => E.takeDecision profile.1 profile.2 = true)
      (fun profile => ∫ score,
        if E.reportDecision profile.2 score then
          E.reportedPayoff profile.2 score
        else E.noReportPayoff profile.2 ∂E.testLaw profile.1 profile.2)
      (fun profile => E.noReportPayoff profile.2) := by
  rcases h with ⟨_, _, _, _, _, _, htake, _, _, _⟩
  exact htake

theorem LG21HiddenAccessOptionalPBODefinition1AE.report_best_response_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature}
    (h : LG21HiddenAccessOptionalPBODefinition1AE E) :
    NoProfitableBinaryChoiceDeviationAE
      (lg21HiddenAccessAccessBaseScoreLaw M testFeature)
      (fun profile => E.reportDecision profile.1 profile.2 = true)
      (fun profile => E.reportedPayoff profile.1 profile.2)
      (fun profile => E.noReportPayoff profile.1) := by
  rcases h with ⟨_, _, _, _, _, _, _, hreport, _, _⟩
  exact hreport

theorem LG21HiddenAccessOptionalPBODefinition1AE.public_pbo
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature}
    (h : LG21HiddenAccessOptionalPBODefinition1AE E) :
    LG21HiddenAccessActualPublicPBO M testFeature E.takeDecision
      E.reportDecision E.reportedPayoff E.noReportPayoff := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hpublic, _⟩
  exact hpublic

theorem LG21HiddenAccessOptionalPBODefinition1AE.noReport_pbo_if_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    {E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature}
    (h : LG21HiddenAccessOptionalPBODefinition1AE E) :
    LG21HiddenAccessActualNoReportPBO M testFeature E.takeDecision
      E.reportDecision E.noReportPayoff := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hnoReport⟩
  exact hnoReport

/-! ## Section 4: observed access, optional reporting -/

/-- Actual source action on the positive-access population in Section 4.
`reportsScore` is only true after the pre-score taking action, so feasibility
does not rely on an off-path report value. -/
def lg21ObservedAccessOptionalActualAction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) : LG21AccessAction where
  takesTest := E.actions.takeDecision
    (lg21ContinuousPopulationSkill student)
    (lg21ContinuousPopulationBase testFeature student)
  reportsScore :=
    if E.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true then
      E.actions.reportDecision
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)
    else false

theorem lg21ObservedAccessOptionalActualAction_feasible
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) :
    LG21RequirementPolicy.feasibleAction LG21RequirementPolicy.noRequirements
      LG21AccessStatus.access
      (lg21ObservedAccessOptionalActualAction E student) := by
  refine (LG21RequirementPolicy.feasibleAction_access_noRequirements_iff
    (lg21ObservedAccessOptionalActualAction E student)).2 ?_
  refine (LG21AccessAction.optionalReporting_feasible_iff_reportImpliesTake
    (lg21ObservedAccessOptionalActualAction E student)).2 ?_
  intro hreport
  cases htake : E.actions.takeDecision
      (lg21ContinuousPopulationSkill student)
      (lg21ContinuousPopulationBase testFeature student) <;>
    simp [lg21ObservedAccessOptionalActualAction, htake] at hreport ⊢

/-- Measurability, source test law, and integrability needed to evaluate an
observed-access optional action at its two decision times. -/
def LG21ObservedAccessOptionalSourceTimedWellFormed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) : Prop :=
  Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
    E.actions.takeDecision pair.2 pair.1) ∧
    Measurable (fun pair :
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      E.actions.reportDecision pair.1 pair.2) ∧
      (∀ latentSkill publicBase,
        IsProbabilityMeasure
          (E.actions.testLaw latentSkill publicBase)) ∧
        (∀ latentSkill publicBase,
          Integrable (fun observedScore =>
            if E.actions.reportDecision publicBase observedScore then
              E.actions.reportedPayoff publicBase observedScore
            else E.actions.noReportPayoff publicBase)
            (E.actions.testLaw latentSkill publicBase)) ∧
          (∀ publicBase latentSkill,
            E.actions.testLaw latentSkill publicBase =
              gaussianReal latentSkill (M.noiseVariance testFeature))

theorem lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_wellFormed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) :
    LG21ObservedAccessOptionalSourceTimedWellFormed E :=
  ⟨E.takeDecision_measurable, E.reportDecision_measurable,
    E.actions.testLaw_isProbability, E.actions.continuationPayoff_integrable,
    E.test_law_gaussian⟩

/-- The two actual observed-access PBO equations.  The report branch observes
`(Z = 1, base, score, X = 1)` and the no-report branch observes
`(Z = 1, base, X = 0)`: `Z = 1` is represented by conditioning on the literal
positive-access population law.  Neither equation is available without its
positive-mass premise. -/
def LG21ObservedAccessOptionalActualBranchPBOs
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) : Prop :=
  (∀ hpositive : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision),
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision)) ∧
    (fun student => E.actions.reportedPayoff
      (lg21ContinuousPopulationBase testFeature student)
      (lg21ContinuousPopulationFeature testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            E.actions.takeDecision E.actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (fun student =>
              (lg21ContinuousPopulationBase testFeature student,
                lg21ContinuousPopulationFeature testFeature student))
              inferInstance]) ∧
  (∀ hpositive : 0 <
      (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision),
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision)) ∧
    (fun student => E.actions.noReportPayoff
      (lg21ContinuousPopulationBase testFeature student)) =ᵐ[
        lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21OptionalSourceNoReportEvent
            (lg21ContinuousPopulationBase testFeature)
            (lg21ContinuousPopulationFeature testFeature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            E.actions.takeDecision E.actions.reportDecision)]
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalSourceNoReportEvent
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature))
          E.actions.takeDecision E.actions.reportDecision))[
            lg21ContinuousPopulationSkill |
            MeasurableSpace.comap (lg21ContinuousPopulationBase testFeature)
              inferInstance])

theorem lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_actualBranchPBOs
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (E : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) :
    LG21ObservedAccessOptionalActualBranchPBOs E := by
  constructor
  · intro hpositive
    exact ⟨E.actual_report_integrable hpositive, E.actual_report_pbo hpositive⟩
  · intro hpositive
    exact ⟨E.actual_noReport_integrable hpositive, E.actual_noReport_pbo hpositive⟩

/-- A.e. student-response obligations for the two attained optional branches.
The no-report payoff occurs only beneath the positive-mass antecedent, so a
null branch cannot supply a fabricated best-response value. -/
def LG21ObservedAccessOptionalPositiveMassMemberResponses
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  ∀ hnoReport : 0 < (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21OptionalCandidateNoReportBranch
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) C.source_timed.actions),
    (∀ latentSkill publicBase,
      Integrable (fun observedScore =>
        lg21OptionalSourceTimedBestContinuationPayoff C.source_timed.actions
          publicBase observedScore)
        (C.source_timed.actions.testLaw latentSkill publicBase)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      (lg21OptionalCandidateReportBranch
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) C.source_timed.actions),
      C.source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      C.source_timed.actions.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student |
        C.source_timed.actions.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true ∧
        C.source_timed.actions.reportDecision
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = false},
      C.source_timed.actions.reportedPayoff
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationFeature testFeature student) ≤
      C.source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      C.source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21OptionalSourceTimedBestContinuationExpectedPayoff C.source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.source_timed.actions.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21OptionalSourceTimedBestContinuationExpectedPayoff C.source_timed.actions
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      C.source_timed.actions.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student))

/--
Section 4's optional-reporting Definition 1 contract under the declared
positive-mass operational interpretation.  Every PBO and every comparison
using a no-report payoff is guarded by positivity of the actual no-report
branch.  It also carries stability against literal positive-mass recalibrated
entries, so the contract cannot reuse the current branch's PBO for a changed
action profile.
-/
def LG21ObservedAccessOptionalPBODefinition1Operational
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  (∀ student,
    LG21RequirementPolicy.feasibleAction LG21RequirementPolicy.noRequirements
      LG21AccessStatus.access
      (lg21ObservedAccessOptionalActualAction C.source_timed student)) ∧
        LG21ObservedAccessOptionalSourceTimedWellFormed C.source_timed ∧
      0 < (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21OptionalCandidateReportBranch
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) C.source_timed.actions) ∧
        LG21ObservedAccessOptionalActualBranchPBOs C.source_timed ∧
          LG21ObservedAccessOptionalPositiveMassMemberResponses C ∧
            LG21OptionalSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature))
              ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
                ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
                  lg21ContinuousPopulationSkill_measurable))
              C.source_timed.actions.testLaw
              C.source_timed.actions.takeDecision C.source_timed.actions.reportDecision ∧
              LG21OptionalSourceStableAgainstPositiveMassRecalibratedReportEntryForTestLaw
                (lg21ContinuousGaussianAccessPopulationLaw M)
                (lg21ContinuousPopulationBase testFeature)
                (lg21ContinuousPopulationFeature testFeature)
                (lg21ContinuousPopulationSkill (Feature := Feature))
                ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
                  ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
                    lg21ContinuousPopulationSkill_measurable))
                C.source_timed.actions.testLaw
                C.source_timed.actions.takeDecision C.source_timed.actions.reportDecision

/-- Every observed-access self-enforcing positive-mass candidate supplies the
explicit operational Definition 1 contract.  This is a transparent repacking
of fields, not a conversion through the legacy `estimationConsistent : Prop`
slot. -/
theorem lg21OptionalSourceTimedPositiveMassSelfEnforcingCandidate_satisfies_definition1PBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    LG21ObservedAccessOptionalPBODefinition1Operational C := by
  refine ⟨?_, ?_, C.active_report_positive, ?_, ?_,
    C.source_timed.local_recalibrated_entry_stable,
    C.source_timed.recalibrated_report_entry_stable⟩
  · intro student
    exact lg21ObservedAccessOptionalActualAction_feasible C.source_timed student
  · exact lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_wellFormed
      C.source_timed
  · exact lg21ObservedAccessOptionalPositiveMassRefinedEquilibrium_actualBranchPBOs
      C.source_timed
  · intro hnoReport
    exact ⟨C.best_continuation_integrable_if_noReport_positive hnoReport,
      C.report_members_weakly_respond_if_noReport_positive hnoReport,
      C.withholding_members_weakly_respond_if_positive hnoReport,
      C.take_members_weakly_respond_if_noReport_positive hnoReport,
      C.noTake_members_weakly_respond_if_positive hnoReport⟩

theorem LG21ObservedAccessOptionalPBODefinition1Operational.feasible
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    {C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature}
    (h : LG21ObservedAccessOptionalPBODefinition1Operational C) :
    ∀ student,
      LG21RequirementPolicy.feasibleAction LG21RequirementPolicy.noRequirements
        LG21AccessStatus.access
        (lg21ObservedAccessOptionalActualAction C.source_timed student) := by
  rcases h with ⟨hfeasible, _, _, _, _, _, _⟩
  exact hfeasible

/-- Direct review projection for Definition 1's observed-access PBO example:
the no-report half is the second conjunct and can only be applied after its
actual branch has positive mass. -/
theorem LG21ObservedAccessOptionalPBODefinition1Operational.actual_branch_pbos
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    {C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature}
    (h : LG21ObservedAccessOptionalPBODefinition1Operational C) :
    LG21ObservedAccessOptionalActualBranchPBOs C.source_timed := by
  rcases h with ⟨_, _, _, hpbo, _, _, _⟩
  exact hpbo

theorem LG21ObservedAccessOptionalPBODefinition1Operational.member_responses
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    {C : LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature}
    (h : LG21ObservedAccessOptionalPBODefinition1Operational C) :
    LG21ObservedAccessOptionalPositiveMassMemberResponses C := by
  rcases h with ⟨_, _, _, _, hresponses, _, _⟩
  exact hresponses

/-! ## Section 4: observed access, report-required testing -/

/-- The literal source action for report-required testing.  The taking
decision is made before the score, and reporting is forced exactly when the
student takes; no score-dependent action is smuggled into the pre-score
decision. -/
def lg21ObservedAccessReportRequiredActualAction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) : LG21AccessAction where
  takesTest := C.selected.takeDecision
    (lg21ContinuousPopulationSkill student)
    (lg21ContinuousPopulationBase testFeature student)
  reportsScore := C.selected.takeDecision
    (lg21ContinuousPopulationSkill student)
    (lg21ContinuousPopulationBase testFeature student)

/-- Definition 1 feasibility for the report-required-after-taking policy is
pointwise for the source action above. -/
theorem lg21ObservedAccessReportRequiredActualAction_feasible
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature)
    (student : Bool × (ℝ × (Feature → ℝ))) :
    LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredConditionalTaking
      LG21AccessStatus.access
      (lg21ObservedAccessReportRequiredActualAction C student) := by
  refine (LG21RequirementPolicy.feasibleAction_access_reportRequiredConditionalTaking_iff _).2 ?_
  refine (LG21AccessAction.reportRequiredAfterTaking_feasible_iff _).2 ?_
  rfl

/-- The measurable, source-timed data needed to evaluate a report-required
candidate.  In particular, the action is a `(skill, base)` action and its
Gaussian score law is explicit, rather than a score-time proxy. -/
def LG21ObservedAccessReportRequiredSourceTimedWellFormed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  Measurable (lg21ContinuousPopulationBase testFeature) ∧
    Measurable (lg21ContinuousPopulationFeature testFeature) ∧
      Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) ∧
        Measurable (fun profileSkill :
            (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
          C.selected.takeDecision profileSkill.2 profileSkill.1) ∧
          Measurable (fun publicScore :
              (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
            C.selected.reportedPayoff publicScore.1 publicScore.2) ∧
            Measurable C.selected.noReportPayoff ∧
              (∀ latentSkill publicBase,
                IsProbabilityMeasure
                  (C.selected.testLaw latentSkill publicBase)) ∧
                (∀ latentSkill publicBase,
                  Integrable (C.selected.reportedPayoff publicBase)
                    (C.selected.testLaw latentSkill publicBase)) ∧
                  (∀ publicBase latentSkill,
                    C.selected.testLaw latentSkill publicBase =
                      gaussianReal latentSkill (M.noiseVariance testFeature))

/-- The report-required source carrier directly supplies all timing and
measurability obligations in the preceding contract. -/
theorem lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_wellFormed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    LG21ObservedAccessReportRequiredSourceTimedWellFormed C := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  refine ⟨C.source_timed.base_measurable, C.source_timed.score_measurable,
    C.source_timed.skill_measurable, C.source_timed.action_measurable,
    C.source_timed.reportedPayoff_measurable,
    C.source_timed.noReportPayoff_measurable,
    C.selected.testLaw_isProbability, C.selected.reportedPayoff_integrable,
    C.source_timed.test_law_gaussian⟩

/-- The actual report and no-take PBO equations of a report-required
candidate.  Both are conditional expectations on their literal action
populations and each remains behind a positive-mass guard. -/
def LG21ObservedAccessReportRequiredActualBranchPBOs
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  (∀ hpositive : 0 < (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | C.selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true}) ∧
      LG21FullPublicReportRequiredReportedPBO
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (fun publicBase latentSkill =>
          C.selected.takeDecision latentSkill publicBase)
        C.selected.reportedPayoff) ∧
    (∀ hpositive : 0 < (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21NormalizedRestriction (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | C.selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false}) ∧
      LG21FullPublicReportRequiredNoTakePBO
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature))
        (fun publicBase latentSkill =>
          C.selected.takeDecision latentSkill publicBase)
        C.selected.noReportPayoff)

/-- This bridge projects the two PBOs from the explicit source carrier; it
never reads `estimationConsistent : Prop`. -/
theorem lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_actualBranchPBOs
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    LG21ObservedAccessReportRequiredActualBranchPBOs C := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  constructor
  · intro hpositive
    exact ⟨C.source_timed.reported_integrable hpositive,
      C.source_timed.reported_pbo hpositive⟩
  · intro hpositive
    exact ⟨C.source_timed.noTake_integrable hpositive,
      C.source_timed.noTake_pbo hpositive⟩

/-- A.e. pre-score response and closure obligations for the two actual
report-required branches.  Every comparison involving the no-take payoff is
guarded by the actual no-take mass, so an empty branch cannot create a hidden
off-path payoff. -/
def LG21ObservedAccessReportRequiredPositiveMassMemberResponses
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  ∀ hnoTake : 0 < (lg21ContinuousGaussianAccessPopulationLaw M)
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      C.selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21ReportRequiredSequentialTakeExpectedPayoff C.selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21ReportRequiredSequentialTakeExpectedPayoff C.selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      C.selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = false},
      lg21ReportRequiredSequentialTakeExpectedPayoff C.selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) ≤
      C.selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student)) ∧
    (∀ᵐ student ∂(lg21ContinuousGaussianAccessPopulationLaw M).restrict
      {student | C.selected.takeDecision
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true},
      C.selected.noReportPayoff
        (lg21ContinuousPopulationBase testFeature student) ≤
      lg21ReportRequiredSequentialTakeExpectedPayoff C.selected
        (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student))

/-- The report-required self-enforcing carrier supplies every guarded
member-response and outsider-closure field directly. -/
theorem lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_memberResponses
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    LG21ObservedAccessReportRequiredPositiveMassMemberResponses C := by
  intro hnoTake
  exact ⟨C.take_members_weakly_respond_if_noTake_positive hnoTake,
    C.noTake_members_weakly_respond_if_positive hnoTake,
    C.take_outsiders_closed_under_strict_gain_if_noTake_positive hnoTake,
    C.noTake_outsiders_closed_under_strict_gain_if_positive hnoTake⟩

/-- Section 4's literal report-required Definition 1 contract under the
approved positive-mass operational interpretation.  It records feasibility,
the source decision timing, actual positive-branch PBOs, and the source
candidate's response/closure semantics without changing a null branch into an
arbitrary numerical PBO. -/
def LG21ObservedAccessReportRequiredPBODefinition1Operational
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) : Prop :=
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  (∀ student,
    LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredConditionalTaking
      LG21AccessStatus.access
      (lg21ObservedAccessReportRequiredActualAction C student)) ∧
    LG21ObservedAccessReportRequiredSourceTimedWellFormed C ∧
      0 < (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | C.selected.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true} ∧
        LG21ObservedAccessReportRequiredActualBranchPBOs C ∧
          LG21ObservedAccessReportRequiredPositiveMassMemberResponses C ∧
            LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
              (lg21ContinuousGaussianAccessPopulationLaw M)
              (lg21ContinuousPopulationBase testFeature)
              (lg21ContinuousPopulationFeature testFeature)
              (lg21ContinuousPopulationSkill (Feature := Feature))
              ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
                ((lg21ContinuousPopulationFeature_measurable testFeature).prodMk
                  lg21ContinuousPopulationSkill_measurable))
              C.selected.testLaw
              (fun latentSkill publicBase =>
                C.selected.takeDecision latentSkill publicBase)

/-- Direct, inspectable repacking of the report-required source carrier into
the explicit operational Definition 1 contract. -/
theorem lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_satisfies_definition1PBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}} {testFeature : Feature}
    (C : LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate
      M haccess testFeature) :
    LG21ObservedAccessReportRequiredPBODefinition1Operational C := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  refine ⟨?_, ?_, C.active_take_positive, ?_, ?_, ?_⟩
  · intro student
    exact lg21ObservedAccessReportRequiredActualAction_feasible C student
  · exact lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_wellFormed C
  · exact lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_actualBranchPBOs C
  · exact lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_memberResponses C
  · exact C.source_timed.positive_mass_recalibrated_stable

/-! ## Section 4: observed access, mandatory given access -/

/-- The literal Definition 1 contract for the source's mandatory-given-access
policy.  There is no discretionary access-side student action to compare:
feasibility forces `Z = Y = X` pointwise.  The two PBO clauses are therefore
the access all-report conditional mean and the no-access base-only conditional
mean, each on its own positive source population. -/
def LG21ObservedAccessMandatoryPBODefinition1
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ)
    (noAccessOutput : Bool × (ℝ × (Feature → ℝ)) → ℝ) : Prop :=
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianAccessPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) :=
    lg21ContinuousGaussianNoAccessPopulationLaw_isProbability M hnoAccess
  letI : IsFiniteMeasure (lg21ContinuousGaussianNoAccessPopulationLaw M) := ⟨by simp⟩
  (∀ student,
    LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredGivenAccess
      (lg21ContinuousPopulationAccessStatus student) (mandatory.action student)) ∧
    (∀ student,
      mandatory.action student =
        if lg21ContinuousPopulationAccess student = true then
          LG21AccessAction.takeAndReport
        else LG21AccessAction.noTake) ∧
      (∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
        mandatory.action student = LG21AccessAction.takeAndReport) ∧
        LG21ObservedAccessAllReportPBO
          (lg21ContinuousGaussianAccessPopulationLaw M)
          (lg21ContinuousPopulationBase testFeature)
          (lg21ContinuousPopulationFeature testFeature)
          (lg21ContinuousPopulationSkill (Feature := Feature)) reportedPayoff ∧
          LG21ContinuousGaussianNoAccessPopulationPBO
            M hnoAccess testFeature noAccessOutput

/-- The mandatory source construction has no hidden behavioral comparison:
the policy's feasibility relation determines the full action profile. -/
theorem LG21ObservedAccessMandatoryPBODefinition1.forced_actions
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature}
    {haccess : 0 < M.accessLaw {true}}
    {hnoAccess : 0 < M.accessLaw {false}} {testFeature : Feature}
    {mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M}
    {reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ}
    {noAccessOutput : Bool × (ℝ × (Feature → ℝ)) → ℝ}
    (h : LG21ObservedAccessMandatoryPBODefinition1 M haccess hnoAccess
      testFeature mandatory reportedPayoff noAccessOutput) :
    ∀ student,
      mandatory.action student =
        if lg21ContinuousPopulationAccess student = true then
          LG21AccessAction.takeAndReport
        else LG21AccessAction.noTake := by
  rcases h with ⟨_, hforced, _, _, _⟩
  exact hforced

/-- A direct source witness for the mandatory Definition 1 contract.  The
PBO equations are constructed from the literal Gaussian conditional laws;
there is no `estimationConsistent` field or caller-supplied PBO premise. -/
theorem lg21ContinuousGaussianPopulation_exists_mandatoryDefinition1PBO
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature) :
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
      (reportedPayoff : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ)
      (noAccessOutput : Bool × (ℝ × (Feature → ℝ)) → ℝ),
      LG21ObservedAccessMandatoryPBODefinition1 M haccess hnoAccess
        testFeature mandatory reportedPayoff noAccessOutput := by
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
      (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → ℝ :=
    lg21ContinuousObservedAccessUnselectedPBO M haccess testFeature
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
  refine ⟨mandatory, reportedPayoff, noAccessOutput, ?_⟩
  refine ⟨mandatory.feasible, ?_, ?_, hreportedPBO, hnoAccessPBO⟩
  · exact lg21MandatoryGivenAccess_feasibleAction_forces_action
      mandatory.action mandatory.feasible
  · exact lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible

/-! The contracts deliberately remain separate.  Hiding access changes
the public sigma-algebra, while observing access changes it to the
access-conditioned source law.  A caller must select the appropriate contract
rather than treating a generic `consistency : Prop` as a proof for both. -/

end

end LG21TestOptionalPolicies
