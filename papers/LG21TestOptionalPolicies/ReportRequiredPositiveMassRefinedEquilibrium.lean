import LG21TestOptionalPolicies.ReportRequiredFullPublicPositiveMassUnraveling
import LG21TestOptionalPolicies.ReportRequiredLocalGaussianCandidate

/-!
# Positive-mass refined report-required equilibrium carrier for LG21

This module gives the source-facing equilibrium carrier for the
report-required protocol under the approved positive-mass refinement.  It is
separate from the legacy sequential carrier because a pointwise comparison to
an unattained no-take history would assign a numerical PBO where the source
model does not determine one.

The carrier therefore has three explicit parts:

* the actual pre-score taking action and the two public observations;
* conditional-mean PBO identities only when the corresponding actual action
  branch has positive mass; and
* stability against the literal positive-mass local candidates whose PBOs are
  recalibrated from their own action populations.

It intentionally contains neither `lg21ReportRequiredSequentialEquilibrium`
nor a pointwise `NoProfitableBinaryChoiceDeviation` field.  In particular, it
does not manufacture a PBO at a null history, and it makes no claim that a
canonical candidate or equilibrium witness exists.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/--
An inspectable source equilibrium for report-required testing under
positive-mass recalibrated stability.

`E` supplies only the source-timed action and payoff functions plus the test
law.  Its legacy `estimationConsistent` field is not used here.  The two PBO
fields below are the actual conditional-expectation obligations, each guarded
by positivity of the branch on which it is meaningful.  The stability field
rules out exactly the literal local candidates whose own positive branches
carry recalibrated PBOs.
-/
structure LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (testNoiseVariance : NNReal) : Prop where
  /-- The public base observed on both action branches is measurable. -/
  base_measurable : Measurable base
  /-- The realized score observed only after taking is measurable. -/
  score_measurable : Measurable score
  /-- Latent skill is measurable under the source population. -/
  skill_measurable : Measurable skill
  /-- Taking is decided before the score and depends only on `(base, skill)`. -/
  action_measurable : Measurable (fun profileSkill : Base × ℝ =>
    E.takeDecision profileSkill.2 profileSkill.1)
  reportedPayoff_measurable : Measurable (fun publicScore : Base × ℝ =>
    E.reportedPayoff publicScore.1 publicScore.2)
  noReportPayoff_measurable : Measurable E.noReportPayoff
  /-- The pre-score evaluation law is the literal source Gaussian score law.
  This prevents a selected report-required profile from evaluating taking under
  a score distribution different from the source model's `skill + noise`. -/
  test_law_gaussian : ∀ publicBase latentSkill,
    E.testLaw latentSkill publicBase =
      gaussianReal latentSkill testNoiseVariance
  /-- Integrability on the actual taking/reporting branch, only if it is
  reached with positive source mass. -/
  reported_integrable : ∀ hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true},
    Integrable skill (lg21NormalizedRestriction rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true})
  /-- The reported output is the actual conditional mean on the positive
  taking/reporting branch. -/
  reported_pbo : ∀ hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true},
    LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.reportedPayoff
  /-- Integrability on the actual no-take branch, only if it is reached with
  positive source mass. -/
  noTake_integrable : ∀ hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false},
    Integrable skill (lg21NormalizedRestriction rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false})
  /-- The no-take output is the actual conditional mean on the positive
  no-take branch. -/
  noTake_pbo : ∀ hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false},
    LG21FullPublicReportRequiredNoTakePBO rawLaw base skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.noReportPayoff
  /-- No literal positive-mass local candidate can enter a current
  zero-taker region after both of its action branches are recalibrated from
  the candidate's own selected population. -/
  positive_mass_recalibrated_stable :
    LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
      rawLaw base score skill
      (base_measurable.prodMk (score_measurable.prodMk skill_measurable))
      E.testLaw
      (fun latentSkill publicBase => E.takeDecision latentSkill publicBase)

namespace LG21ReportRequiredPositiveMassRefinedSourceEquilibrium

/-- The actual taking event is measurable from the source action rule. -/
theorem actual_take_event_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance) :
    MeasurableSet {omega | E.takeDecision (skill omega) (base omega) = true} := by
  change MeasurableSet
    ((fun omega => E.takeDecision (skill omega) (base omega)) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (S.action_measurable.comp (S.base_measurable.prodMk S.skill_measurable))

/-- The actual no-take event is measurable from the source action rule. -/
theorem actual_noTake_event_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance) :
    MeasurableSet {omega | E.takeDecision (skill omega) (base omega) = false} := by
  change MeasurableSet
    ((fun omega => E.takeDecision (skill omega) (base omega)) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (S.action_measurable.comp (S.base_measurable.prodMk S.skill_measurable))

/-- Project the actual reported-branch PBO only after its positivity premise
has been supplied. -/
theorem reported_pbo_if_positive
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance)
    (hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}) :
    LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.reportedPayoff :=
  S.reported_pbo hpositive

/-- Project the actual no-take PBO only after its positivity premise has been
supplied.  No theorem in this interface exposes a value for a null no-take
branch. -/
theorem noTake_pbo_if_positive
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance)
    (hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}) :
    LG21FullPublicReportRequiredNoTakePBO rawLaw base skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.noReportPayoff :=
  S.noTake_pbo hpositive

/-- Project the source's positive-mass recalibrated stability condition. -/
theorem stable_against_positive_mass_local_recalibrated_entry
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega -> Base} {score skill : Omega -> ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    {testNoiseVariance : NNReal}
    (S : LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
      rawLaw base score skill E testNoiseVariance) :
    LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntryForTestLaw
      rawLaw base score skill
      (S.base_measurable.prodMk (S.score_measurable.prodMk S.skill_measurable))
      E.testLaw
      (fun latentSkill publicBase => E.takeDecision latentSkill publicBase) :=
  S.positive_mass_recalibrated_stable

end LG21ReportRequiredPositiveMassRefinedSourceEquilibrium

end

end LG21TestOptionalPolicies
