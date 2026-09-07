import LG21TestOptionalPolicies.ReportRequiredFullPublicActionBridge
import LG21TestOptionalPolicies.PositiveMassPBORefinement
import LG21TestOptionalPolicies.SequentialEquilibrium
import LG21TestOptionalPolicies.SelectedPopulationConditionalSupport

/-!
# Full-public positive-mass semantics for report-required LG21 testing

This module is the global, source-facing behavioral boundary for the
report-required part of Lemma 4.1.  A taking action is an exact measurable
subset of the actual `(public base, latent skill)` population.  The school
sees the full public base and a score on the report branch, and only the full
public base on the no-report branch.

Two distinctions are deliberate:

* Definition 1 gives a pointwise binary best-response comparison at a fixed
  public base.  With a strictly increasing taking payoff, it makes the exact
  no-take action set downward closed in skill at that same base.  It does not
  posit a cutoff or a positive-mass fibre.
* The selected full-public posterior bridge calibrates the report PBO only
  almost everywhere on the actual reporter law.  Turning that fact and the
  no-report PBO into a global strict gain for actual no-takers is a separate
  source-population/absolute-continuity obligation.  It is exposed below as
  `hstrictGain`, rather than silently replacing it by a pointwise posterior
  value on an unreached score or a hidden skill cohort.

The final theorem is intentionally useful as a closeout target: once the
literal Gaussian source proves the displayed global strict-gain statement,
Definition 1 rules out a positive-mass no-take event with no fixed-base or
per-score positivity premise.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-! ## Exact full-public action events -/

/--
The report-required taking set as a subset of full latent public states.  Its
coordinates are ordered `(base, skill)`, matching the school-visible base and
the student's latent decision input.
-/
def lg21ReportRequiredFullPublicTakeSet
    {Base : Type*} (take : Base → ℝ → Bool) : Set (Base × ℝ) :=
  {profileSkill | take profileSkill.1 profileSkill.2 = true}

/-- The complementary exact no-take action set. -/
def lg21ReportRequiredFullPublicNoTakeSet
    {Base : Type*} (take : Base → ℝ → Bool) : Set (Base × ℝ) :=
  {profileSkill | take profileSkill.1 profileSkill.2 = false}

/-- Measurability of the full-public taking event. -/
theorem lg21ReportRequiredFullPublicTakeSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    MeasurableSet (lg21ReportRequiredFullPublicTakeSet take) := by
  change MeasurableSet
    ((fun profileSkill : Base × ℝ => take profileSkill.1 profileSkill.2) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage htake

/-- Measurability of the full-public no-take event. -/
theorem lg21ReportRequiredFullPublicNoTakeSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (take : Base → ℝ → Bool)
    (htake : Measurable (fun profileSkill : Base × ℝ =>
      take profileSkill.1 profileSkill.2)) :
    MeasurableSet (lg21ReportRequiredFullPublicNoTakeSet take) := by
  change MeasurableSet
    ((fun profileSkill : Base × ℝ => take profileSkill.1 profileSkill.2) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage htake

/--
The actual source-population reporter event is the preimage of the full
public taking set.  It is an event determined by the literal action rule, not
a separately named latent cohort.
-/
theorem lg21_reportRequired_actualReporter_eq_fullPublicTakeSet_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (skill : Omega → ℝ)
    (take : Base → ℝ → Bool) :
    {omega | take (base omega) (skill omega) = true} =
      (fun omega => (base omega, skill omega)) ⁻¹'
        lg21ReportRequiredFullPublicTakeSet take := by
  rfl

/-- The analogous exact source-population no-take event. -/
theorem lg21_reportRequired_actualNoTake_eq_fullPublicNoTakeSet_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (skill : Omega → ℝ)
    (take : Base → ℝ → Bool) :
    {omega | take (base omega) (skill omega) = false} =
      (fun omega => (base omega, skill omega)) ⁻¹'
        lg21ReportRequiredFullPublicNoTakeSet take := by
  rfl

/-! ## Definition-1 action closure, without a cutoff premise -/

/--
For a source report-required equilibrium whose ex-ante taking payoff is
strictly increasing in latent skill, the exact taking set is upward closed in
the skill coordinate at each *same* public base.  This is the formal version
of the fact that a high-skill no-taker cannot coexist with a lower-skill taker
under the candidate's own PBOs.
-/
theorem lg21_reportRequired_fullPublic_takeSet_upperClosed_of_sourceBestResponse
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (hstrict : ∀ base, StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)) :
    ∀ ⦃low high : Base × ℝ⦄,
      low.1 = high.1 → low.2 ≤ high.2 →
        low ∈ lg21ReportRequiredFullPublicTakeSet
          (fun base skill => E.takeDecision skill base) →
        high ∈ lg21ReportRequiredFullPublicTakeSet
          (fun base skill => E.takeDecision skill base) := by
  intro low high hbase hskill hlow
  rcases low with ⟨lowBase, lowSkill⟩
  rcases high with ⟨highBase, highSkill⟩
  change lowBase = highBase at hbase
  change lowSkill ≤ highSkill at hskill
  change E.takeDecision lowSkill lowBase = true at hlow
  subst highBase
  change E.takeDecision highSkill lowBase = true
  exact bool_choice_upperClosed_of_noProfitableBinaryChoiceDeviation_strictMono
    (E.takeDecision · lowBase)
    (lg21ReportRequiredSequentialEquilibrium_take_bestResponse hEq lowBase)
    (hstrict lowBase) hskill hlow

/--
The exact no-take action set is downward closed in skill at a common public
base.  This is the source-facing closure behind the high-band observation:
if a high latent skill is assigned no-take, every lower skill with the same
public base must also be assigned no-take.  No measure, fibre positivity, or
named cohort is introduced.
-/
theorem lg21_reportRequired_fullPublic_noTakeSet_downwardClosed_of_sourceBestResponse
    {Base Test : Type*} [MeasurableSpace Test]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test}
    (hEq : lg21ReportRequiredSequentialEquilibrium E)
    (hstrict : ∀ base, StrictMono
      (fun skill => lg21ReportRequiredSequentialTakeExpectedPayoff E skill base)) :
    ∀ ⦃low high : Base × ℝ⦄,
      low.1 = high.1 → low.2 ≤ high.2 →
        high ∈ lg21ReportRequiredFullPublicNoTakeSet
          (fun base skill => E.takeDecision skill base) →
        low ∈ lg21ReportRequiredFullPublicNoTakeSet
          (fun base skill => E.takeDecision skill base) := by
  intro low high hbase hskill hhigh
  by_contra hnot
  have hlowTake : low ∈ lg21ReportRequiredFullPublicTakeSet
      (fun base skill => E.takeDecision skill base) := by
    change E.takeDecision low.2 low.1 = true
    simpa [lg21ReportRequiredFullPublicNoTakeSet] using hnot
  have hhighTake : high ∈ lg21ReportRequiredFullPublicTakeSet
      (fun base skill => E.takeDecision skill base) :=
    lg21_reportRequired_fullPublic_takeSet_upperClosed_of_sourceBestResponse
      hEq hstrict hbase hskill hlowTake
  change E.takeDecision high.2 high.1 = false at hhigh
  change E.takeDecision high.2 high.1 = true at hhighTake
  simp [hhigh] at hhighTake

/-! ## Global selected-action PBO and positive-mass closure -/

/--
An explicit source-facing identification of the reported payoff with the
literal conditional expectation on the actual positive reporter event.  The
source's `estimationConsistent` field is abstract, so this equality is kept as
an auditable proof obligation rather than inferred from a proposition whose
contents are not inspectable.
-/
def LG21FullPublicReportRequiredReportedPBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (rawLaw : Measure Omega) (base : Omega → Base) (score skill : Omega → ℝ)
    (take : Base → ℝ → Bool) (reportedPayoff : Base → ℝ → ℝ) : Prop :=
  let reporterLaw := lg21NormalizedRestriction rawLaw
    {omega | take (base omega) (skill omega) = true}
  (fun omega => reportedPayoff (base omega) (score omega)) =ᵐ[reporterLaw]
    reporterLaw[skill |
      MeasurableSpace.comap (fun omega => (base omega, score omega)) inferInstance]

/--
The corresponding literal PBO condition on the no-take/no-report branch.  At
that information set the school observes the complete public base but no test
score.  The equality is meaningful only under a positive actual no-take
branch, which is enforced by the carrier below.
-/
def LG21FullPublicReportRequiredNoTakePBO
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (rawLaw : Measure Omega) (base : Omega → Base) (skill : Omega → ℝ)
    (take : Base → ℝ → Bool) (noTakePayoff : Base → ℝ) : Prop :=
  let noTakeLaw := lg21NormalizedRestriction rawLaw
    {omega | take (base omega) (skill omega) = false}
  (fun omega => noTakePayoff (base omega)) =ᵐ[noTakeLaw]
    noTakeLaw[skill | MeasurableSpace.comap base inferInstance]

/--
An inspectable source-facing report-required equilibrium carrier.  It replaces
the opaque `estimationConsistent : Prop` field of the generic sequential
carrier by the two conditional-expectation identities that the paper's PBO
definition actually requires after the school applies the known action rule.

The positive-mass guards are essential: a regular conditional distribution
does not give a source-determined finite PBO value on an action branch that no
student reaches.  This carrier does not assert a cutoff, a per-score
positivity fact, a hidden cohort, or a whole-candidate-equilibrium condition.
-/
structure LG21FullPublicReportRequiredSourceEquilibrium
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ) : Prop where
  /-- The direct pre-score taking best response from Definition 1.  The
  source-facing carrier keeps this behavioral obligation separate from the
  conditional-mean PBO fields below, rather than relying on an opaque
  consistency proposition. -/
  take_best_response : ∀ publicBase,
    NoProfitableBinaryChoiceDeviation
      (fun latentSkill ↦ E.takeDecision latentSkill publicBase = true)
      (fun latentSkill ↦
        lg21ReportRequiredSequentialTakeExpectedPayoff E latentSkill publicBase)
      (fun _latentSkill ↦ E.noReportPayoff publicBase)
  base_measurable : Measurable base
  score_measurable : Measurable score
  skill_measurable : Measurable skill
  action_measurable : Measurable (fun profileSkill : Base × ℝ =>
    E.takeDecision profileSkill.2 profileSkill.1)
  reportedPayoff_measurable : Measurable (fun publicScore : Base × ℝ =>
    E.reportedPayoff publicScore.1 publicScore.2)
  noReportPayoff_measurable : Measurable E.noReportPayoff
  reported_integrable : ∀ hpositive :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true},
    Integrable skill (lg21NormalizedRestriction rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true})
  reported_pbo : ∀ hpositive :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true},
    LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.reportedPayoff
  noTake_integrable : ∀ hpositive :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = false},
    Integrable skill (lg21NormalizedRestriction rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false})
  noTake_pbo : ∀ hpositive :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = false},
    LG21FullPublicReportRequiredNoTakePBO rawLaw base skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.noReportPayoff

/--
The source carrier exposes no-take PBO consistency only at a positive actual
branch.  This is a projection lemma so downstream proofs cannot accidentally
obtain an off-path no-take payoff by unfolding a generic consistency name.
-/
theorem LG21FullPublicReportRequiredSourceEquilibrium.noTake_pbo_if_positive
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E)
    (hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = false}) :
    LG21FullPublicReportRequiredNoTakePBO rawLaw base skill
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
      E.noReportPayoff :=
  S.noTake_pbo hpositive

/-- The carrier's literal full-public taking set is measurable. -/
theorem LG21FullPublicReportRequiredSourceEquilibrium.takeSet_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E) :
    MeasurableSet (lg21ReportRequiredFullPublicTakeSet
      (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)) :=
  lg21ReportRequiredFullPublicTakeSet_measurable
    (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    S.action_measurable

/-- The carrier's actual reporter event is a measurable source-population event. -/
theorem LG21FullPublicReportRequiredSourceEquilibrium.actualReporterEvent_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E) :
    MeasurableSet {omega | E.takeDecision (skill omega) (base omega) = true} := by
  change MeasurableSet
    ((fun omega => E.takeDecision (skill omega) (base omega)) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (S.action_measurable.comp (S.base_measurable.prodMk S.skill_measurable))

/-- The carrier's actual no-take event is likewise measurable. -/
theorem LG21FullPublicReportRequiredSourceEquilibrium.actualNoTakeEvent_measurable
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E) :
    MeasurableSet {omega | E.takeDecision (skill omega) (base omega) = false} := by
  change MeasurableSet
    ((fun omega => E.takeDecision (skill omega) (base omega)) ⁻¹' ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (S.action_measurable.comp (S.base_measurable.prodMk S.skill_measurable))

/--
The literal full-public selected-action bridge converts a source PBO
identification into the canonical selected-posterior mean.  Its scope is
exactly the actual reporter law.  In particular, it does not choose a value
for a score reached only by a hypothetical no-taker.
-/
theorem lg21_fullPublic_reportRequired_reportedPBO_eq_canonicalSelectedMean_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (take : Base → ℝ → Bool) (reportedPayoff : Base → ℝ → ℝ)
    (hpositive : 0 < rawLaw {omega | take (base omega) (skill omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent take)).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (hintegrable : Integrable skill
      (lg21NormalizedRestriction rawLaw
        {omega | take (base omega) (skill omega) = true}))
    (hreportedPBO : LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      take reportedPayoff) :
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {omega | take (base omega) (skill omega) = true}
    (fun omega => reportedPayoff (base omega) (score omega)) =ᵐ[reporterLaw]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega) := by
  intro reporterLaw
  have hbridge :=
    lg21_reportRequired_fullPublicAction_condExp_eq_signalPosteriorMean_ae
      rawLaw base score skill hbase hscore hskill signal selectedLatentLaw take
      (fun omega => take (base omega) (skill omega)) (fun _ => rfl) hpositive
      hselectedJoint hintegrable
  have hsourcePBO :
      (fun omega => reportedPayoff (base omega) (score omega)) =ᵐ[reporterLaw]
        reporterLaw[skill |
          MeasurableSpace.comap (fun omega => (base omega, score omega)) inferInstance] := by
    simpa [LG21FullPublicReportRequiredReportedPBO] using hreportedPBO
  filter_upwards [hsourcePBO, hbridge] with omega hsource hcanonical
  exact hsource.trans hcanonical

/--
The literal selected-action bridge applied to the inspectable source carrier.
The source carrier supplies the actual reported PBO condition; the separate
selected-joint argument supplies the population calculation.  Neither is
recovered from an opaque consistency field.
-/
theorem LG21FullPublicReportRequiredSourceEquilibrium.reported_pbo_eq_canonical_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (hpositive : 0 < rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase))).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw)) :
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {omega | E.takeDecision (skill omega) (base omega) = true}
    (fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[reporterLaw]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega) := by
  exact lg21_fullPublic_reportRequired_reportedPBO_eq_canonicalSelectedMean_ae
    rawLaw base score skill hbase hscore hskill signal selectedLatentLaw
    (fun publicBase latentSkill => E.takeDecision latentSkill publicBase)
    E.reportedPayoff hpositive hselectedJoint (S.reported_integrable hpositive)
    (S.reported_pbo hpositive)

/--
The explicit per-test-law comparison that discharges the global strict-gain
obligation.  This has the right source timing: a student decides before a
score is drawn, so the strict comparison is integrated against that student's
actual test law.  The premise is almost everywhere under each such law, not a
per-score selected-mass requirement.
-/
theorem lg21_reportRequired_strictGain_of_reportedPayoffAboveNoTake_ae
    {Base Test : Type*} [MeasurableSpace Test]
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base Test)
    (habove : ∀ skill base, ∀ᵐ test ∂E.testLaw skill base,
      E.noReportPayoff base < E.reportedPayoff base test) :
    ∀ skill base,
      E.noReportPayoff base <
        lg21ReportRequiredSequentialTakeExpectedPayoff E skill base := by
  intro skill base
  letI : IsProbabilityMeasure (E.testLaw skill base) :=
    E.testLaw_isProbability skill base
  have hstrict := lg21_integral_lt_integral_of_ae_lt_probability
    (E.testLaw skill base)
    (integrable_const (E.noReportPayoff base))
    (E.reportedPayoff_integrable skill base)
    (habove skill base)
  simpa [lg21ReportRequiredSequentialTakeExpectedPayoff] using hstrict

/--
Global report-required positive-mass closure.  This theorem uses the actual
source sequential equilibrium and the exact full-public action event.  The
strict-gain premise is deliberately global and almost everywhere under the
source population: establishing it is where the literal Gaussian law must
transport the selected reporter PBO and the no-report PBO across public-base
fibres.  It cannot be replaced by a fixed-base assumption or a per-score
selection-positivity assertion.

The first conjunct records the selected-action PBO consequence for the actual
reporter population; the second is the desired no-positive-mass no-take
conclusion.
-/
theorem lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_globalStrictGain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (hbest : ∀ publicBase,
      NoProfitableBinaryChoiceDeviation
        (fun latentSkill ↦ E.takeDecision latentSkill publicBase = true)
        (fun latentSkill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E latentSkill publicBase)
        (fun _latentSkill ↦ E.noReportPayoff publicBase))
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (hpositiveReporter :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent
            (fun base skill => E.takeDecision skill base))).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (hintegrable : Integrable skill
      (lg21NormalizedRestriction rawLaw
        {omega | E.takeDecision (skill omega) (base omega) = true}))
    (hreportedPBO : LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      (fun base skill => E.takeDecision skill base) E.reportedPayoff)
    (hstrictGain : ∀ᵐ omega ∂rawLaw,
      E.takeDecision (skill omega) (base omega) = false →
        E.noReportPayoff (base omega) <
          lg21ReportRequiredSequentialTakeExpectedPayoff E
            (skill omega) (base omega)) :
    ((fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
        lg21NormalizedRestriction rawLaw
          {omega | E.takeDecision (skill omega) (base omega) = true}]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega)) ∧
      rawLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  constructor
  · exact lg21_fullPublic_reportRequired_reportedPBO_eq_canonicalSelectedMean_ae
      rawLaw base score skill hbase hscore hskill signal selectedLatentLaw
      (fun base skill => E.takeDecision skill base) E.reportedPayoff
      hpositiveReporter hselectedJoint hintegrable hreportedPBO
  · have himpossible : ∀ᵐ omega ∂rawLaw,
        E.takeDecision (skill omega) (base omega) ≠ false := by
      filter_upwards [hstrictGain] with omega hgain hnoTake
      have hnoTakeBest :=
        (hbest (base omega)).2 (skill omega) (by simp [hnoTake])
      exact (not_le_of_gt (hgain hnoTake)) hnoTakeBest
    have hzero := ae_iff.mp himpossible
    simpa only [Set.mem_setOf_eq, not_not] using hzero

/--
Convenient source-facing form of the global closure theorem.  Its only
behavioral/PBO separation premise says that the candidate's reported estimate
strictly exceeds its no-report estimate almost everywhere under every actual
test law.  The preceding theorem turns this into the needed ex-ante gain;
the full-public PBO conclusion remains tied to the literal selected action
event.
-/
theorem lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_reportedPayoffAboveNoTake
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (hbest : ∀ publicBase,
      NoProfitableBinaryChoiceDeviation
        (fun latentSkill ↦ E.takeDecision latentSkill publicBase = true)
        (fun latentSkill ↦
          lg21ReportRequiredSequentialTakeExpectedPayoff E latentSkill publicBase)
        (fun _latentSkill ↦ E.noReportPayoff publicBase))
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (hpositiveReporter :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent
            (fun base skill => E.takeDecision skill base))).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (hintegrable : Integrable skill
      (lg21NormalizedRestriction rawLaw
        {omega | E.takeDecision (skill omega) (base omega) = true}))
    (hreportedPBO : LG21FullPublicReportRequiredReportedPBO rawLaw base score skill
      (fun base skill => E.takeDecision skill base) E.reportedPayoff)
    (habove : ∀ latentSkill publicBase,
      ∀ᵐ realizedScore ∂E.testLaw latentSkill publicBase,
        E.noReportPayoff publicBase < E.reportedPayoff publicBase realizedScore) :
    ((fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
        lg21NormalizedRestriction rawLaw
          {omega | E.takeDecision (skill omega) (base omega) = true}]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega)) ∧
      rawLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  apply lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_globalStrictGain
    hbest rawLaw base score skill hbase hscore hskill signal selectedLatentLaw
    hpositiveReporter hselectedJoint hintegrable hreportedPBO
  filter_upwards [] with omega
  intro hnoTake
  exact lg21_reportRequired_strictGain_of_reportedPayoffAboveNoTake_ae E habove
    (skill omega) (base omega)

/--
Source-carrier form of the full-public closure theorem.  This is the direct
formal counterpart of the paper's Definition 1 plus its PBO definition: the
only remaining behavioral input is the explicitly stated global strict-gain
lemma.  In particular, no theorem may obtain this result by treating
`estimationConsistent : Prop` as though it contained the PBO equations.
-/
theorem LG21FullPublicReportRequiredSourceEquilibrium.noPositiveMassNoTake_of_globalStrictGain
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (hpositiveReporter :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase))).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (hstrictGain : ∀ᵐ omega ∂rawLaw,
      E.takeDecision (skill omega) (base omega) = false →
        E.noReportPayoff (base omega) <
          lg21ReportRequiredSequentialTakeExpectedPayoff E
            (skill omega) (base omega)) :
    ((fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
        lg21NormalizedRestriction rawLaw
          {omega | E.takeDecision (skill omega) (base omega) = true}]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega)) ∧
      rawLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  exact lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_globalStrictGain
    S.take_best_response rawLaw base score skill hbase hscore hskill signal selectedLatentLaw
    hpositiveReporter hselectedJoint (S.reported_integrable hpositiveReporter)
    (S.reported_pbo hpositiveReporter) hstrictGain

/--
Preferred source-carrier closeout target.  The PBO identities and Definition 1
best response come from the explicit carrier, while the remaining substantive
Gaussian inequality is stated at the proper pre-score timing as an a.e.
comparison under each actual test law.
-/
theorem LG21FullPublicReportRequiredSourceEquilibrium.noPositiveMassNoTake_of_reportedPayoffAboveNoTake
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    {rawLaw : Measure Omega} [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    {base : Omega → Base} {score skill : Omega → ℝ}
    {E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ}
    (S : LG21FullPublicReportRequiredSourceEquilibrium rawLaw base score skill E)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (hpositiveReporter :
      0 < rawLaw {omega | E.takeDecision (skill omega) (base omega) = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent
            (fun publicBase latentSkill => E.takeDecision latentSkill publicBase))).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (habove : ∀ latentSkill publicBase,
      ∀ᵐ realizedScore ∂E.testLaw latentSkill publicBase,
        E.noReportPayoff publicBase < E.reportedPayoff publicBase realizedScore) :
    ((fun omega => E.reportedPayoff (base omega) (score omega)) =ᵐ[
        lg21NormalizedRestriction rawLaw
          {omega | E.takeDecision (skill omega) (base omega) = true}]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega)) ∧
      rawLaw {omega | E.takeDecision (skill omega) (base omega) = false} = 0 := by
  exact lg21_reportRequired_fullPublic_noPositiveMassNoTake_of_reportedPayoffAboveNoTake
    S.take_best_response rawLaw base score skill hbase hscore hskill signal selectedLatentLaw
    hpositiveReporter hselectedJoint (S.reported_integrable hpositiveReporter)
    (S.reported_pbo hpositiveReporter) habove

end

end LG21TestOptionalPolicies
