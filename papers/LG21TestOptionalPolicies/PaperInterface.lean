import LG21TestOptionalPolicies.ContinuousPopulation
import LG21TestOptionalPolicies.Assumptions
import LG21TestOptionalPolicies.Definition1LiteralPBOContract
import LG21TestOptionalPolicies.ClarifiedTheorem32Model
import LG21TestOptionalPolicies.Theorem32GaussianCounterexample
import LG21TestOptionalPolicies.HiddenAccessTheorem31OptionalSourceCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralOutputLawBridge
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredSourceCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredFairnessCloseout
import LG21TestOptionalPolicies.ObservedAccessLemma41LiteralSourceCloseout
import LG21TestOptionalPolicies.ObservedAccessOptionalSection4Bridge
import LG21TestOptionalPolicies.Proposition42ActiveBranchSourceBridge
import LG21TestOptionalPolicies.Proposition42ReportRequiredActiveBranchSourceBridge
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition42Bridge
import LG21TestOptionalPolicies.MandatoryObservedAccessSection4PolicyEndpoints
import LG21TestOptionalPolicies.ObservedAccessAllProtocolD6OutputBridge
import LG21TestOptionalPolicies.MandatoryGivenAccessSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessAllProtocolProposition43Bridge
import LG21TestOptionalPolicies.ObservedAccessAllProtocolTheorem44Fairness
import LG21TestOptionalPolicies.ObservedAccessProposition43PolicyEndpoints
import LG21TestOptionalPolicies.ObservedAccessPolicyTheorem44Endpoints
import LG21TestOptionalPolicies.MandatoryObservedAccessProposition43Nonvacuity
import LG21TestOptionalPolicies.MandatoryObservedAccessTheorem44FairnessBridge
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchCloseout
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchModels
import LG21TestOptionalPolicies.ObservedAccessOptionalActiveBranchSection4Bridge
import LG21TestOptionalPolicies.ObservedAccessReportRequiredActiveBranchSection4
import LG21TestOptionalPolicies.SourceExactSemanticLayer

/-!
# Paper Interface: LG21 Test-Optional Policies

This is the review surface for *Test-optional Policies: Overcoming Strategic
Behavior and Informational Gaps*. It states source-facing results in paper
order and keeps proof plumbing in implementation modules.

The source's literal arbitrary-randomized-policy version of Theorem 3.2 is
false. The approved clarified theorem below makes reported-score output
deterministic while retaining an arbitrary no-report law. The voluntary
Section 4 exposes declared source-timed, positive-mass self-enforcing
candidates and a fibrewise active-branch selection for the two voluntary
protocols. This makes the source's operational unraveling reading visible,
rather than claiming it follows from a literal static-RCD definition.
Legacy conditional Gaussian endpoints remain diagnostics. A null action fibre
is never assigned a fabricated payoff.

-/

namespace LG21TestOptionalPolicies

noncomputable section

open AppliedModelingLib
open AppliedModelingLib.Probability
open MeasureTheory
open ProbabilityTheory

namespace PaperInterface

/-! ## Source model and definitions -/

/-- The unit-mass continuous Gaussian student model with independent access. -/
abbrev student_gaussian_signal_model := @paper_student_gaussian_signal_model

/-- The source action constraints and access-independence model. -/
abbrev access_action_constraints_and_access_independence :=
  @paper_access_action_constraints_and_access_independence

/--
Definition 1 for the hidden-access optional protocol.  This is an explicit
source-timed contract: feasible actions, both decision-stage responses, and
the actual public/no-report PBO equations are all part of the proposition.
The no-report equality is guarded by its attained positive-mass event.
-/
abbrev definition1_hidden_access_optional_pbo_contract :=
  @LG21HiddenAccessOptionalPBODefinition1AE


/--
Definition 1 for observed-access optional reporting under the documented
positive-mass operational reading.  It makes the source's `Z = 1, X = 0`
conditional-mean PBO explicit, conditions every unattained-branch statement
on positive mass, and keeps the two student decision times distinct.
-/
abbrev definition1_observed_access_optional_operational_pbo_contract :=
  @LG21ObservedAccessOptionalPBODefinition1Operational


/--
Definition 1 for observed-access reporting-required-after-taking under the
documented positive-mass operational reading. Taking remains a pre-score
choice; actual report and no-take conditional means are each guarded by their
own attained population.
-/
abbrev definition1_observed_access_report_required_operational_pbo_contract :=
  @LG21ObservedAccessReportRequiredPBODefinition1Operational

/--
The source-timed report-required candidate realizes feasibility, guarded
actual PBOs, and a.e. pre-score response/closure obligations without reading a
legacy opaque consistency field.
-/
abbrev definition1_observed_access_report_required_operational_source_timed :=
  @lg21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate_satisfies_definition1PBO

/--
Definition 1 for reporting required given observed access. Feasibility fixes
the only access-side action, while the explicit contract records the actual
all-report and no-access PBO equations.
-/
abbrev definition1_observed_access_mandatory_pbo_contract :=
  @LG21ObservedAccessMandatoryPBODefinition1

/--
The source Gaussian model constructs a mandatory-given-access Definition 1
PBO witness directly. The result supplies no hidden PBO assumption and no
discretionary access-side best-response placeholder.
-/
abbrev definition1_observed_access_mandatory_pbo_source_witness :=
  @lg21ContinuousGaussianPopulation_exists_mandatoryDefinition1PBO

/-- The optional protocol's source-timed positive-mass candidate. Its PBO,
response, and outsider-closure obligations apply only to attained branches. -/
abbrev voluntary_optional_self_enforcing_candidate :=
  @LG21OptionalSourceTimedPositiveMassSelfEnforcingCandidate

/-- The report-required protocol's source-timed positive-mass candidate. -/
abbrev voluntary_report_required_self_enforcing_candidate :=
  @LG21ReportRequiredSourceTimedPositiveMassSelfEnforcingCandidate

/--
Declared operational selection for optional reporting in Section 4. This is
the branch-maximal preservation rule used by the voluntary closeout. It ranges
over source-timed self-enforcing positive-mass candidates; it is not a
restatement or consequence of literal static-RCD Definition 1.
-/
abbrev voluntary_optional_active_branch_selection :=
  @LG21OptionalFibrewiseActiveBranchSelection

/--
Declared operational selection for report-required-after-taking in Section 4.
The selected source-PBO record and candidate-side response/closure evidence
are part of the rule, so action selection cannot be detached from the
positive-branch conditional-mean semantics.
-/
abbrev voluntary_report_required_active_branch_selection :=
  @LG21ReportRequiredFibrewiseActiveBranchSelection

/-- Common continuous-Gaussian source parameters used by the selected
voluntary Section 4 routes. -/
abbrev observed_access_gaussian_source := @LG21ObservedAccessGaussianSource

/-- A selected optional profile with its explicit active-branch convention. -/
abbrev optional_active_branch_profile := @LG21OptionalActiveBranchProfile

/-- A selected report-required profile, its positive-branch PBO record, and
its explicit active-branch convention. -/
abbrev report_required_active_branch_profile := @LG21ReportRequiredActiveBranchProfile

/-- Definition 2: access/no-access estimate-law equality conditional on skill. -/
abbrev definition2_latent_skill_fair :=
  @lg21SourceLawLatentSkillFair

/-- Definition 3: access/no-access estimate-law equality conditional on observables. -/
abbrev definition3_observable_fair :=
  @lg21SourceLawObservablyFair

/-- Definition 4: demographic access/no-access estimate-law equality. -/
abbrev definition4_demographic_fair :=
  @lg21SourceLawDemographicallyFair

/-- Definition 5: equality of base-only and full-feature estimate laws. -/
abbrev definition5_test_blank :=
  @lg21SourceLawTestBlank

/-- Latent-skill fairness implies observable, then demographic, fairness. -/
abbrev fairness_implication_chain :=
  @paper_continuous_fairness_implication_chain_of_kernel_mixtures

/-! ## Theorem 3.1: hidden access and strategic withholding -/

/--
The optional-reporting branch of Theorem 3.1 in the source's pointwise
quantifier order.  Taking is evaluated before a nondegenerate Gaussian score,
reporting afterward, and the supplied actions are pointwise best responses to
the displayed estimates.  The conclusion is pointwise for every skill, base,
and score and includes positive Gaussian mass below the finite cutoff.
-/
def theorem3_1_optional_reporting_source_timedSpec : Prop :=
  ∀ {Base : Type*}
    (testLaw : ℝ -> Base -> Measure ℝ)
    (testLaw_isProbability :
      ∀ skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : ℝ -> Base -> Bool)
    (reportDecision : Base -> ℝ -> Bool)
    (reportedPayoff : Base -> ℝ -> ℝ)
    (noReportPayoff : Base -> ℝ)
    (continuationPayoff_integrable : ∀ skill base,
      Integrable
        (fun score => lg21OptionalSourceContinuationPayoff
          reportDecision reportedPayoff noReportPayoff base score)
        (testLaw skill base))
    (hbest : LG21OptionalPointwiseBestResponses testLaw takeDecision
      reportDecision reportedPayoff noReportPayoff)
    (scoreVariance : NNReal) (hvariance : scoreVariance ≠ 0)
    (htestLaw : ∀ skill base,
      testLaw skill base = gaussianReal skill scoreVariance)
    (intercept slope : Base -> ℝ)
    (hslope : ∀ base, 0 < slope base)
    (hreported : ∀ base score,
      reportedPayoff base score = intercept base + slope base * score)
    (htie : ∀ base score,
      reportedPayoff base score = noReportPayoff base ->
        reportDecision base score = true),
    (∀ skill base, takeDecision skill base = true) ∧
      ∀ base,
        ∃ cutoff : ℝ,
          (∀ score,
            reportDecision base score = true ↔ cutoff ≤ score) ∧
          ∀ skill,
            0 < testLaw skill base
              {score | reportDecision base score = false}


/-- The same literal optional source equilibrium fails latent-skill fairness. -/
abbrev theorem3_1_optional_reporting_not_latent_skill_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_latentSkillFairAt_of_literalSourceStability

/-- The same literal optional source equilibrium fails observable fairness. -/
abbrev theorem3_1_optional_reporting_not_observably_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_observablyFairAt_of_literalSourceStability

/-- The same literal optional source equilibrium fails demographic fairness. -/
abbrev theorem3_1_optional_reporting_not_demographically_fair :=
  @lg21HiddenAccessOptionalLiteralOutputLawSurface_not_demographicallyFairAt_of_literalSourceStability

/--
The report-required source equilibrium has positive access/no-take mass under
the literal Gaussian factorization. This is the paper's strategic withholding
population, not an off-path payoff convention.
-/
abbrev theorem3_1_report_required_positive_withholding :=
  @LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.optionalNoReport_positive_of_sourceGaussianFactor

/--
Under the source's positive-mass local-tail equilibrium stability, the
report-required taking action has a finite skill cutoff almost everywhere in
the literal base law.
-/
abbrev theorem3_1_report_required_finite_take_cutoff_ae :=
  @LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE.exists_finite_takeCutoff_ae_of_localTailStability

/--
The report-required branch of Theorem 3.1.  Its taking action is a pointwise
pre-score best response and the expected reported estimate is positive-slope
affine in skill.  The source's take-at-indifference convention yields the
finite cutoff iff for every base and skill, with positive Gaussian mass below
the cutoff.
-/
def theorem3_1_report_required_source_timedSpec : Prop :=
  ∀ {Base Test : Type*} [MeasurableSpace Test]
    (testLaw : ℝ -> Base -> Measure Test)
    (testLaw_isProbability :
      ∀ skill base, IsProbabilityMeasure (testLaw skill base))
    (takeDecision : ℝ -> Base -> Bool)
    (reportedPayoff : Base -> Test -> ℝ)
    (noReportPayoff : Base -> ℝ)
    (reportedPayoff_integrable : ∀ skill base,
      Integrable (reportedPayoff base) (testLaw skill base))
    (hbest : LG21ReportRequiredPointwiseBestResponse testLaw takeDecision
      reportedPayoff noReportPayoff)
    (intercept slope : Base -> ℝ)
    (hslope : ∀ base, 0 < slope base)
    (htakePayoff : ∀ skill base,
      lg21ReportRequiredSourceTakeExpectedPayoff testLaw reportedPayoff
          skill base =
        intercept base + slope base * skill)
    (htie : ∀ skill base,
      lg21ReportRequiredSourceTakeExpectedPayoff testLaw reportedPayoff
          skill base = noReportPayoff base ->
        takeDecision skill base = true)
    (skillMean : Base -> ℝ) (skillVariance : NNReal)
    (hskillVariance : skillVariance ≠ 0),
    ∀ base,
      ∃ cutoff : ℝ,
        (∀ skill,
          takeDecision skill base = true ↔ cutoff ≤ skill) ∧
        0 < gaussianReal (skillMean base) skillVariance
          {skill | takeDecision skill base = false}


/-- The forced-report literal actual-output surface fails Definition 2. -/
abbrev theorem3_1_report_required_not_latent_skill_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_latentSkillFairAt_of_sourceGaussianFactor

/-- The forced-report literal actual-output surface fails Definition 3. -/
abbrev theorem3_1_report_required_not_observably_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_observablyFairAt_of_sourceGaussianFactor

/-- The forced-report literal actual-output surface fails Definition 4. -/
abbrev theorem3_1_report_required_not_demographically_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_demographicallyFairAt_of_sourceGaussianFactor

/-- Combined actual-output-law closeout for the three source fairness notions. -/
abbrev theorem3_1_report_required_not_fair :=
  @lg21HiddenAccessReportRequiredLiteralOutputLawSurface_not_fair_of_sourceGaussianFactor

/-- Theorem 3.1's fairness conclusion on the actual public-output laws of
the two hidden-access strategic-withholding equilibria.  The quantified
equilibrium records determine the take/report decisions and the realized
access/no-access laws; the three failures are not asserted for a caller-made
Gaussian/point-law surface. -/
def theorem3_1_hidden_access_pbo_fails_all_fairness_definitionsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature) (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature → ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ)
    (hbaseMean : Measurable baseMean) (baseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
          (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianSignalJointKernel baseMean hbaseMean baseVariance
          (M.noiseVariance testFeature : ℝ))
    (optionalEquilibrium :
      LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hoptionalReportBest : optionalEquilibrium.OptionalReportBestResponseAE)
    (hoptionalStable :
      LG21HiddenAccessSourceStableAgainstLocalCandidateEntry
        optionalEquilibrium hnoAccess)
    (requiredEquilibrium :
      LG21HiddenAccessReportRequiredLiteralSourceEquilibriumAE M testFeature)
    (hrequiredStable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature)
      requiredEquilibrium.source.takeDecision),
    (¬ lg21HiddenAccessOptionalLatentSkillFairAt optionalEquilibrium ∧
      ¬ lg21HiddenAccessOptionalObservablyFairAt optionalEquilibrium
        baseMean hbaseMean baseVariance ∧
      ¬ lg21HiddenAccessOptionalDemographicallyFairAt optionalEquilibrium) ∧
    (¬ lg21HiddenAccessReportRequiredLatentSkillFair requiredEquilibrium ∧
      ¬ lg21HiddenAccessReportRequiredObservablyFairAt requiredEquilibrium
        baseMean hbaseMean baseVariance ∧
      ¬ lg21HiddenAccessReportRequiredDemographicallyFairAt
        requiredEquilibrium)



/-! ## Theorem 3.2: clarified deterministic-reporter theorem -/

/--
Archival diagnostic: arbitrary randomized output invalidates literal Theorem
3.2. It is not the governing clarified target.
-/
abbrev theorem3_2_gaussian_randomized_policy_counterexample :=
  @paper_theorem3_2_gaussian_randomized_policy_counterexample

/--
Clarified optional-reporting Theorem 3.2 for every supplied source-model
equilibrium/fibre. The model makes the reported branch deterministic and keeps
the no-report law arbitrary; the source's latent-skill-or-observable fairness
alternative is explicit, with the model's checked implication reducing the
latent branch to the operational observable-law comparison used by the proof.
-/
def theorem3_2_optional_reporting_clarified_modelSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedOptionalReportingModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base),
    LG21OptionalOperationalTestBlank
      (model.scoreLaw e base)
      (model.policy.baseOnlyLaw e base)
      (model.reporterSet e base)
      (lg21OptionalDeterministicReporterKernel
        (model.reporterSet e base)
        (model.reporterSet_measurable e base)
        (model.reporterOutput e base)
        (model.reporterOutput_measurable e base)
        (model.policy.baseOnlyLaw e base))


/--
Clarified report-required Theorem 3.2 for every supplied source-model
equilibrium/fibre. The reported branch is a deterministic transform of the
noisy score, the no-take law is arbitrary, and the source's latent-skill-or-
observable fairness alternative is retained before the checked implication to
the observable output-law comparison.
-/
def theorem3_2_report_required_clarified_modelSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base),
    gaussianReal (model.populationMean e base) (model.populationVariance e base)
        (model.takerSet e base) = 0 \/
      ∀ᵐ skill ∂gaussianReal (model.populationMean e base)
        (model.populationVariance e base),
        lg21ReportRequiredOperationalKernel
          (model.takerSet e base)
          (model.takerSet_measurable e base)
          (model.reportedKernel e base)
          (model.policy.baseOnlyLaw e base) skill = model.policy.baseOnlyLaw e base


/-! ## Lemma 4.1: observed-access strategy-proofness -/

/--
The mandatory-given-access protocol is direct: source feasibility forces every
access action to be `takeAndReport`, and the same literal finite Gaussian
population supplies the Definition 6 resampling experiment.
-/
abbrev lemma4_1_mandatory_given_access_literal_source :=
  @lg21_mandatoryGivenAccess_literal_source_closeout

/--
Conditional all-protocol unraveling support. This consumes the legacy
one-direction entry carriers and therefore does not establish the source
Lemma 4.1 equilibrium claim: it has neither a nonvacuity witness nor the
two-sided closed-profile obligations needed for voluntary exits. It remains a
local analytic diagnostic while that source bridge is repaired.
-/
abbrev lemma4_1_all_observed_access_protocols_conditional_unraveling :=
  @lg21ContinuousGaussianAccessPopulation_lemma4_1_all_protocols_of_sourceTimed







/--
Lemma 4.1 under the declared Section 4 operational convention. The three
universal fields keep the source's requirement regimes separate: mandatory
actions are feasible by construction, while the voluntary actions arise from
source-timed positive-mass profiles selected by the fibrewise maximal
active-branch rule. The remaining fields state the source-relevant action
uniqueness almost everywhere. This does not identify static-RCD null-branch
versions, PBO records, or arbitrary raw Definition 1 equilibria.
-/
def lemma4_1_observed_access_strategy_proofnessSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature),
    Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium source.population,
      ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
        mandatory.action student = LG21AccessAction.takeAndReport) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          optionalProfile.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true ∧
            optionalProfile.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) = true) ∧
      (∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          reportRequiredProfile.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) = true) ∧
      (∀ left right : LG21OptionalActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.actions.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) ∧
          left.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student) =
            right.selected.actions.reportDecision
              (lg21ContinuousPopulationBase source.test_feature student)
              (lg21ContinuousPopulationFeature source.test_feature student)) ∧
      ∀ left right : LG21ReportRequiredActiveBranchProfile source,
        ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw source.population,
          left.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student) =
            right.selected.takeDecision
              (lg21ContinuousPopulationSkill student)
              (lg21ContinuousPopulationBase source.test_feature student)


universe uLemma41

/-- Lemma 4.1 on the actual observed-access Gaussian source and the governing
positive-mass active-branch profiles.  This is the approved Section 4 a.e.
interpretation; it introduces no generic affine/cutoff/tail assumptions and no
off-path pointwise PBO completion. -/
def lemma4_1_observed_access_strategy_proofness_source_coreSpec : Prop :=
  lemma4_1_observed_access_strategy_proofnessSpec.{uLemma41}



/-- Corrected local raw-score indifference equation used in the Lemma 4.1 proof. -/
abbrev lemma4_1_taking_indifference_affine_inverse :=
  @paper_lemma4_1_taking_indifference_affine_inverse

/-! ## Propositions 4.2--4.3: observed-access information gaps -/



/--
Proposition 4.2 across the three requirement policies advertised by the source.
Each conjunct retains its own protocol-specific profile quantifier; the theorem
does not require a shared profile, an equality of off-path outputs, or any
cross-protocol stability premise.
-/
def proposition4_2_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (noAccessEstimateKernel : Kernel
      (LG21NonTestFeature Feature source.test_feature -> ℝ) ℝ)
    [IsMarkovKernel noAccessEstimateKernel],
    (Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        LG21P42OptionalActiveBranchCanonicalPolicyWitness source optionalProfile
          noAccessEstimateKernel) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        LG21P42ReportRequiredActiveBranchCanonicalPolicyWitness source
          reportRequiredProfile noAccessEstimateKernel) ∧
    (Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ mandatoryProfile : LG21P42MandatoryGivenAccessPBOProfile source,
        LG21P42MandatoryGivenAccessCanonicalPolicyWitness source
          mandatoryProfile noAccessEstimateKernel)


/--
The paper-facing core of Proposition 4.2.  The source says that the students'
requirement-policy strategy space is irrelevant once the school observes an
actual score and applies the Bayesian posterior.  Accordingly this statement
quantifies directly over the source Gaussian observed-score model and over an
arbitrary base-only no-access policy; no equilibrium-branch selector or
protocol-specific profile is part of the proposition.
-/
def proposition4_2_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21P42ObservedScoreGaussianPBOModel Base)
    (base : Base) {skillLow skillHigh : ℝ},
    skillLow < skillHigh →
      ¬ lg21P42ObservedScoreLatentSkillFair model


/--
Conditional optional actual-output gaps for the Proposition 4.3 calculation.
This is analytic support; the direct active-branch endpoints below supply the
source-facing voluntary routes under the recorded operational convention.
-/
abbrev proposition4_3_conditional_optional_source_timed :=
  @lg21ContinuousGaussianPopulation_optional_sourceTimed_proposition43_actual_gaps

/-- The mandatory Gaussian source construction has the Proposition 4.3 gaps. -/
abbrev proposition4_3_mandatory_source :=
  @LG21MandatorySection4Source.proposition43_mandatory_actual_measure_gaps

/--
Nonvacuous mandatory-given-access witness for the Proposition 4.3 calculation.
Feasibility fixes the access action, so this route does not rely on a voluntary
null-branch equilibrium convention.
-/
abbrev proposition4_3_mandatory_given_access_nonvacuity :=
  @lg21ContinuousGaussianPopulation_mandatory_actualPBO_not_fair_exists_literalSource





/--
Analytic strengthening for Proposition 4.3: every selected PBO profile in
each requirement regime fails both fairness predicates.  The source-facing
claim below retains the existential equilibrium quantifier dictated by
Definitions 3 and 4.  The voluntary and mandatory PBOs remain independently
quantified because their attained information branches differ; this does not
impose one shared no-report output or an off-path completion across protocols.
-/
def proposition4_3_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput))
     Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    (Nonempty (LG21P43MandatoryGivenAccessPBOProfile source hnoAccess) ∧
      ∀ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21P43MandatoryGivenAccessFairnessFailure source hnoAccess profile
          mandatoryNoReportPayoff)


/--
Proposition 4.3 at the quantifier strength stated by Definitions 3 and 4.
Those definitions call a policy fair only when its distributional comparison
holds in every equilibrium.  Thus, for each of the three requirement regimes,
this result supplies one PBO equilibrium whose induced estimates fail both
observable and demographic fairness.  The stronger result that every selected
profile fails remains available separately as analytic support.
-/
def proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibriumSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false})
    (noAccessOutput : Bool × (ℝ × (Feature -> ℝ)) -> ℝ)
    (hnoAccessPBO : LG21ContinuousGaussianNoAccessPopulationPBO
      source.population hnoAccess source.test_feature noAccessOutput),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess actualOutput noAccessOutput))
     (∃ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
     (∃ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
     ∃ (profile : LG21P43MandatoryGivenAccessPBOProfile source hnoAccess)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianNoAccessPopulationLaw_isProbability source.population
            hnoAccess
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianNoAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance baseMeanVariance : ℝ)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseMean : Measurable baseMean)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
              baseLaw ⊗ₘ gaussianLocationKernel
                baseMean hbaseMean baseVariance.toNNReal ∧
            0 ≤ baseMeanVariance ∧
            (¬ LG21ObservedAccessDeterministicObservableFairAE baseLaw
                (lg21ContinuousPopulationBase source.test_feature)
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess
                  (lg21ObservedAccessActualOutput
                    (lg21ContinuousPopulationBase source.test_feature)
                    (lg21ContinuousPopulationFeature source.test_feature)
                    profile.mandatory.action profile.reportedPayoff mandatoryNoReportPayoff)
                  profile.noAccessOutput)) ∧
              (¬ LG21ObservedAccessDeterministicDemographicallyFair
                (lg21ContinuousGaussianAccessPopulationLaw source.population)
                (lg21ContinuousGaussianNoAccessPopulationLaw source.population)
                (lg21ObservedAccessDeterministicTwoBranchOutput
                  lg21ContinuousPopulationAccess
                  (lg21ObservedAccessActualOutput
                    (lg21ContinuousPopulationBase source.test_feature)
                    (lg21ContinuousPopulationFeature source.test_feature)
                    profile.mandatory.action profile.reportedPayoff mandatoryNoReportPayoff)
                  profile.noAccessOutput)))


/-- The source's zero-mean Gaussian signal model after adjoining the test as
one additional independent signal. The new coordinate has noise law
`N(0, testNoiseVariance)`; there is no free noise-offset parameter. -/
def lg21GaussianSignalFamilyWithTest
    {Feature : Type*} [Fintype Feature]
    (baseSignals : GaussianSignalFamily Feature)
    (testNoiseVariance : ℝ) (testNoiseVariance_pos : 0 < testNoiseVariance) :
    GaussianSignalFamily (Option Feature) where
  priorMean := baseSignals.priorMean
  priorVar := baseSignals.priorVar
  noiseVar
    | none => testNoiseVariance
    | some feature => baseSignals.noiseVar feature
  priorVar_pos := baseSignals.priorVar_pos
  noiseVar_pos
    | none => testNoiseVariance_pos
    | some feature => baseSignals.noiseVar_pos feature


/-- Proposition 4.3's direct source-model comparison. Access students' PBO
uses the common base signals and the additional zero-mean test signal;
no-access students' PBO uses the common base signals only. -/
def lg21CenteredExtraTestPosteriorLawSurface
    {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (baseSignals : GaussianSignalFamily Feature)
    (testNoiseVariance : ℝ) (testNoiseVariance_pos : 0 < testNoiseVariance) :
    LG21SourceLawPolicySurface ℝ PUnit ℝ GaussianScaleLaw where
  Equilibrium := PUnit
  latentAccessLaw := fun _ _ _ =>
    (lg21GaussianSignalFamilyWithTest baseSignals testNoiseVariance
      testNoiseVariance_pos).posteriorMeanScaleLaw
  latentNoAccessLaw := fun _ _ _ => baseSignals.posteriorMeanScaleLaw
  observableAccessLaw := fun _ _ =>
    (lg21GaussianSignalFamilyWithTest baseSignals testNoiseVariance
      testNoiseVariance_pos).posteriorMeanScaleLaw
  observableNoAccessLaw := fun _ _ => baseSignals.posteriorMeanScaleLaw
  demographicAccessLaw := fun _ =>
    (lg21GaussianSignalFamilyWithTest baseSignals testNoiseVariance
      testNoiseVariance_pos).posteriorMeanScaleLaw
  demographicNoAccessLaw := fun _ => baseSignals.posteriorMeanScaleLaw
  baseOnlyLaw := fun _ _ => baseSignals.posteriorMeanScaleLaw
  fullFeatureLaw := fun _ _ _ =>
    (lg21GaussianSignalFamilyWithTest baseSignals testNoiseVariance
      testNoiseVariance_pos).posteriorMeanScaleLaw

/--
The paper-facing core of Proposition 4.3.  It states the two policy-law
comparisons directly for the source Gaussian signal family: access students'
Bayesian estimate uses the extra test signal, while no-access students'
Bayesian estimate uses the common non-test signals.  Strategic profile and
active-branch implementation records are not premises of this information-gap
claim.
-/
def proposition4_3_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [Nonempty Feature]
    (baseSignals : GaussianSignalFamily Feature)
    (testNoiseVariance : ℝ) (testNoiseVariance_pos : 0 < testNoiseVariance),
    let policy : LG21SourceLawPolicySurface.{0, 0, 0, 0, 0}
        ℝ PUnit.{1} ℝ GaussianScaleLaw :=
      lg21CenteredExtraTestPosteriorLawSurface.{_, 0, 0} baseSignals
        testNoiseVariance testNoiseVariance_pos
    ¬ lg21SourceLawObservablyFair policy ∧
      ¬ lg21SourceLawDemographicallyFair policy


/-- Corrected local direct marginal Gaussian comparison supporting Proposition 4.3. -/
abbrev proposition4_3_actual_gaussian_measure_repair :=
  @paper_proposition4_3_actual_gaussian_measure_observable_and_demographic_gaps



/-! ## Definition 6 and Theorem 4.4: resampling policy -/

/-- Definition 6's access-side continuous estimate kernel. -/
abbrev definition6_continuous_access_estimate_kernel :=
  @lg21ContinuousAccessEstimateKernel

/-- Definition 6's no-access continuous resampling estimate kernel. -/
abbrev definition6_continuous_resampling_estimate_kernel :=
  @lg21ContinuousResamplingEstimateKernel

/-- Definition 6's access-side estimate law. -/
abbrev definition6_continuous_access_estimate_law :=
  @paper_definition6_continuous_access_estimate_law

/-- Definition 6's no-access resampling estimate law. -/
abbrev definition6_continuous_no_access_resampling_law :=
  @paper_definition6_continuous_no_access_resampling_law


/--
Conditional all-protocol output-law transport. Its voluntary carriers have
not been selected by the recorded active-branch convention, so it remains
analytic support rather than a source-facing Theorem 4.4 route.
-/
abbrev theorem4_4_conditional_all_observed_access_protocols_actual_output_eq_noAccessResampling :=
  @lg21ContinuousGaussianAccessPopulation_allProtocols_actualOutput_eq_noAccessResampling_of_literalSource

/-- Conditional optional actual-output resampling transport. -/
abbrev theorem4_4_conditional_optional_source_timed :=
  @lg21ContinuousGaussianPopulation_optional_sourceTimed_actualOutput_eq_noAccessResampling

/-- The mandatory source construction's Gaussian resampling equality. -/
abbrev theorem4_4_mandatory_source_gaussian_resampling_fair :=
  @LG21MandatorySection4Source.theorem44_mandatory_source_gaussian_resampling_fair

/--
Mandatory-given-access actual-output fairness under the attained PBO. This
route is nonvacuous at the action level because feasibility fixes reporting.
-/
abbrev theorem4_4_mandatory_given_access_actual_output_fairness :=
  @lg21ContinuousGaussianAccessPopulation_mandatoryObservedAccessOutput_observableAndDemographicFair_of_pbo





/--
Theorem 4.4 across the three requirement policies advertised by the source.
Each conjunct is a separate protocol instance of Definition 6's common
source-derived resampling construction. The statement does not invent a
simultaneous profile, require a common off-path voluntary action, or use the
conditional legacy all-protocol bridge as source-result evidence.
-/
def theorem4_4_all_observed_access_requirement_protocolsSpec : Prop :=
  ∀ {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (source : LG21ObservedAccessGaussianSource Feature)
    (hnoAccess : 0 < source.population.accessLaw {false}),
    (let claim : (Bool × (ℝ × (Feature -> ℝ)) -> ℝ) -> Prop :=
      fun actualOutput =>
        letI : IsProbabilityMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) :=
          lg21ContinuousGaussianAccessPopulationLaw_isProbability source.population
            source.access_positive
        letI : IsFiniteMeasure
            (lg21ContinuousGaussianAccessPopulationLaw source.population) := ⟨by simp⟩
        ∃ (baseLaw : Measure (LG21NonTestFeature Feature source.test_feature -> ℝ))
            (baseMean : (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ)
            (baseVariance : ℝ) (hbaseMean : Measurable baseMean)
            (hbaseLaw : IsProbabilityMeasure baseLaw)
            (hbaseVariance : 0 < baseVariance),
          lg21ContinuousGaussianFullBaseLatentPrimitiveLaw source.population
              source.test_feature =
            baseLaw ⊗ₘ gaussianLocationKernel
              baseMean hbaseMean baseVariance.toNNReal ∧
          (letI : IsProbabilityMeasure baseLaw := hbaseLaw
           let S : LG21GaussianPBOResamplingSource
              (LG21NonTestFeature Feature source.test_feature -> ℝ) :=
            { baseLaw := baseLaw
              baseLaw_isProbability := inferInstance
              posteriorBaseMean := baseMean
              posteriorBaseMean_measurable := hbaseMean
              posteriorBaseVariance := baseVariance.toNNReal
              posteriorBaseVariance_pos := by
                rw [NNReal.coe_pos, Real.toNNReal_pos]
                exact hbaseVariance
              testNoiseVariance := source.population.noiseVariance source.test_feature
              testNoiseVariance_pos := source.test_noise_variance_positive }
           LG21ObservedAccessFair source.population source.test_feature
             { accessOutput := actualOutput
               noAccessKernel := lg21D6NoAccessResamplingEstimateKernel S
               noAccessKernel_isMarkov := inferInstance })
     Nonempty (LG21OptionalActiveBranchProfile source) ∧
      Nonempty (LG21ReportRequiredActiveBranchProfile source) ∧
      (∀ optionalProfile : LG21OptionalActiveBranchProfile source,
        claim
          (lg21OptionalSourceTimedActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            optionalProfile.selected.actions)) ∧
      ∀ reportRequiredProfile : LG21ReportRequiredActiveBranchProfile source,
        claim
          (lg21ReportRequiredSequentialActualOutput
            (lg21ContinuousPopulationBase source.test_feature)
            (lg21ContinuousPopulationFeature source.test_feature)
            (lg21ContinuousPopulationSkill (Feature := Feature))
            reportRequiredProfile.selected)) ∧
    (Nonempty (LG21P42MandatoryGivenAccessPBOProfile source) ∧
      ∀ (profile : LG21P42MandatoryGivenAccessPBOProfile source)
        (mandatoryNoReportPayoff :
          (LG21NonTestFeature Feature source.test_feature -> ℝ) -> ℝ),
        LG21T44MandatoryGivenAccessResamplingFairnessCertificate source hnoAccess
          profile mandatoryNoReportPayoff)


/--
The paper-facing core of Theorem 4.4.  Definition 6 uses the same
base-conditioned score experiment and the same Bayesian posterior-mean map on
the actual-access and synthetic-score branches.  Their conditional estimate
laws are therefore equal at every base profile, and mixing those pointwise
equal kernels over the base population gives demographic equality.
-/
def theorem4_4_all_observed_access_requirement_protocols_source_coreSpec : Prop :=
  ∀ {Omega Base Test : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test]
    (policy : LG21Definition6ExactResamplingPolicy Omega Base Test)
    (baseLaw : Measure Base),
    (∀ base,
      ((Kernel.id ×ₖ policy.testGivenBase).map
          (fun z => policy.posteriorEstimate z.1 z.2)) base =
        lg21Definition6ExactNoAccessEstimateKernel policy base) ∧
      Measure.bind baseLaw
          ((Kernel.id ×ₖ policy.testGivenBase).map
            (fun z => policy.posteriorEstimate z.1 z.2)) =
        Measure.bind baseLaw (lg21Definition6ExactNoAccessEstimateKernel policy)




/-! ## Material prose claims discovered by the current source-only inventory -/

/-- The paper's distributional-equality notation is literal equality of laws. -/
def distributional_equality {Law : Type*} (left right : Law) : Prop :=
  left = right

/-- A report rule indexed by latent skill is independent of skill when it is
the lift of the source's base-and-realized-score rule. -/
def report_decision_skill_independent
    {Skill Base Test : Type*}
    (report : Skill → Base → Test → Bool) : Prop :=
  ∀ q q' base score, report q base score = report q' base score

/-- The source report rule has no latent-skill argument once the score and
base features have been realized. -/
def report_decision_skill_independenceSpec : Prop :=
  ∀ {Skill Base Test : Type*} (report : Base → Test → Bool),
    report_decision_skill_independent
      (fun (_ : Skill) base score => report base score)

universe uSkill uBase uTest uEstimate uEquilibrium uLaw

/-- The exact continuous-law implication chain asserted after Definition 4. -/
def fairness_implication_chainSpec : Prop :=
  ∀ {Skill : Type uSkill} {Base : Type uBase} {Test : Type uTest}
    {Estimate : Type uEstimate}
    [MeasurableSpace Skill] [MeasurableSpace Base]
    [MeasurableSpace Estimate]
    (S : LG21SourceLawPolicySurface.{uSkill, uBase, uTest, uEstimate, uEquilibrium}
      Skill Base Test (Measure Estimate))
    (skillGivenBase : Kernel Base Skill)
    (baseLaw : Measure Base)
    (latentAccessKernel latentNoAccessKernel :
      S.Equilibrium → Base → Kernel Skill Estimate)
    (observableAccessKernel observableNoAccessKernel :
      S.Equilibrium → Kernel Base Estimate)
    (hLatentAccess :
      ∀ e base skill,
        latentAccessKernel e base skill = S.latentAccessLaw e skill base)
    (hLatentNoAccess :
      ∀ e base skill,
        latentNoAccessKernel e base skill = S.latentNoAccessLaw e skill base)
    (hObservableAccessLatent :
      ∀ e base,
        S.observableAccessLaw e base =
          Measure.bind (skillGivenBase base) (latentAccessKernel e base))
    (hObservableNoAccessLatent :
      ∀ e base,
        S.observableNoAccessLaw e base =
          Measure.bind (skillGivenBase base) (latentNoAccessKernel e base))
    (hObservableAccessKernel :
      ∀ e base, observableAccessKernel e base = S.observableAccessLaw e base)
    (hObservableNoAccessKernel :
      ∀ e base, observableNoAccessKernel e base = S.observableNoAccessLaw e base)
    (hDemographicAccess :
      ∀ e,
        S.demographicAccessLaw e =
          Measure.bind baseLaw (observableAccessKernel e))
    (hDemographicNoAccess :
      ∀ e,
        S.demographicNoAccessLaw e =
          Measure.bind baseLaw (observableNoAccessKernel e)),
    (lg21SourceLawLatentSkillFair S → lg21SourceLawObservablyFair S) ∧
      (lg21SourceLawObservablyFair S →
        lg21SourceLawDemographicallyFair S)

/-- A constant-output policy is the explicit witness behind the source's
observation that ignoring test scores can trivially satisfy all fairness
notions. -/
def test_score_ignoring_law_surface
    (Skill Base Test Law Equilibrium : Type*) (law : Law) :
    LG21SourceLawPolicySurface Skill Base Test Law where
  Equilibrium := Equilibrium
  latentAccessLaw := fun _ _ _ => law
  latentNoAccessLaw := fun _ _ _ => law
  observableAccessLaw := fun _ _ => law
  observableNoAccessLaw := fun _ _ => law
  demographicAccessLaw := fun _ => law
  demographicNoAccessLaw := fun _ => law
  baseOnlyLaw := fun _ _ => law
  fullFeatureLaw := fun _ _ _ => law

/-- Ignoring every test-dependent input gives a policy that is test-blank and
satisfies Definitions 2--4. -/
def ignoring_test_scores_achieves_fairnessSpec : Prop :=
  ∀ (Skill Base Test Law Equilibrium : Type*) (law : Law),
    let S := test_score_ignoring_law_surface
      Skill Base Test Law Equilibrium law
    lg21SourceLawTestBlank S ∧
      lg21SourceLawLatentSkillFair S ∧
      lg21SourceLawObservablyFair S ∧
      lg21SourceLawDemographicallyFair S

/-- Every proposition schema built from the four law-level fairness/blankness
predicates is invariant when the source's access/nonaccess labels are replaced
by reporter/nonreporter labels.  This quantifies over the result being
transported, rather than recording only four definition-level equivalences. -/
def reporting_conditioned_generalizationSpec : Prop :=
  ∀ (Skill : Type uSkill) (Base : Type uBase) (Test : Type uTest)
    (Law : Type uLaw)
    (R : LG21ReportingConditionedLawPolicySurface.{uSkill, uBase, uTest, uLaw,
      uEquilibrium} Skill Base Test Law)
    (Result : Prop → Prop → Prop → Prop → Prop),
    Result
        (lg21ReportingConditionedLatentSkillFair R)
        (lg21ReportingConditionedObservablyFair R)
        (lg21ReportingConditionedDemographicallyFair R)
        (lg21ReportingConditionedTestBlank R) ↔
      Result
        (lg21SourceLawLatentSkillFair R.toSourceLawSurface)
        (lg21SourceLawObservablyFair R.toSourceLawSurface)
        (lg21SourceLawDemographicallyFair R.toSourceLawSurface)
        (lg21SourceLawTestBlank R.toSourceLawSurface)

/-- The threshold-acceptance interpretation following Theorem 4.4. -/
def thompson_acceptance_interpretationSpec : Prop :=
  ∀ {Omega Base Test : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Base] [MeasurableSpace Test]
    (experiment : LG21Definition6ExactResamplingPolicy Omega Base Test)
    (base : Base) (cutoff : ℝ),
    lg21Definition6ExactNoAccessEstimateKernel experiment base (Set.Ici cutoff) =
        experiment.testGivenBase base
          {test | cutoff ≤ experiment.posteriorEstimate base test} ∧
      ((Kernel.id ×ₖ experiment.testGivenBase).map
          (fun z => experiment.posteriorEstimate z.1 z.2)) base
          (Set.Ici cutoff) =
        lg21Definition6ExactNoAccessEstimateKernel experiment base (Set.Ici cutoff)

/-- Source modeling convention used in the Lemma 4.1 proof: taking is selected
when the probability of a better result exceeds that of a worse result. -/
def test_taking_probability_preference
    (probabilityBetter probabilityWorse : ℝ) : Prop :=
  probabilityWorse < probabilityBetter

/-- Approved corrected report-required target for the proof-side presentation
at the end of the Theorem 3.2 appendix proof.  The proposition is repeated
transparently because this source presentation has its own correction record;
it is not an alias-shaped semantic target. -/
def theorem3_2_report_required_proof_conclusion_clarifiedSpec : Prop :=
  ∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hFair : lg21SourceLawLatentSkillFair model.policy \/
      lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base),
    gaussianReal (model.populationMean e base) (model.populationVariance e base)
        (model.takerSet e base) = 0 \/
      ∀ᵐ skill ∂gaussianReal (model.populationMean e base)
        (model.populationVariance e base),
        lg21ReportRequiredOperationalKernel
          (model.takerSet e base)
          (model.takerSet_measurable e base)
          (model.reportedKernel e base)
          (model.policy.baseOnlyLaw e base) skill = model.policy.baseOnlyLaw e base

/-- Approved corrected proof-summary target for the two hidden-access
voluntary schedules.  The archival `demographic` word is governed by the
recorded correction to `observable`, and each schedule's operational target
is exposed rather than hidden behind a theorem-name conjunction. -/
def theorem3_2_observable_summary_clarifiedSpec : Prop :=
  (∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedOptionalReportingModel Base)
    (hObservable : lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base),
    LG21OptionalOperationalTestBlank
      (model.scoreLaw e base)
      (model.policy.baseOnlyLaw e base)
      (model.reporterSet e base)
      (lg21OptionalDeterministicReporterKernel
        (model.reporterSet e base)
        (model.reporterSet_measurable e base)
        (model.reporterOutput e base)
        (model.reporterOutput_measurable e base)
        (model.policy.baseOnlyLaw e base))) ∧
  (∀ {Base : Type*} [MeasurableSpace Base]
    (model : LG21ClarifiedReportRequiredModel Base)
    (hObservable : lg21SourceLawObservablyFair model.policy)
    (e : model.policy.Equilibrium) (base : Base),
    gaussianReal (model.populationMean e base) (model.populationVariance e base)
        (model.takerSet e base) = 0 \/
      ∀ᵐ skill ∂gaussianReal (model.populationMean e base)
        (model.populationVariance e base),
        lg21ReportRequiredOperationalKernel
          (model.takerSet e base)
          (model.takerSet_measurable e base)
          (model.reportedKernel e base)
          (model.policy.baseOnlyLaw e base) skill = model.policy.baseOnlyLaw e base)

/--
The material requirement-policy scope statement as a policy-indexed family.
Each constructor exposes the checked results for that requirement regime;
quantifying over `policy` records the advertised across-regime scope instead
of presenting an unindexed finite checklist.
-/
def requirement_policy_scope_generalizationSpec : Prop :=
  ∀ policy : LG21RequirementPolicy,
    match policy with
    | .noRequirements =>
        theorem3_1_optional_reporting_source_timedSpec.{0} ∧
          theorem3_2_optional_reporting_clarified_modelSpec.{0} ∧
          lemma4_1_observed_access_strategy_proofness_source_coreSpec.{0} ∧
          proposition4_2_all_observed_access_requirement_protocols_source_coreSpec.{0} ∧
          proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibriumSpec.{0} ∧
          theorem4_4_all_observed_access_requirement_protocols_source_coreSpec.{0, 0, 0}
    | .reportRequiredConditionalTaking =>
        theorem3_1_report_required_source_timedSpec.{0, 0} ∧
          theorem3_2_report_required_clarified_modelSpec.{0} ∧
          lemma4_1_observed_access_strategy_proofness_source_coreSpec.{0} ∧
          proposition4_2_all_observed_access_requirement_protocols_source_coreSpec.{0} ∧
          proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibriumSpec.{0} ∧
          theorem4_4_all_observed_access_requirement_protocols_source_coreSpec.{0, 0, 0}
    | .reportRequiredGivenAccess =>
        lemma4_1_observed_access_strategy_proofness_source_coreSpec.{0} ∧
          proposition4_2_all_observed_access_requirement_protocols_source_coreSpec.{0} ∧
          proposition4_3_each_requirement_protocol_has_unfair_pbo_equilibriumSpec.{0} ∧
          theorem4_4_all_observed_access_requirement_protocols_source_coreSpec.{0, 0, 0}

end PaperInterface

end

end LG21TestOptionalPolicies
