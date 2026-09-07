import LG21TestOptionalPolicies.DiscussionGeneralizations
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLocalTailCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry
import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchSelection

/-!
# Source Conditions: LG21 Test-Optional Policies

These declarations document source-model conditions and approved
clarifications used during the LG21 remediation. They are mathematical
predicates, not proof certificates or caller-supplied premises of the selected
paper-facing endpoints. The clarified Theorem 3.2 conditions are listed
separately so the repaired theorem does not conceal a policy restriction in an
alias.
-/

namespace LG21TestOptionalPolicies

open AppliedModelingLib
open MeasureTheory ProbabilityTheory

/-- The source Gaussian prior and every observed signal have nonzero variance. -/
abbrev assumption_source_gaussian_variances_nondegenerate
    {Feature : Type*}
    (priorVariance : NNReal) (noiseVariance : Feature → NNReal) : Prop :=
  priorVariance ≠ 0 ∧ ∀ feature, noiseVariance feature ≠ 0

/-- The Bayesian-optimal policy returns the posterior expected latent skill. -/
abbrev assumption_bayesian_optimal_estimation
    {Information : Type*}
    (policyEstimate posteriorMean : Information → ℝ) : Prop :=
  ∀ information, policyEstimate information = posteriorMean information

/-- The requirement regime is one of the three protocols stated in the paper. -/
abbrev assumption_source_requirement_protocol
    (protocol : LG21SequentialRequirementProtocol) : Prop :=
  protocol = LG21SequentialRequirementProtocol.optionalReporting ∨
    protocol = LG21SequentialRequirementProtocol.reportRequiredAfterTaking ∨
      protocol = LG21SequentialRequirementProtocol.reportRequiredGivenAccess

/--
The optional-reporting candidate scope ruled out by the approved Theorem 3.1
operational stability refinement.  Taking the candidate record as a direct
input makes every positive-mass, PBO, response, and gain obligation available
to semantic review.  This predicate adds no new premise: its universal closure
over the candidate type is definitionally the visible `Not (Nonempty ...)`
stability premise.
-/
abbrev source_convention_theorem3_1_optional_local_candidate_excluded
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (_candidate : LG21HiddenAccessSourceLocalCandidateEntry E hnoAccess) : Prop :=
  False

/--
The report-required local-tail candidate scope ruled out by the approved
Theorem 3.1 operational stability refinement.  The direct record input exposes
the candidate's positive branches, recalibrated PBOs, measurability, and
strict-gain obligations to semantic review; it does not strengthen the
paper-facing theorem beyond its already visible stability premise.
-/
abbrev source_convention_theorem3_1_report_required_local_tail_candidate_excluded
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (_candidate : LG21ReportRequiredLocalTailEntry
      (M := M) (testFeature := testFeature) currentTake) : Prop :=
  False

/--
Section 4's operational voluntary-equilibrium convention for optional
reporting.  It makes the source's ``any fraction is unstable'' unraveling
reading precise: among source-timed, positive-mass self-enforcing candidates,
the selected full-action branch is fibrewise maximal almost everywhere.  It is
not derived from the static-RCD predicate in Definition 1, and it does not
assign a PBO or a payoff to an unattained branch.
-/
abbrev source_convention_lemma4_1_optional_maximal_active_branch
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (selected : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature) : Prop :=
  LG21OptionalFibrewiseActiveBranchSelection M haccess testFeature selected

/--
The report-required-after-taking instance of the Section 4 operational
maximal-active-branch convention.  The selected positive-branch PBO record is
an explicit input, so this convention cannot silently use a null no-take
conditional mean.
-/
abbrev source_convention_lemma4_1_report_required_maximal_active_branch
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (selected : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (selectedSource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) selected
        (M.noiseVariance testFeature)) : Prop :=
  LG21ReportRequiredFibrewiseActiveBranchSelection
    M haccess testFeature selected selectedSource

/--
Clarified Theorem 3.2 policy condition: on the entire information branch in
which a test score is reported, the estimate law is a point mass.  The
no-report branch is deliberately not constrained by this predicate.
-/
abbrev assumption_clarified_theorem3_2_deterministic_reported_output
    {Score : Type*}
    (reportedOutputLaw : Score → Measure ℝ) : Prop :=
  ∃ reportedValue : Score → ℝ,
    ∀ score, reportedOutputLaw score = Measure.dirac (reportedValue score)

/--
The finite-expectation clarification used for report-required timing: every
latent skill type evaluates an integrable deterministic reported estimate
under its shifted Gaussian score law.  This is the L1 form needed by Lean's
expectation and Gaussian-transform APIs.
-/
abbrev assumption_clarified_theorem3_2_finite_reporter_expectations
    (reportedValue : ℝ → ℝ) (noiseVariance : NNReal) : Prop :=
  noiseVariance ≠ 0 ∧
    ∀ mean, Integrable reportedValue (gaussianReal mean noiseVariance)

/--
The source resampling policy draws the synthetic no-access test from the same
base-conditioned test kernel as the access population.
-/
abbrev assumption_resampling_uses_source_conditional_test_law
    {Base Test Law : Type*}
    (sourceConditionalTestLaw syntheticConditionalTestLaw : Base → Law) : Prop :=
  ∀ base, syntheticConditionalTestLaw base = sourceConditionalTestLaw base

/--
The Discussion's “appropriate tie-breaking” condition for an admission
probability objective: it preserves and reflects every action comparison by
the expected-estimate objective.
-/
abbrev assumption_admission_probability_order_equivalent_tiebreak
    {Info Action : Type*}
    (E : ChoiceEquilibriumData Info Action)
    (admissionPayoff : Info → Action → ℝ) : Prop :=
  lg21AdmissionPayoffOrderEquivalent E admissionPayoff

end LG21TestOptionalPolicies
