import PZMH20PerformativePrediction.MainTheorems
import PZMH20PerformativePrediction.Assumptions
import PZMH20PerformativePrediction.DomainRelativeRRM
import PZMH20PerformativePrediction.DomainRelativeExistence
import PZMH20PerformativePrediction.DomainRelativeCorollary
import PZMH20PerformativePrediction.StrategicClassificationBridge
import PZMH20PerformativePrediction.DomainRelativeRGD
import PZMH20PerformativePrediction.EmpiricalRRMSamplingRecovery
import PZMH20PerformativePrediction.EmpiricalRRMAllDimensionalRecovery
import PZMH20PerformativePrediction.EmpiricalRRMCriticalDimensionRecovery
import PZMH20PerformativePrediction.CriticalDimensionSampleCountRates
import PZMH20PerformativePrediction.SubcriticalDimensionSampleCount

/-!
# Human-Facing Paper Interface: Performative Prediction

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly. Keep the row-level dashboard and LLM audit statements in this file
for every paper. Move implementation details, proof aliases, and bulky helper
lemmas behind imported modules such as `AuditInterface.lean`, but expose the
audited paper-facing statements directly here; do not use
`paper_interface.audit_surface_path`.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- A material reusable `AppliedModelingLib` primitive may remain a reference here only
  after `audit/library_semantic_review.json` records its exact bounded library
  declaration and an explicit byte-pinned paper-source connection. The
  dashboard and human-review packet show and source-check that declaration
  before the dependent Spec; a library name, docstring, or glossary is not a
  semantic bridge. Do not add a duplicate paper claim merely to restate it.
- If a named theorem needs a hypothesis that is not derived from earlier Lean
  declarations, declare that hypothesis in `Assumptions.lean` and list it in
  `status.json` `review_surface.assumption_names`.
- Then state the named results directly, with assumptions visible in each
  theorem signature by referencing named paper assumptions imported from
  `Assumptions.lean`.
- In the statement-first phase, write every complete source-facing statement as
  a transparent `<name>Spec : Prop` here, exactly once. Put the paired
  theorem/lemma of that exact type in `ProofInterface.lean`; its temporary
  proof body may be `by sorry` only in a private draft. This separation keeps
  the human semantic surface free of thin wrapper declarations.
- Before drafting that Lean surface, independently inventory every material
  source atom from exact pinned source quote bytes. Do not infer source atoms
  from declaration, binder, field, function, or source-map names.
- Run raw-source-to-expanded-Spec statement matching plus Lean-emitted
  premise/conclusion claim-atom review on the skeleton. The semantic comparison uses
  only byte-pinned source quotes (and separately pinned source context) against
  the expanded transparent Spec; map summaries and proof wrappers are not
  semantic inputs. Then freeze each canonical Lean declaration-manifest digest.
- In the proof phase, replace the `ProofInterface.lean` `sorry` with a short
  proof that calls into `MainTheorems.lean` or lower proof files without
  changing the specification or theorem type. Any specification/type change
  invalidates the freeze and requires a fresh statement audit.
- At formalized closeout, complete the v11 realization receipt: Lean Meta checks
  the theorem has exactly the transparent Spec type; each source atom is bound
  to the elaborated Spec surface; closure traversal includes proof and instance
  arguments; and every material terminal has a source, approved correction or
  additional assumption, checked derivation, or version-pinned foundation
  disposition. No data, container, or identifier-based exemption is allowed.
- The transparent `...Spec` is the sole semantic-review target for its source
  claim. The paired theorem/lemma is a proof endpoint whose exact Spec type is
  verified by Lean Meta, not a duplicate source-to-Lean comparison row.
- Keep proof endpoints, exhaustive endpoint aliases, and proof-seam checks in
  `ProofInterface.lean`, implementation modules, or `ProofLedger.lean`, not
  here. Do not create new `PostPaperAudit.lean` or `AuditLedger.lean` files;
  those names are legacy.

## Named Results

Each entry has one semantic-review target (`Spec`) and one proof endpoint (the
paired theorem/lemma). The human dashboard and review packet present that pair
once rather than treating the two declarations as duplicate paper claims.

- Definition 2.1: performative optimality and risk.
- Definition 2.3: performative stability / decoupled risk.
- Definition 3.3: repeated risk minimization and the fixed-point-to-stability bridge.
- Proposition 3.6(a)'s real Dirac linear-loss counterexample.
- Proposition 3.6(b)'s real Dirac regularized-hinge counterexample.
- Proposition 3.6(c)'s real Dirac squared-loss counterexample.
- Proposition 4.2's corrected finite Bernoulli witness for concave
  performative risk; its extra endpoint condition is explicit.
- Theorem 3.5's domain-relative general-measure W₁ contraction, convergence,
  and explicit logarithmic iteration threshold, without differentiation
  under expectation.
- Proposition 4.1's arbitrary-law compact-convex best-response fixed point,
  with an explicit joint-continuity/Berge boundary.
- A candidate derivative-free Theorem 4.3 endpoint whose model is defined only
  on the source domain, pending source-fidelity review.
- Corollary 5.1 for the general-measure strategic-classification model, with
  the actual selected follower response and Stackelberg benchmark explicit.
- Theorem 3.10's corrected compact/continuous exponential-moment bridge. It
  is an explicit additional route to the uniform moment envelope required by
  an adaptive schedule, not a claim that the printed pointwise assumption
  entails that envelope.
- Theorem 3.10's corrected RERM/RGD population data: their source factors,
  stable fixed points, and population contractions are explicit; RERM's
  variational first-order condition is stated on the feasible domain.
- Theorem 3.10's corrected all-round RGD trajectory consequence, with its
  explicit adaptive trace, selected-shell bad-event probability, and
  analytic/numerical premises.
-/

namespace PZMH20PerformativePrediction

open AppliedModelingLib
open MeasureTheory
open ProbabilityTheory
open scoped InnerProductSpace

/-- Definition 2.1's performative-optimality condition. -/
def performativeOptimalitySpec {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  IsPerformativelyOptimal model parameter ↔
    ∀ candidate, performativeRisk model parameter ≤ performativeRisk model candidate

/-- A finite parameter carrier attains the Definition 2.1 performative optimum. -/
def finitePerformativeOptimumExistsSpec {Parameter Data : Type*}
    [Fintype Parameter] [Nonempty Parameter]
    [Fintype Data] [DecidableEq Data] (model : FinitePerformativeModel Parameter Data) : Prop :=
  ∃ parameter, IsPerformativelyOptimal model parameter

/-- Definition 2.3's stability condition, expanded in decoupled-risk notation. -/
def performativeStabilitySpec {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (parameter : Parameter) : Prop :=
  IsStable model parameter ↔
    ∀ candidate,
      decoupledPerformativeRisk model parameter parameter ≤
        decoupledPerformativeRisk model parameter candidate

/-- A fixed point of Definition 3.3's RRM update is stable in Definition 2.3. -/
def rrmFixedPointStableSpec {Parameter Data : Type*}
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (update : Parameter → Parameter)
    (parameter : Parameter) : Prop :=
  IsRRM model update → update parameter = parameter → IsStable model parameter

/--
The exact real-valued linear-loss/Dirac construction in Proposition 3.6(a).
For every positive source pair `(epsilon, beta)`, it records the actual
gradient, convexity/smoothness and absence of strong convexity, W₁ sensitivity,
unique stable point, and a nonconvergent selected RRM trajectory.
-/
def proposition36aExactDiracCounterexampleSpec (epsilon beta gamma : ℝ) : Prop :=
  0 < epsilon → 0 < beta → 0 < gamma →
    IsMeasureRepeatedRiskMinimizationOn (proposition36aMeasureModel epsilon beta)
        proposition36aDomain proposition36aRRMUpdate ∧
    (∀ datum candidate,
      HasGradientAt (fun parameter => proposition36aMeasureLoss beta datum parameter)
        (proposition36aMeasureGradient beta datum candidate) candidate) ∧
    (∀ datum, ConvexOn ℝ Set.univ
      (fun candidate => proposition36aMeasureLoss beta datum candidate)) ∧
    IsJointlySmoothGradient (proposition36aMeasureGradient beta) beta.toNNReal ∧
    IsMeasureWassersteinSensitive (proposition36aMeasureModel epsilon beta) epsilon ∧
    (∀ modulus, 0 < modulus →
      ¬ IsMeasurePointwiseGradientStronglyConvex (proposition36aMeasureModel epsilon beta)
        (proposition36aMeasureGradient beta) modulus) ∧
    (∀ theta,
      IsMeasurePerformativelyStableOn (proposition36aMeasureModel epsilon beta)
        proposition36aDomain theta ↔ theta = 0) ∧
    (¬ ∃ limit : ℝ, Filter.Tendsto
      (fun iteration => proposition36aRRMUpdate^[iteration] 1) Filter.atTop (nhds limit))

/--
The exact real point-mass regularized-hinge construction in Proposition 3.6(b).
The source only needs RRM minimization at the two points on its exhibited
orbit; those two exact domain-constrained minimization steps, rather than an
arbitrary off-orbit selector, are stated explicitly.
-/
def proposition36bExactDiracEndpointCounterexampleSpec
    (epsilon gamma penalty : ℝ) : Prop :=
  0 < epsilon → 0 < gamma → IsProposition36bLargePenalty epsilon gamma penalty →
    IsMeasureWassersteinSensitive (proposition36bMeasureModel epsilon gamma penalty) epsilon ∧
    (∀ datum, StrongConvexOn Set.univ gamma
      (fun candidate => proposition36bMeasureLoss gamma penalty datum candidate)) ∧
    (¬ DifferentiableAt ℝ
      (fun candidate => proposition36bMeasureLoss gamma penalty (epsilon * 2) candidate)
      (proposition36bLowerEndpoint epsilon)) ∧
    ((proposition36bRRMUpdate epsilon 2 ∈ proposition36bDomain epsilon ∧
      ∀ candidate ∈ proposition36bDomain epsilon,
        measureDecoupledPerformativeRisk (proposition36bMeasureModel epsilon gamma penalty)
          2 (proposition36bRRMUpdate epsilon 2) ≤
        measureDecoupledPerformativeRisk (proposition36bMeasureModel epsilon gamma penalty)
          2 candidate) ∧
    (proposition36bRRMUpdate epsilon (proposition36bLowerEndpoint epsilon) ∈
      proposition36bDomain epsilon ∧
      ∀ candidate ∈ proposition36bDomain epsilon,
        measureDecoupledPerformativeRisk (proposition36bMeasureModel epsilon gamma penalty)
          (proposition36bLowerEndpoint epsilon)
          (proposition36bRRMUpdate epsilon (proposition36bLowerEndpoint epsilon)) ≤
        measureDecoupledPerformativeRisk (proposition36bMeasureModel epsilon gamma penalty)
          (proposition36bLowerEndpoint epsilon) candidate)) ∧
    (¬ ∃ limit : ℝ, Filter.Tendsto
      (fun iteration => (proposition36bRRMUpdate epsilon)^[iteration] 2)
        Filter.atTop (nhds limit))

/--
The source-uniform Proposition 3.6(b) existential endpoint.  The source's
smoothness constant is vacuous in this nonsmooth alternative; the witness
chooses a sufficiently large regularization penalty from the positive
`epsilon` and `gamma` constants.
-/
def proposition36bSourceUniformCounterexampleSpec
    (epsilon beta gamma : ℝ) : Prop :=
  0 < epsilon → 0 < beta → 0 < gamma →
    ∃ penalty : ℝ,
      IsProposition36bLargePenalty epsilon gamma penalty ∧
      proposition36bExactDiracEndpointCounterexampleSpec epsilon gamma penalty

/--
The exact real-valued squared-loss/Dirac construction in Proposition 3.6(c).
It records the source model's actual gradient, regularity constants, W₁
sensitivity, RRM update, and all three stated stability/divergence regimes.
-/
def proposition36cExactDiracCounterexampleSpec (epsilon initial : ℝ) : Prop :=
  IsMeasureRepeatedRiskMinimization (proposition36cMeasureModel epsilon)
      (proposition36cRRMUpdate epsilon) ∧
  IsJointlySmoothGradient proposition36cGradient 2 ∧
  IsMeasurePointwiseGradientStronglyConvex (proposition36cMeasureModel epsilon)
      proposition36cGradient 2 ∧
  (∀ datum candidate, HasGradientAt (fun parameter => proposition36cLoss datum parameter)
      (proposition36cGradient datum candidate) candidate) ∧
  (0 ≤ epsilon → IsMeasureWassersteinSensitive (proposition36cMeasureModel epsilon) epsilon) ∧
  (epsilon = 1 → ¬ ∃ theta,
    IsMeasurePerformativelyStable (proposition36cMeasureModel epsilon) theta) ∧
  (epsilon ≠ 1 → ∀ theta,
    IsMeasurePerformativelyStable (proposition36cMeasureModel epsilon) theta ↔
      theta = proposition36cStablePoint epsilon) ∧
  (1 < epsilon → proposition36cStablePoint epsilon < initial →
    Filter.Tendsto (fun iteration => (proposition36cRRMUpdate epsilon)^[iteration] initial)
      Filter.atTop Filter.atTop) ∧
  (1 < epsilon → initial < proposition36cStablePoint epsilon →
    Filter.Tendsto (fun iteration => (proposition36cRRMUpdate epsilon)^[iteration] initial)
      Filter.atTop Filter.atBot)

/--
The feasible parameter-uniform Proposition 3.6(c) counterexample.  The pinned
source prints arbitrary positive `beta` and `gamma`; this corrected endpoint
records the necessary compatibility `gamma ≤ beta` and proves the source
threshold `gamma / beta ≤ epsilon`, including equality, gives a diverging RRM
trajectory.
-/
def proposition36cFeasibleUniformCounterexampleSpec
    (epsilon beta gamma : ℝ) : Prop :=
  0 < epsilon → 0 < beta → 0 < gamma → gamma ≤ beta → gamma / beta ≤ epsilon →
    IsMeasureRepeatedRiskMinimization
        (proposition36cRegularityMeasureModel epsilon beta gamma)
        (proposition36cRegularityRRMUpdate epsilon beta gamma) ∧
    IsJointlySmoothGradient
      (proposition36cRegularityGradient beta gamma) beta.toNNReal ∧
    IsMeasurePointwiseGradientStronglyConvex
      (proposition36cRegularityMeasureModel epsilon beta gamma)
      (proposition36cRegularityGradient beta gamma) gamma ∧
    (∀ datum candidate,
      HasGradientAt
        (fun parameter => proposition36cRegularityLoss beta gamma datum parameter)
        (proposition36cRegularityGradient beta gamma datum candidate) candidate) ∧
    IsMeasureWassersteinSensitive
      (proposition36cRegularityMeasureModel epsilon beta gamma) epsilon ∧
    ∃ initial,
      Filter.Tendsto
        (fun iteration =>
          (proposition36cRegularityRRMUpdate epsilon beta gamma)^[iteration] initial)
        Filter.atTop Filter.atTop

/--
A corrected finite witness for Proposition 4.2.  Its binary data law is valid
on the source interval because both affine endpoint biases lie in `[-1/2,1/2]`.
The witness records the exact displayed risk, the source loss regularity, its
finite Wasserstein sensitivity, and concavity of the resulting risk.
-/
def proposition42CorrectedFiniteWitnessSpec : Prop :=
  ∃ (mu epsilon : ℝ) (hmu : |mu| ≤ (1 : ℝ) / 2)
    (hmuEpsilon : |mu + epsilon| ≤ (1 : ℝ) / 2),
    (1 : ℝ) / 2 < epsilon ∧ epsilon < (2 : ℝ) / 2 ∧
    IsFiniteWassersteinSensitive (correctedProposition42Model mu epsilon hmu hmuEpsilon) epsilon ∧
    (∀ datum candidate,
      HasGradientAt (fun parameter => proposition42Loss parameter datum)
        (proposition42Gradient datum candidate) candidate) ∧
    (∀ datum center candidate,
      proposition42Loss candidate datum ≥ proposition42Loss center datum +
        proposition42Gradient datum center * (candidate - center) +
          (2 : ℝ) / 2 * (candidate - center) ^ 2) ∧
    IsJointlySmoothGradient proposition42Gradient 2 ∧
    (∀ theta : {theta : ℝ // theta ∈ Set.Icc (0 : ℝ) 1},
      performativeRisk (correctedProposition42Model mu epsilon hmu hmuEpsilon) theta =
        (1 : ℝ) / 4 - 2 * theta * mu + (1 - 2 * epsilon) * theta ^ 2) ∧
    ConcaveOn ℝ Set.univ
      (fun theta : ℝ => (1 : ℝ) / 4 - 2 * theta * mu + (1 - 2 * epsilon) * theta ^ 2)

/-- The contraction-convergence conclusion used in Theorem 3.5's proof route. -/
def rrmConvergenceSpec {Parameter : Type*} [MetricSpace Parameter]
    [CompleteSpace Parameter] [Nonempty Parameter]
    (update : Parameter → Parameter) {K : NNReal} (hcontract : ContractingWith K update)
    (initial : Parameter) : Prop :=
  Filter.Tendsto (fun n => update^[n] initial) Filter.atTop
    (nhds (hcontract.fixedPoint update))

/-- Definition 3.7's population repeated-gradient-descent update. -/
def repeatedGradientDescentSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (project : Parameter → Parameter)
    (stepSize : ℝ) : Prop :=
  ∀ deployed, repeatedGradientDescentUpdate model gradient project stepSize deployed =
    project (deployed - stepSize • frozenPopulationGradient model gradient deployed deployed)

/-- Definition 3.9's realized-sample repeated empirical risk minimization rule. -/
def repeatedEmpiricalRiskMinimizationSpec
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    (model : FinitePerformativeModel Parameter Data) (domain : Set Parameter)
    {sampleCount : ℕ} (samples : Parameter → Fin sampleCount → Data)
    (update : Parameter → Parameter) : Prop :=
  IsEmpiricalRepeatedRiskMinimizationOn model domain samples update ↔
    ∀ deployed ∈ domain, update deployed ∈ domain ∧ ∀ candidate ∈ domain,
      empiricalDecoupledPerformativeRisk model (samples deployed) (update deployed) ≤
        empiricalDecoupledPerformativeRisk model (samples deployed) candidate

/-- Definition 3.9's realized-sample repeated empirical gradient-descent update. -/
def repeatedEmpiricalGradientDescentSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data]
    (gradient : Data → Parameter → Parameter) (project : Parameter → Parameter)
    (stepSize : ℝ) {sampleCount : ℕ} (sample : Fin sampleCount → Data) : Prop :=
  ∀ deployed, repeatedEmpiricalGradientDescentUpdate gradient project stepSize sample deployed = project
    (deployed - stepSize • empiricalPopulationGradient gradient sample deployed)

/--
Finite primal transport bridge for Definition 3.1.  This is not yet the
source's arbitrary-distribution Wasserstein-1 equivalence; it is the concrete
finite coupling estimate used by the source proof's Lipschitz-test step.
-/
def finiteTransportSensitivityLipschitzStatisticSpec
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) : Prop :=
  IsFiniteTransportSensitive model sensitivity →
    |pmfExp (model.dataLaw first) statistic - pmfExp (model.dataLaw second) statistic| ≤
      (L : ℝ) * (sensitivity * dist first second)

/--
Finite-PMF Wasserstein-1 bridge for Definition 3.1.  It records the
Lipschitz-test consequence of the finite W₁ infimum, while retaining the
explicit finite-carrier scope.
-/
def finiteWassersteinSensitivityLipschitzStatisticSpec
    {Parameter Data : Type*} [Fintype Data] [DecidableEq Data]
    [MetricSpace Parameter] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data) (sensitivity : ℝ)
    {L : NNReal} {statistic : Data → ℝ} (hstatistic : LipschitzWith L statistic)
    (first second : Parameter) : Prop :=
  IsFiniteWassersteinSensitive model sensitivity →
    |pmfExp (model.dataLaw first) statistic - pmfExp (model.dataLaw second) statistic| ≤
      (L : ℝ) * (sensitivity * dist first second)

/--
Finite version of the gradient-pairing distribution-shift estimate in the
source's Appendix E.1.  It is a proved proof component, not the full
Theorem 3.5 contraction claim.
-/
def finiteTransportSensitivityGradientPairingSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness sensitivity : ℝ)
    (displacement evaluated first second : Parameter) : Prop :=
  0 ≤ smoothness →
  (∀ (left right : Data) (parameter : Parameter),
    ‖gradient left parameter - gradient right parameter‖ ≤ smoothness * dist left right) →
  IsFiniteTransportSensitive model sensitivity →
  |pmfExp (model.dataLaw first) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ) -
      pmfExp (model.dataLaw second) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ)| ≤
    (smoothness * ‖displacement‖) * (sensitivity * dist first second)

/--
Finite-W₁ version of the Appendix E.1 gradient-pairing substep.  The
finite-carrier restriction is deliberate; it is not an arbitrary-measure
Kantorovich--Rubinstein formalization.
-/
def finiteWassersteinSensitivityGradientPairingSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness sensitivity : ℝ)
    (displacement evaluated first second : Parameter) : Prop :=
  0 ≤ smoothness →
  (∀ (left right : Data) (parameter : Parameter),
    ‖gradient left parameter - gradient right parameter‖ ≤ smoothness * dist left right) →
  IsFiniteWassersteinSensitive model sensitivity →
  |pmfExp (model.dataLaw first) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ) -
      pmfExp (model.dataLaw second) (fun datum => ⟪displacement, gradient datum evaluated⟫_ℝ)| ≤
    (smoothness * ‖displacement‖) * (sensitivity * dist first second)

/--
Finite-PMF, whole-parameter-space specialization of Theorem 3.5(a).  It is
not a literal full-paper endpoint because the source permits an arbitrary
closed convex parameter set and defines sensitivity through Wasserstein-1.
-/
def finiteUnconstrainedRRMContractionSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (update : Parameter → Parameter) (hrrm : IsRRM model update)
    (first second : Parameter) : Prop :=
  ‖update first - update second‖ ≤
    (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖

/--
Finite-PMF, whole-parameter-space Theorem 3.5(a) specialization under the
finite Wasserstein-1 sensitivity condition itself.  It remains narrower than
the source because both data laws and W₁ are finite-PMF objects.
-/
def finiteWassersteinUnconstrainedRRMContractionSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (update : Parameter → Parameter) (hrrm : IsRRM model update)
    (first second : Parameter) : Prop :=
  ‖update first - update second‖ ≤
    (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖

/--
Finite-PMF, convex-domain Theorem 3.5(a) specialization under finite-W₁
sensitivity.  An RRM selector supplies the in-domain minimizers; convexity is
used to derive their variational first-order conditions.
-/
def finiteWassersteinConvexRRMContractionSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) : Prop :=
  ‖update first - update second‖ ≤
    (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖

/--
Finite-PMF convex-domain specialization of Theorem 3.5(b) under finite-W₁
sensitivity.  It gives the unique stable point, convergence, and the geometric
RRM error bound on the supplied closed convex parameter domain.
-/
def finiteWassersteinConvexRRMConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) : Prop :=
  ∃ stable ∈ domain, IsStableOn model domain stable ∧
    (∀ other ∈ domain, IsStableOn model domain other → other = stable) ∧
    Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
    ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖

/--
Whole-space arbitrary-probability-measure realization of Theorem 3.5(b).
Unlike the finite-PMF specializations, its distribution shift is stated through
the general W₁ coupling-cost infimum.  Explicit integrability,
differentiation-under-expectation, and strong-monotonicity assumptions record
the analytic obligations needed to connect this result to (A1)--(A2).
-/
def measureWassersteinUnconstrainedRRMConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Nonempty Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hgradient : IsDataGradientLipschitz gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRM model update)
    (hgradientAt : ∀ distributionParameter evaluatedParameter,
      HasGradientAt
        (fun parameter => measureDecoupledPerformativeRisk model distributionParameter parameter)
        (measureFrozenPopulationGradient model gradient distributionParameter evaluatedParameter)
        evaluatedParameter)
    (hstrong : IsMeasureFrozenGradientStronglyMonotone model gradient modulus)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) : Prop :=
  ∃ stable, IsMeasureStable model stable ∧
    (∀ other, IsMeasureStable model other → other = stable) ∧
    Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
    ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖

/--
Arbitrary-probability-measure, closed-convex-domain realization of Theorem
3.5(a).  It takes the source's full A1 joint smoothness and pointwise A2
strong-convexity assumptions; the latter is proved to imply expected-gradient
strong monotonicity.  Differentiation under expectation is discharged by the
reusable dominated theorem, with local loss measurability and pointwise
differentiability retained explicitly.
-/
def measureWassersteinConvexRRMContractionSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsMeasureWassersteinSensitive model sensitivity)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsMeasureRRMOn model domain update)
    (hloss_meas : ∀ distributionParameter evaluatedParameter,
      ∀ᶠ parameter in nhds evaluatedParameter,
        AEStronglyMeasurable (fun datum => model.loss datum parameter)
          (model.dataLaw distributionParameter : Measure Data))
    (hpointwise : ∀ datum parameter,
      HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) : Prop :=
  ‖update first - update second‖ ≤
    (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖

/--
Both parts of Theorem 3.5 for probability laws and losses defined only on the
source's closed convex parameter set. The contraction, unique stable point,
geometric rate, and explicit logarithmic threshold use A1/A2 on that set;
no gradient-integrability or differentiation-under-expectation premise is needed.
-/
def measureWassersteinConvexRRMConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [FiniteDimensional ℝ Parameter]
    [MeasurableSpace Data] [MetricSpace Data]
    (domain : Set Parameter) (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) {smoothness : NNReal}
    (hjoint : (∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        (smoothness : ℝ) * dist first second) ∧
      ∀ first second parameter,
        ‖gradient first parameter - gradient second parameter‖ ≤
          (smoothness : ℝ) * dist first second)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      model.decoupledPerformativeRisk deployed (update deployed) ≤
        model.decoupledPerformativeRisk deployed candidate)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : domain) : Prop :=
  (∀ first second,
      ‖(update first : Parameter) - (update second : Parameter)‖ ≤
        (sensitivity * (smoothness : ℝ) / modulus) *
          ‖(first : Parameter) - (second : Parameter)‖) ∧
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
      (∀ iteration, dist (update^[iteration] initial) stable ≤
        (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) /
            (1 - sensitivity * (smoothness : ℝ) / modulus) ≤ (iteration : ℝ) →
          dist (update^[iteration] initial) stable ≤ radius

/--
Domain-relative realization of both parts of Theorem 3.8. Under A1, A2,
general W₁ sensitivity, and the source step-size and sensitivity restrictions,
the actual Euclidean projection update contracts on an arbitrary nonempty
closed convex finite-dimensional parameter domain. The conclusion includes its
unique stable point, geometric convergence, and the displayed logarithmic
entry bound. The expected pointwise gradient is assumed Bochner integrable at
each feasible deployed/evaluated pair, which is exactly what makes the stated
population update defined.
-/
def measureWassersteinConvexRGDConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [FiniteDimensional ℝ Parameter]
    [MeasurableSpace Data] [MetricSpace Data] {domain : Set Parameter}
    (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter) {smoothness : NNReal}
    (hjoint : (∀ datum first second,
      ‖gradient datum first - gradient datum second‖ ≤
        (smoothness : ℝ) * ‖(first : Parameter) - (second : Parameter)‖) ∧
      ∀ first second parameter,
        ‖gradient first parameter - gradient second parameter‖ ≤
          (smoothness : ℝ) * dist first second)
    (hintegrable : ∀ deployed evaluated : domain,
      Integrable (fun datum => gradient datum evaluated)
        (model.dataLaw deployed : Measure Data))
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : model.IsWassersteinSensitive sensitivity)
    (hmodulus : 0 < modulus)
    (hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    (hclosed : IsClosed domain) (hnonempty : domain.Nonempty) (hconvex : Convex ℝ domain)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : domain) : Prop :=
  let factor := 1 - stepSize * (modulus * (smoothness : ℝ) /
    (modulus + (smoothness : ℝ)) -
      sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))
  (∀ first second,
      dist (DomainRelative.rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize first)
          (DomainRelative.rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize second) ≤
        factor * dist first second) ∧
    ∃ stable : domain, model.IsPerformativelyStable stable ∧
      (∀ other, model.IsPerformativelyStable other → other = stable) ∧
      Filter.Tendsto
        (fun iteration =>
          (DomainRelative.rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
            initial)
        Filter.atTop (nhds stable) ∧
      (∀ iteration,
        dist
          ((DomainRelative.rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
            initial) stable ≤ factor ^ iteration * dist initial stable) ∧
      ∀ radius > 0, ∀ iteration : ℕ,
        Real.log (dist initial stable / radius) / (1 - factor) ≤ (iteration : ℝ) →
        dist
          ((DomainRelative.rgdUpdateOn model gradient hnonempty hclosed hconvex stepSize)^[iteration]
            initial) stable ≤ radius

/--
Finite-PMF, convex-domain specialization of Theorem 3.5(a).  The source's
closedness condition supports its ambient parameter-space/existence setting;
because this statement receives an RRM selector that already returns a
minimizer in `domain`, convexity is the only domain property used in the
variational first-order proof.  Its finite primal transport premise is still
not a literal Wasserstein-1 equivalence.
-/
def finiteConvexRRMContractionSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (first second : Parameter) (hfirst : first ∈ domain) (hsecond : second ∈ domain) : Prop :=
  ‖update first - update second‖ ≤
    (sensitivity * (smoothness : ℝ) / modulus) * ‖first - second‖

/--
Finite-PMF convex-domain specialization of Theorem 3.5(b).  Under the strict
contraction condition, RRM has one domain-stable point and its iterates converge
to it at the geometric rate from the source proof.  This remains a finite
primal-transport specialization rather than literal Wasserstein-1 semantics.
-/
def finiteConvexRRMConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity) (hmodulus : 0 < modulus)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hconvex : Convex ℝ domain)
    (update : Parameter → Parameter) (hrrm : IsRRMOn model domain update)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial : Parameter) (hinitial : initial ∈ domain) : Prop :=
  ∃ stable ∈ domain, IsStableOn model domain stable ∧
    (∀ other ∈ domain, IsStableOn model domain other → other = stable) ∧
    Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
    ∀ iteration, ‖update^[iteration] initial - stable‖ ≤
      (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * ‖initial - stable‖

/--
Finite-PMF primal-transport specialization of Theorem 3.8.  The projection
input splits the two standard Euclidean-projection consequences used by the
source proof: its variational inequality and nonexpansiveness.  The conclusion
combines the sharp displayed contraction rate with part (b)'s unique stable
point and geometric convergence statement.
-/
def finiteConvexRGDConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : Parameter) (hinitial : initial ∈ domain) : Prop :=
  ∃ stable ∈ domain, IsStableOn model domain stable ∧
    (∀ other ∈ domain, IsStableOn model domain other → other = stable) ∧
    Filter.Tendsto
      (fun iteration => (repeatedGradientDescentUpdate model gradient project stepSize)^[iteration] initial)
      Filter.atTop (nhds stable) ∧
    ∀ iteration,
      ‖(repeatedGradientDescentUpdate model gradient project stepSize)^[iteration] initial - stable‖ ≤
        (1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
          sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))) ^ iteration *
            ‖initial - stable‖

/--
Finite-PMF W₁ realization of Theorem 3.8.  The source's Wasserstein
sensitivity premise is represented by the finite coupling-infimum condition;
the conclusion gives the displayed RGD rate and part (b)'s stable-point
existence, uniqueness, and convergence.
-/
def finiteWassersteinConvexRGDConvergesLinearlySpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) {smoothness : NNReal}
    (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {sensitivity modulus : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (hmodulus : 0 < modulus) (hmodulus_le : modulus ≤ (smoothness : ℝ))
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    (domain : Set Parameter) (hclosed : IsClosed domain) (hnonempty : domain.Nonempty)
    (hconvex : Convex ℝ domain) (project : Parameter → Parameter)
    (hproject : IsVariationalEuclideanProjectionOn domain project)
    (hproject_nonexpansive : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 < stepSize)
    (hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ)))
    (hsensitivity_small : sensitivity < modulus /
      ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ))))
    (initial : Parameter) (hinitial : initial ∈ domain) : Prop :=
  ∃ stable ∈ domain, IsStableOn model domain stable ∧
    (∀ other ∈ domain, IsStableOn model domain other → other = stable) ∧
    Filter.Tendsto
      (fun iteration => (repeatedGradientDescentUpdate model gradient project stepSize)^[iteration] initial)
      Filter.atTop (nhds stable) ∧
    ∀ iteration,
      ‖(repeatedGradientDescentUpdate model gradient project stepSize)^[iteration] initial - stable‖ ≤
        (1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
          sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))) ^ iteration *
            ‖initial - stable‖

/--
Finite-PMF primal-transport specialization of Theorem 4.3.  The source's
arbitrary-distribution Wasserstein condition is represented here by an
explicit finite coupling certificate.
-/
def finiteOptimumStableDistanceSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {constant : NNReal} (hloss : IsDataLossLipschitz model constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) : Prop :=
  ‖optimal - stable‖ ≤ 2 * (constant : ℝ) * sensitivity / modulus

/--
Finite-PMF W₁ specialization of Theorem 4.3.  The finite-W₁ sensitivity
condition is used directly; arbitrary-measure semantics remain out of scope.
-/
def finiteWassersteinOptimumStableDistanceSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {constant : NNReal} (hloss : IsDataLossLipschitz model constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) : Prop :=
  ‖optimal - stable‖ ≤ 2 * (constant : ℝ) * sensitivity / modulus

/--
Finite-PMF primal-transport objective-value specialization of Corollary 5.1.
It applies to a supplied stable parameter; the source's RGD theorem that
produces such a point is tracked separately.
-/
def finiteStableObjectiveGapSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsDataLossLipschitz model dataConstant)
    (hparameterLoss : IsParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteTransportSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) : Prop :=
  performativeRisk model stable - performativeRisk model optimal ≤
    2 * (dataConstant : ℝ) * sensitivity *
      ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus

/--
Finite-PMF W₁ specialization of Corollary 5.1's conditional stable-point
objective bound.
-/
def finiteWassersteinStableObjectiveGapSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [Fintype Data] [DecidableEq Data] [MetricSpace Data]
    (model : FinitePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter)
    (hgradientAt : ∀ datum evaluated,
      HasGradientAt (fun parameter => model.loss datum parameter) (gradient datum evaluated) evaluated)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsPointwiseGradientStronglyConvex model gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : IsDataLossLipschitz model dataConstant)
    (hparameterLoss : IsParameterLossLipschitz model parameterConstant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : IsFiniteWassersteinSensitive model sensitivity)
    (optimal stable : Parameter)
    (hoptimal : IsPerformativelyOptimal model optimal) (hstable : IsStable model stable) : Prop :=
  performativeRisk model stable - performativeRisk model optimal ≤
    2 * (dataConstant : ℝ) * sensitivity *
      ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus

/--
Arbitrary-law compact-convex realization of Proposition 4.1. The model and
joint continuity of decoupled risk are restricted to the feasible domain.
Joint expected-risk continuity is the approved additional analytic premise; it
does not follow from pointwise loss continuity and Wasserstein sensitivity
alone without suitable control of the loss tails.
-/
def measureCompactConvexStablePointExistsSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [FiniteDimensional ℝ Parameter] [MeasurableSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (hcompact : IsCompact domain) (hne : domain.Nonempty) (hconvex : Convex ℝ domain)
    (hjoint : Continuous (fun point : domain × domain =>
      model.decoupledPerformativeRisk point.1 point.2))
    (hlossConvex : ∀ datum, ConvexOn ℝ domain (measureLossOnDomain model datum)) : Prop :=
  ∃ parameter : domain, model.IsPerformativelyStable parameter

/--
Candidate arbitrary-law W₁ statement of Theorem 4.3 on the source parameter
domain, pending source-fidelity review. The model, loss, integrability, and all
hypotheses are domain-relative; A1 and off-domain integrability are absent.
-/
def measureWassersteinOptimumStableDistanceSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [MeasurableSpace Data] [MetricSpace Data]
    {domain : Set Parameter} (model : MeasurePerformativeModelOn Parameter Data domain)
    (gradient : Data → domain → Parameter)
    (_hclosed : IsClosed domain) (_hconvex : Convex ℝ domain)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (_hstrong : model.IsPointwiseGradientStronglyConvex gradient modulus)
    {constant : NNReal} (_hloss : model.IsDataLossLipschitz constant)
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (_hsensitive : model.IsWassersteinSensitive sensitivity)
    (optimal stable : domain)
    (_hoptimal : model.IsPerformativelyOptimal optimal)
    (_hstable : model.IsPerformativelyStable stable) : Prop :=
  ‖(optimal : Parameter) - (stable : Parameter)‖ ≤
    2 * (constant : ℝ) * sensitivity / modulus

/--
General-measure strategic-classification statement of Corollary 5.1. The
induced law is the baseline population pushed forward through the selected
feature best response, preserving labels. The benchmark is a Stackelberg
equilibrium for that same response selection. All loss and gradient
conditions are restricted to the feasible parameter domain.
-/
def measureWassersteinStableObjectiveGapSpec
    {Parameter Feature Label : Type*}
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [FiniteDimensional ℝ Parameter]
    [MeasurableSpace Feature] [MeasurableSpace Label]
    [MetricSpace (Feature × Label)] {domain : Set Parameter}
    (profile : MeasureStrategicClassificationProfile Parameter Feature Label domain)
    (gradient : (Feature × Label) → domain → Parameter)
    (hclosed : IsClosed domain) (hconvex : Convex ℝ domain) {smoothness : NNReal}
    (hjoint :
      (∀ datum first second,
        ‖gradient datum first - gradient datum second‖ ≤
          (smoothness : ℝ) * dist (first : Parameter) (second : Parameter)) ∧
      (∀ first second parameter,
        ‖gradient first parameter - gradient second parameter‖ ≤
          (smoothness : ℝ) * dist first second))
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : profile.performativeModelOn.IsPointwiseGradientStronglyConvex gradient modulus)
    {dataConstant parameterConstant : NNReal}
    (hdataLoss : profile.performativeModelOn.IsDataLossLipschitz dataConstant)
    (hparameterLoss : ∀ datum, LipschitzWith parameterConstant (profile.loss datum))
    {sensitivity : ℝ} (hsensitivity : 0 ≤ sensitivity)
    (hsensitive : profile.performativeModelOn.IsWassersteinSensitive sensitivity)
    (update : domain → domain)
    (hrrm : ∀ deployed candidate,
      profile.performativeModelOn.decoupledPerformativeRisk deployed (update deployed) ≤
        profile.performativeModelOn.decoupledPerformativeRisk deployed candidate)
    (hfactor : sensitivity * (smoothness : ℝ) / modulus < 1)
    (initial optimal : domain)
    (hoptimal : profile.IsStackelbergEquilibrium optimal)
    : Prop :=
  ∃ stable : domain, profile.performativeModelOn.IsPerformativelyStable stable ∧
    (∀ other, profile.performativeModelOn.IsPerformativelyStable other → other = stable) ∧
    Filter.Tendsto (fun iteration => update^[iteration] initial) Filter.atTop (nhds stable) ∧
    (∀ iteration, dist (update^[iteration] initial) stable ≤
      (sensitivity * (smoothness : ℝ) / modulus) ^ iteration * dist initial stable) ∧
    profile.leaderRisk stable - profile.leaderRisk optimal ≤
      2 * (dataConstant : ℝ) * sensitivity *
        ((parameterConstant : ℝ) + (dataConstant : ℝ) * sensitivity) / modulus

/--
Corrected population part of Theorem 3.10's RERM branch.  In contrast to the
earlier whole-space convenience interface, its contraction is required only
on the source's feasible convex domain.  The associated proof endpoint makes
the additional Bochner-differentiation hypotheses explicit.
-/
def theorem310RERMConstrainedPopulationDataSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness : NNReal)
    (sensitivity modulus : ℝ) (domain : Set Parameter)
    (populationUpdate : Parameter → Parameter) (stable : Parameter) : Prop :=
  (0 ≤ sensitivity * (smoothness : ℝ) / modulus ∧
    sensitivity * (smoothness : ℝ) / modulus < 1 / 2) ∧
    populationUpdate stable = stable ∧
    (∀ first ∈ domain, ∀ second ∈ domain,
      dist (populationUpdate first) (populationUpdate second) ≤
        (sensitivity * (smoothness : ℝ) / modulus) * dist first second) ∧
    (∀ deployed ∈ domain,
      IsMeasureFrozenGradientFirstOrderOptimalOn model gradient domain deployed
        (populationUpdate deployed))

/--
Corrected population part of Theorem 3.10's RGD branch.  Its factor is the
source's A1/A2 interpolation factor; the proof endpoint makes the projection,
Bochner-differentiation, and stable-point hypotheses visible.
-/
def theorem310RGDPopulationDataSpec
    {Parameter Data : Type*} [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] [MeasurableSpace Data] [MetricSpace Data]
    (model : MeasurePerformativeModel Parameter Data)
    (gradient : Data → Parameter → Parameter) (smoothness : NNReal)
    (sensitivity modulus stepSize : ℝ) (project : Parameter → Parameter)
    (stable : Parameter) : Prop :=
  (0 ≤ 1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
    sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ))) ∧
    1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
      sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ))) < 1) ∧
    measureRepeatedGradientDescentUpdate model gradient project stepSize stable = stable ∧
    ∀ parameter,
      dist (measureRepeatedGradientDescentUpdate model gradient project stepSize parameter)
        (measureRepeatedGradientDescentUpdate model gradient project stepSize stable) ≤
        (1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
          sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))) *
          dist parameter stable

/--
A corrected Theorem 3.10 support lemma: compactness of the deployed domain
and continuity of the exponential moment functional produce one uniform bound
for every adaptive history-selected law.  These are visible additional
conditions; the source theorem states only pointwise moment finiteness.
-/
def theorem310CompactContinuousMomentEnvelopeSpec
    {Parameter : Type*} [TopologicalSpace Parameter]
    (dimension : ℕ)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (domain : Set Parameter) (alpha gamma : ℝ)
    (hcompact : IsCompact domain)
    (hmoment : ∀ parameter ∈ domain,
      Probability.HasExponentialRadialMoment (model.dataLaw parameter) alpha gamma)
    (hcontinuous : ContinuousOn (fun parameter =>
      ∫ datum : EuclideanSpace ℝ (Fin dimension),
        Real.exp (gamma * Real.rpow ‖datum‖ alpha) ∂(model.dataLaw parameter : Measure _))
        domain)
    (countSchedule : ℕ → ℕ)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace (fun round => Fin (countSchedule round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hdeployed : ∀ iteration history, deployedOfHistory iteration history ∈ domain) : Prop :=
  ∃ momentBound : ℝ, ∀ iteration history,
    Probability.HasBoundedExponentialRadialMoment
      (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound

/--
Corrected all-round RGD consequence of Theorem 3.10. The selected-shell
certificate event is measured on the one adaptive Ionescu--Tulcea trace; its
probability bound, the W₁ threshold, and all numerical recurrence conditions
are explicit rather than absorbed into a concentration certificate.
-/
def theorem310CorrectedRGDAllRoundTrajectorySpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    (dimension cutoff : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
    {smoothness : NNReal} (hjoint : IsJointlySmoothGradient gradient smoothness)
    (hsmoothness : smoothness ≠ 0)
    (project : Parameter → Parameter) (hproject : LipschitzWith 1 project)
    (stepSize : ℝ) (hstepSize : 0 ≤ stepSize)
    (hcountPositive : ∀ round,
      0 < pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : ∀ iteration history batch,
      deployedOfHistory (iteration + 1) (heterogeneousBatchTraceSnoc history batch) =
        measureSampledGradientDescentUpdate gradient project stepSize
          (hcountPositive iteration) batch (deployedOfHistory iteration history))
    (hintegrablePopulation : ∀ deployed,
      Integrable (fun datum => gradient datum deployed) (model.dataLaw deployed :
        Measure (EuclideanSpace ℝ (Fin dimension))))
    (hintegrableEmpirical : ∀ (iteration : ℕ)
      (history : HeterogeneousBatchTrace
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration)
      (batch : Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension)),
      Integrable (fun datum => gradient datum (deployedOfHistory iteration history))
        (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
          Measure (EuclideanSpace ℝ (Fin dimension))))
    (stable : Parameter) {contraction outerContraction wassersteinBound radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (hstable : measureRepeatedGradientDescentUpdate model gradient project stepSize stable = stable)
    (hcontract : ∀ parameter,
      dist (measureRepeatedGradientDescentUpdate model gradient project stepSize parameter)
        (measureRepeatedGradientDescentUpdate model gradient project stepSize stable) ≤
        contraction * dist parameter stable)
    (hbound_nonneg : 0 ≤ wassersteinBound)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound)
    (herror_outer : stepSize * (smoothness : ℝ) * wassersteinBound ≤
      (outerContraction - contraction) * radius)
    (herror_absorbed : stepSize * (smoothness : ℝ) * wassersteinBound ≤
      (1 - contraction) * radius)
    (initialDistance : ℝ)
    (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius)
    (hinitialDistance : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      dist (deployedOfHistory 0 history) stable ≤ initialDistance)
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
          dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
              dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration))
    : Prop :=
    ∃ entryIteration : ℕ,
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw model sampling
        (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
        deployedOfHistory hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ radius} ≥ 1 - p

/-- Source-facing carrier for the corrected RGD route of Theorem 3.10. -/
structure Theorem310CorrectedRGDAllRoundTrajectoryData
    (Parameter : Type*) [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter] where
  dimension : ℕ
  cutoff : ℕ
  hdimension : 2 < dimension
  eta : ℝ
  alpha : ℝ
  gamma : ℝ
  momentBound : ℝ
  deviation : ℝ
  scaledDeviation : ℝ
  tailBound : ℝ
  heta_pos : 0 < eta
  heta_le_one : eta ≤ 1
  halpha_pos : 0 < alpha
  hgamma_pos : 0 < gamma
  halpha_gap : 1 + eta < alpha
  hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta))
  hscaled_pos : 0 < scaledDeviation
  hscaled_le_one : scaledDeviation ≤ 1
  htailBound_pos : 0 < tailBound
  htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
    Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
      Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound
  p : ℝ
  headTolerance : ℝ
  hp : 0 < p
  hheadTolerance : 0 < headTolerance
  htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound
  model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension))
  sampling : MeasurePerformativeSamplingKernel model
  gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter
  smoothness : NNReal
  hjoint : IsJointlySmoothGradient gradient smoothness
  hsmoothness : smoothness ≠ 0
  sensitivity : ℝ
  modulus : ℝ
  hsensitivity_nonneg : 0 ≤ sensitivity
  hsensitive : IsMeasureWassersteinSensitive model sensitivity
  hmodulus_pos : 0 < modulus
  hmodulus_le : modulus ≤ (smoothness : ℝ)
  hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus
  domain : Set Parameter
  hconvex : Convex ℝ domain
  project : Parameter → Parameter
  hproject : LipschitzWith 1 project
  hprojectVariational : IsVariationalEuclideanProjectionOn domain project
  stepSize : ℝ
  hstepSize : 0 ≤ stepSize
  hstepSize_pos : 0 < stepSize
  hstepSize_le : stepSize ≤ 2 / (modulus + (smoothness : ℝ))
  hsensitivity_small : sensitivity < modulus /
    ((modulus + (smoothness : ℝ)) * (1 + (3 / 2) * stepSize * (smoothness : ℝ)))
  hintegrable : ∀ distributionParameter evaluatedParameter,
    Integrable (fun datum => gradient datum evaluatedParameter)
      (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension)))
  hloss_meas : ∀ distributionParameter evaluatedParameter,
    ∀ᶠ parameter in nhds evaluatedParameter,
      AEStronglyMeasurable (fun datum => model.loss datum parameter)
        (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension)))
  hpointwise : ∀ datum parameter,
    HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter
  hcountPositive : ∀ round,
    0 < pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round
  deployedOfHistory : ∀ iteration,
    HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter
  hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration)
  hempirical : ∀ iteration history batch,
    deployedOfHistory (iteration + 1) (heterogeneousBatchTraceSnoc history batch) =
      measureSampledGradientDescentUpdate gradient project stepSize
        (hcountPositive iteration) batch (deployedOfHistory iteration history)
  hintegrableEmpirical : ∀ (iteration : ℕ)
    (history : HeterogeneousBatchTrace
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) iteration)
    (batch : Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
      EuclideanSpace ℝ (Fin dimension)),
    Integrable (fun datum => gradient datum (deployedOfHistory iteration history))
      (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
        Measure (EuclideanSpace ℝ (Fin dimension)))
  stable : Parameter
  hstablePerformative : IsMeasurePerformativelyStableOn model domain stable
  contraction : ℝ
  outerContraction : ℝ
  wassersteinBound : ℝ
  radius : ℝ
  hcontraction_eq : contraction =
    1 - stepSize * (modulus * (smoothness : ℝ) / (modulus + (smoothness : ℝ)) -
      sensitivity * ((3 / 2) * stepSize * (smoothness : ℝ) ^ 2 + (smoothness : ℝ)))
  hcontraction_le_outer : contraction ≤ outerContraction
  hbound_nonneg : 0 ≤ wassersteinBound
  hbudget : Real.sqrt dimension * deviation +
    (2 * Real.sqrt dimension) *
      ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound
  herror_outer : stepSize * (smoothness : ℝ) * wassersteinBound ≤
    (outerContraction - contraction) * radius
  herror_absorbed : stepSize * (smoothness : ℝ) * wassersteinBound ≤ (1 - contraction) * radius
  initialDistance : ℝ
  houter_lt_one : outerContraction < 1
  hradius_pos : 0 < radius
  hinitialDistance : ∀ history : HeterogeneousBatchTrace
    (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
    (EuclideanSpace ℝ (Fin dimension)) 0,
    dist (deployedOfHistory 0 history) stable ≤ initialDistance
  hmoment : ∀ iteration history,
    Probability.HasBoundedExponentialRadialMoment
      (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound
  hevent : ∀ iteration, MeasurableSet
    (heterogeneousBatchTraceBadEventPair
      (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
        dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
        (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
        (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
        (measurePerformativeDeployedLaw model
          (fun round => Fin (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
          deployedOfHistory)) iteration)

/-- Compact review surface for the corrected all-round RGD consequence. -/
def theorem310CorrectedRGDAllRoundTrajectoryReviewSpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (data : Theorem310CorrectedRGDAllRoundTrajectoryData Parameter) : Prop :=
    ∃ entryIteration : ℕ,
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw data.model data.sampling
        (pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
          data.dimension data.cutoff data.eta data.alpha data.gamma data.momentBound data.tailBound
          data.scaledDeviation data.p data.headTolerance)
        data.deployedOfHistory data.hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (data.deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) data.stable ≤ data.radius} ≥
        1 - data.p

/--
The explicit supercritical RERM batch-count schedule used by the corrected
Theorem 3.10 interface.  Naming this schedule keeps the source-facing
trajectory proposition readable while retaining the exact compiled schedule as
a separately reviewable definition.
-/
noncomputable def theorem310CorrectedRERMCountSchedule
    (dimension cutoff : ℕ) (eta alpha gamma momentBound tailBound scaledDeviation p headTolerance : ℝ) :
    ℕ → ℕ :=
  pOneFournierGuillinTheorem310SupercriticalCappedConcreteCountSchedule
    dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance

/--
Source-facing carrier for the corrected RERM route of Theorem 3.10.  Its
labeled fields make every premise of the compiled all-round statement
independently reviewable, while the companion Spec below states the actual
adaptive trajectory conclusion.
-/
structure Theorem310CorrectedRERMAllRoundTrajectoryData
    (Parameter : Type*) [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter] where
  dimension : ℕ
  cutoff : ℕ
  hdimension : 2 < dimension
  eta : ℝ
  alpha : ℝ
  gamma : ℝ
  momentBound : ℝ
  deviation : ℝ
  scaledDeviation : ℝ
  tailBound : ℝ
  heta_pos : 0 < eta
  heta_le_one : eta ≤ 1
  halpha_pos : 0 < alpha
  hgamma_pos : 0 < gamma
  halpha_gap : 1 + eta < alpha
  hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta))
  hscaled_pos : 0 < scaledDeviation
  hscaled_le_one : scaledDeviation ≤ 1
  htailBound_pos : 0 < tailBound
  htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
    Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
      Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound
  p : ℝ
  headTolerance : ℝ
  hp : 0 < p
  hheadTolerance : 0 < headTolerance
  htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound
  model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension))
  sampling : MeasurePerformativeSamplingKernel model
  constant : NNReal
  hloss : IsMeasureDataLossLipschitz model constant
  hconstant : constant ≠ 0
  gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter
  smoothness : NNReal
  hjoint : IsJointlySmoothGradient gradient smoothness
  sensitivity : ℝ
  modulus : ℝ
  hmodulus : 0 < modulus
  hsensitivity_nonneg : 0 ≤ sensitivity
  hsmoothness_pos : 0 < (smoothness : ℝ)
  hsensitivity_lt : sensitivity < modulus / (2 * (smoothness : ℝ))
  hsensitive : IsMeasureWassersteinSensitive model sensitivity
  hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus
  hintegrable : ∀ distributionParameter evaluatedParameter,
    Integrable (fun datum => gradient datum evaluatedParameter)
      (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension)))
  domain : Set Parameter
  hconvex : Convex ℝ domain
  hcountPositive : ∀ round,
    0 < theorem310CorrectedRERMCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round
  deployedOfHistory : ∀ iteration,
    HeterogeneousBatchTrace
      (fun round => Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter
  hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration)
  hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
    (theorem310CorrectedRERMCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
    hcountPositive deployedOfHistory
  populationUpdate : Parameter → Parameter
  hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate
  hloss_meas : ∀ distributionParameter evaluatedParameter,
    ∀ᶠ parameter in nhds evaluatedParameter,
      AEStronglyMeasurable (fun datum => model.loss datum parameter)
        (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension)))
  hpointwise : ∀ datum parameter,
    HasGradientAt (fun theta => model.loss datum theta) (gradient datum parameter) parameter
  stable : Parameter
  hstablePerformative : IsMeasurePerformativelyStableOn model domain stable
  contraction : ℝ
  outerContraction : ℝ
  wassersteinBound : ℝ
  tolerance : ℝ
  radius : ℝ
  hcontraction_eq : contraction = sensitivity * (smoothness : ℝ) / modulus
  hcontraction_le_outer : contraction ≤ outerContraction
  htolerance_nonneg : 0 ≤ tolerance
  hinitial : ∀ history : HeterogeneousBatchTrace
    (fun round => Fin (theorem310CorrectedRERMCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
    (EuclideanSpace ℝ (Fin dimension)) 0,
    deployedOfHistory 0 history ∈ domain
  hbudget : Real.sqrt dimension * deviation +
    (2 * Real.sqrt dimension) *
      ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound
  herror_outer : Real.sqrt (4 * tolerance / modulus) ≤
    (outerContraction - contraction) * radius
  herror_absorbed : Real.sqrt (4 * tolerance / modulus) ≤ (1 - contraction) * radius
  initialDistance : ℝ
  houter_lt_one : outerContraction < 1
  hradius_pos : 0 < radius
  hinitialDistance : ∀ history : HeterogeneousBatchTrace
    (fun round => Fin (theorem310CorrectedRERMCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
    (EuclideanSpace ℝ (Fin dimension)) 0,
    dist (deployedOfHistory 0 history) stable ≤ initialDistance
  hmoment : ∀ iteration history,
    Probability.HasBoundedExponentialRadialMoment
      (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound
  hintegrableEmpiricalLoss : ∀ (iteration : ℕ)
    (history : HeterogeneousBatchTrace
      (fun round => Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) iteration)
    (batch : Fin (theorem310CorrectedRERMCountSchedule
      dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
      EuclideanSpace ℝ (Fin dimension))
    candidate, candidate ∈ domain →
    Integrable (fun datum => model.loss datum candidate)
      (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
        Measure (EuclideanSpace ℝ (Fin dimension)))
  hbound_nonneg : 0 ≤ wassersteinBound
  htolerance : (constant : ℝ) * wassersteinBound ≤ tolerance
  hevent : ∀ iteration, MeasurableSet
    (heterogeneousBatchTraceBadEventPair
      (fun round => Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
        dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
        (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
        (theorem310CorrectedRERMCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
        (measurePerformativeDeployedLaw model
          (fun round => Fin (theorem310CorrectedRERMCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
          deployedOfHistory)) iteration)

/--
Compact review surface for the corrected all-round RERM consequence of Theorem
3.10.  The data carrier above records the source and repair premises; this
definition retains the genuine selected-shell, after-entry probability claim.
-/
def theorem310CorrectedRERMAllRoundTrajectoryReviewSpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (data : Theorem310CorrectedRERMAllRoundTrajectoryData Parameter) : Prop :=
    ∃ entryIteration : ℕ,
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw data.model data.sampling
        (theorem310CorrectedRERMCountSchedule
          data.dimension data.cutoff data.eta data.alpha data.gamma data.momentBound data.tailBound
          data.scaledDeviation data.p data.headTolerance)
        data.deployedOfHistory data.hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (data.deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) data.stable ≤ data.radius} ≥
        1 - data.p

/--
Corrected all-round RERM consequence of Theorem 3.10.  This is the
empirical-minimization counterpart of
`theorem310CorrectedRGDAllRoundTrajectorySpec`: the actual adaptive sampling
trace, selected-certificate union event, W₁-to-uniform-risk bridge, and
two-phase numerical conditions are all exposed as assumptions.
-/
def theorem310CorrectedRERMAllRoundTrajectorySpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (dimension cutoff : ℕ) (hdimension : 2 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment : tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    {constant : NNReal} (hloss : IsMeasureDataLossLipschitz model constant)
    (hconstant : constant ≠ 0)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : IsMeasurePointwiseGradientStronglyConvex model gradient modulus)
    (hintegrable : ∀ distributionParameter evaluatedParameter,
      Integrable (fun datum => gradient datum evaluatedParameter)
        (model.dataLaw distributionParameter : Measure (EuclideanSpace ℝ (Fin dimension))))
    (domain : Set Parameter)
    (hcountPositive : ∀ round,
      0 < theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin (theorem310CorrectedRERMCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
      (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
      hcountPositive deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (hfirstOrder : ∀ deployed ∈ domain,
      IsMeasureFrozenGradientFirstOrderOptimalOn model gradient domain deployed
        (populationUpdate deployed))
    (stable : Parameter) {contraction outerContraction wassersteinBound tolerance radius : ℝ}
    (hcontraction_nonneg : 0 ≤ contraction)
    (hcontraction_le_outer : contraction ≤ outerContraction)
    (hstable : populationUpdate stable = stable)
    (hcontract : ∀ parameter ∈ domain,
      dist (populationUpdate parameter) (populationUpdate stable) ≤
        contraction * dist parameter stable)
    (htolerance_nonneg : 0 ≤ tolerance)
    (hinitial : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      deployedOfHistory 0 history ∈ domain)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤ wassersteinBound)
    (herror_outer : Real.sqrt (4 * tolerance / modulus) ≤
      (outerContraction - contraction) * radius)
    (herror_absorbed : Real.sqrt (4 * tolerance / modulus) ≤ (1 - contraction) * radius)
    (initialDistance : ℝ)
    (houter_lt_one : outerContraction < 1)
    (hradius_pos : 0 < radius)
    (hinitialDistance : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      dist (deployedOfHistory 0 history) stable ≤ initialDistance)
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hintegrableEmpiricalLoss : ∀ (iteration : ℕ)
      (history : HeterogeneousBatchTrace
        (fun round => Fin (theorem310CorrectedRERMCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration)
      (batch : Fin (theorem310CorrectedRERMCountSchedule
        dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension))
      candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos (hcountPositive iteration) batch :
          Measure (EuclideanSpace ℝ (Fin dimension))))
    (hbound_nonneg : 0 ≤ wassersteinBound)
    (htolerance : (constant : ℝ) * wassersteinBound ≤ tolerance)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin (theorem310CorrectedRERMCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanSelectedShellPartitionCertificateBadEvent
          dimension cutoff eta
          (pOneFournierGuillinTheorem310CappedDeviation
            dimension eta alpha gamma momentBound scaledDeviation)
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (theorem310CorrectedRERMCountSchedule
            dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin (theorem310CorrectedRERMCountSchedule
              dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration))
    : Prop :=
    ∃ entryIteration : ℕ,
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw model sampling
        (theorem310CorrectedRERMCountSchedule
          dimension cutoff eta alpha gamma momentBound tailBound scaledDeviation p headTolerance)
        deployedOfHistory hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ radius} ≥ 1 - p

/--
Source-facing carrier for the direct empirical-`W₁` RERM recovery route.

Unlike the historical selected-shell interface above, this route keeps the
statistical input in its native form: a measurable raw `W₁` bad event, its
finite-IID roundwise failure bound, and the threshold used by the empirical
minimizer recurrence.  In particular it does not add a loss-Lipschitz bridge,
gradient integrability, a pointwise first-order certificate, or a supplied
selected-shell concentration certificate.
-/
structure Theorem310RERMRawWassersteinSamplingRecoveryData
    (Parameter : Type*) [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter] where
  dimension : ℕ
  cutoff : ℕ
  alpha : ℝ
  gamma : ℝ
  momentBound : ℝ
  deviation : ℝ
  model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension))
  sampling : MeasurePerformativeSamplingKernel model
  gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter
  domain : Set Parameter
  hconvex : Convex ℝ domain
  smoothness : NNReal
  hgradient : ∀ datum parameter, parameter ∈ domain →
    HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter
  hdata : ∀ first second parameter, parameter ∈ domain →
    ‖gradient first parameter - gradient second parameter‖ ≤
      (smoothness : ℝ) * dist first second
  modulus : ℝ
  hmodulus : 0 < modulus
  hstrong : EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
    model.loss gradient domain modulus
  confidence : ℕ → ℝ
  countSchedule : ℕ → ℕ
  hcountPositive : ∀ iteration, 0 < countSchedule iteration
  deployedOfHistory : ∀ iteration,
    HeterogeneousBatchTrace (fun round => Fin (countSchedule round))
      (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter
  hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration)
  hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn
    model domain countSchedule hcountPositive deployedOfHistory
  populationUpdate : Parameter → Parameter
  hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate
  stable : Parameter
  hstable : IsMeasurePerformativelyStableOn model domain stable
  sensitivity : ℝ
  radius : ℝ
  p : ℝ
  hsensitivityNonneg : 0 ≤ sensitivity
  hsmoothnessPos : 0 < (smoothness : ℝ)
  hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ))
  hsensitive : IsMeasureWassersteinSensitiveOn model domain sensitivity
  hradius : 0 < radius
  hinitial : ∀ history : HeterogeneousBatchTrace
    (fun round => Fin (countSchedule round)) (EuclideanSpace ℝ (Fin dimension)) 0,
    deployedOfHistory 0 history ∈ domain
  hempiricalIntegrable : ∀ iteration
    (batch : Fin (countSchedule iteration) → EuclideanSpace ℝ (Fin dimension))
    candidate, candidate ∈ domain →
    Integrable (fun datum => model.loss datum candidate)
      (empiricalSampleProbabilityMeasureOfPos
        (hcountPositive iteration) batch : Measure (EuclideanSpace ℝ (Fin dimension)))
  entryIteration : ℕ
  hentry : ∀ trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
    (fun round => Fin (countSchedule round)) (EuclideanSpace ℝ (Fin dimension)) i,
    Real.log
        (dist (deployedOfHistory 0
          (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / radius) /
      (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
        (entryIteration : ℝ)
  pnonneg : 0 ≤ p
  hevent : ∀ iteration, MeasurableSet
    (heterogeneousBatchTraceBadEventPair (fun round => Fin (countSchedule round))
      (pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
        dimension cutoff alpha gamma momentBound deviation confidence countSchedule
        hcountPositive
        (measurePerformativeDeployedLaw model (fun round => Fin (countSchedule round))
          deployedOfHistory)) iteration)
  hfiniteIID : ∀ iteration history,
    (Probability.finiteIIDSampleLaw
      (measurePerformativeDeployedLaw model (fun round => Fin (countSchedule round))
        deployedOfHistory iteration history :
          Measure (EuclideanSpace ℝ (Fin dimension)))
      (countSchedule iteration)).real
      {batch |
        pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
          dimension cutoff alpha gamma momentBound deviation confidence countSchedule
          hcountPositive
          (measurePerformativeDeployedLaw model (fun round => Fin (countSchedule round))
            deployedOfHistory) iteration history batch} ≤ theorem310FailureBudget p iteration
  hthreshold : ∀ iteration history,
    pOneFournierGuillinAdaptiveEuclideanWassersteinOneThreshold
      dimension cutoff alpha gamma momentBound deviation confidence countSchedule
      (measurePerformativeDeployedLaw model (fun round => Fin (countSchedule round))
        deployedOfHistory) iteration history ≤ ENNReal.ofReal (sensitivity * radius)

/-- The direct raw-`W₁` sampling conclusion for the RERM branch of Theorem
3.10.  The after-entry conclusion is almost-sure in the adaptive sampling
trace up to the explicit total failure probability `p`. -/
def theorem310RERMRawWassersteinSamplingRecoverySpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter] [CompleteSpace Parameter]
    (data : Theorem310RERMRawWassersteinSamplingRecoveryData Parameter) : Prop :=
    (measurePerformativeHeterogeneousBatchTraceInfiniteLaw data.model data.sampling
      data.countSchedule data.deployedOfHistory data.hmeasurableDeployed).real
      {trace | ∀ iteration, data.entryIteration ≤ iteration →
        dist (data.deployedOfHistory iteration
          (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) data.stable ≤ data.radius} ≥
        1 - data.p

/-- Source-facing all-dimensional concrete-schedule version of the direct
empirical-`W₁` RERM recovery.  The selected-shell concentration construction
is used only to establish the raw `W₁` event budget and threshold internally;
the RERM recurrence itself has no loss-Lipschitz transport bridge. -/
private def theorem310RERMRawWassersteinAllDimensionalSamplingRecoveryImplementationSpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter]
    (dimension cutoff : ℕ) (hdimension : 0 < dimension)
    {eta alpha gamma momentBound deviation scaledDeviation tailBound : ℝ}
    (heta_pos : 0 < eta) (heta_le_one : eta ≤ 1)
    (halpha_pos : 0 < alpha) (hgamma_pos : 0 < gamma)
    (halpha_gap : 1 + eta < alpha)
    (hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta)))
    (hscaled_pos : 0 < scaledDeviation) (hscaled_le_one : scaledDeviation ≤ 1)
    (htailBound_pos : 0 < tailBound)
    (htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
      Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
        Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound)
    (p headTolerance : ℝ) (hp : 0 < p) (hheadTolerance : 0 < headTolerance)
    (htailBound_moment :
      tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound)
    (model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension)))
    (sampling : MeasurePerformativeSamplingKernel model)
    (gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter)
    (domain : Set Parameter) (hconvex : Convex ℝ domain) (smoothness : NNReal)
    (hgradient : ∀ datum parameter, parameter ∈ domain →
      HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter)
    (hdata : ∀ first second parameter, parameter ∈ domain →
      ‖gradient first parameter - gradient second parameter‖ ≤
        (smoothness : ℝ) * dist first second)
    {modulus : ℝ} (hmodulus : 0 < modulus)
    (hstrong : EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
      model.loss gradient domain modulus)
    (deployedOfHistory : ∀ iteration,
      HeterogeneousBatchTrace
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter)
    (hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration))
    (hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance)
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance)
      deployedOfHistory)
    (populationUpdate : Parameter → Parameter)
    (hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate)
    (stable : Parameter) (hstable : IsMeasurePerformativelyStableOn model domain stable)
    {sensitivity radius : ℝ} (hsensitivityNonneg : 0 ≤ sensitivity)
    (hsmoothnessPos : 0 < (smoothness : ℝ))
    (hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ)))
    (hsensitive : IsMeasureWassersteinSensitiveOn model domain sensitivity)
    (hradius : 0 < radius)
    (hinitial : ∀ history : HeterogeneousBatchTrace
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) 0,
      deployedOfHistory 0 history ∈ domain)
    (hempiricalIntegrable : ∀ iteration
      (batch : Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance iteration) →
        EuclideanSpace ℝ (Fin dimension))
      candidate, candidate ∈ domain →
      Integrable (fun datum => model.loss datum candidate)
        (empiricalSampleProbabilityMeasureOfPos
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance iteration)
          batch : Measure (EuclideanSpace ℝ (Fin dimension))))
    (entryIteration : ℕ)
    (hentry : ∀ trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) i,
      Real.log
          (dist (deployedOfHistory 0
            (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / radius) /
        (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
          (entryIteration : ℝ))
    (hmoment : ∀ iteration history,
      Probability.HasBoundedExponentialRadialMoment
        (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound)
    (hbudget : Real.sqrt dimension * deviation +
      (2 * Real.sqrt dimension) *
        ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤
          sensitivity * radius)
    (hevent : ∀ iteration, MeasurableSet
      (heterogeneousBatchTraceBadEventPair
        (fun round => Fin
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
        (pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
          dimension cutoff alpha gamma momentBound deviation
          (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
            alpha gamma tailBound deviation scaledDeviation p headTolerance)
          (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
            eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
          (measurePerformativeDeployedLaw model
            (fun round => Fin
              (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
                eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
            deployedOfHistory)) iteration)) : Prop :=
    ∃ gateScale : ℕ,
      scaledDeviation ≤ Probability.pOneFournierGuillinHeadGateRadius eta gateScale →
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw model sampling
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance)
        deployedOfHistory hmeasurableDeployed).real
        {trace | ∀ iteration, entryIteration ≤ iteration →
          dist (deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) stable ≤ radius} ≥
        1 - p

/--
Concrete source-facing input for the all-dimensional raw-`W₁` RERM branch of
Theorem 3.10.  This carrier deliberately fixes the selected-shell count and
confidence schedules in its field types.  In particular, it does not expose a
caller-supplied finite-IID failure certificate or transport threshold: the
lower all-dimensional concentration theorem derives both from the moment and
tail-envelope fields below.

Keeping the complete theorem input in one named constructor makes the public
Spec readable without hiding any premise: the semantic-prerequisite review
surface displays every constructor field together with the source theorem's
corrected premise bundle.
-/
structure Theorem310RERMRawWassersteinAllDimensionalSamplingRecoveryData
    (Parameter : Type*) [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter] where
  dimension : ℕ
  cutoff : ℕ
  hdimension : 0 < dimension
  eta : ℝ
  alpha : ℝ
  gamma : ℝ
  momentBound : ℝ
  deviation : ℝ
  scaledDeviation : ℝ
  tailBound : ℝ
  heta_pos : 0 < eta
  heta_le_one : eta ≤ 1
  halpha_pos : 0 < alpha
  hgamma_pos : 0 < gamma
  halpha_gap : 1 + eta < alpha
  hscaled : scaledDeviation = deviation * Real.rpow 2 (-(1 + eta))
  hscaled_pos : 0 < scaledDeviation
  hscaled_le_one : scaledDeviation ≤ 1
  htailBound_pos : 0 < tailBound
  htailEnvelope : ∀ law : ProbabilityMeasure (EuclideanSpace ℝ (Fin dimension)),
    Probability.HasBoundedExponentialRadialMoment law alpha gamma momentBound →
      Probability.fifthOrderExponentialRadialTailConstant law alpha gamma ≤ tailBound
  p : ℝ
  headTolerance : ℝ
  hp : 0 < p
  hheadTolerance : 0 < headTolerance
  htailBound_moment :
    tailBound = (Nat.factorial 5 : ℝ) * gamma⁻¹ ^ 5 * momentBound
  model : MeasurePerformativeModel Parameter (EuclideanSpace ℝ (Fin dimension))
  sampling : MeasurePerformativeSamplingKernel model
  gradient : EuclideanSpace ℝ (Fin dimension) → Parameter → Parameter
  domain : Set Parameter
  hconvex : Convex ℝ domain
  smoothness : NNReal
  hgradient : ∀ datum parameter, parameter ∈ domain →
    HasGradientWithinAt (model.loss datum) (gradient datum parameter) domain parameter
  hdata : ∀ first second parameter, parameter ∈ domain →
    ‖gradient first parameter - gradient second parameter‖ ≤
      (smoothness : ℝ) * dist first second
  modulus : ℝ
  hmodulus : 0 < modulus
  hstrong : EmpiricalMinimizerPerturbation.IsPointwiseGradientStronglyConvexOn
    model.loss gradient domain modulus
  deployedOfHistory : ∀ iteration,
    HeterogeneousBatchTrace
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
          eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (EuclideanSpace ℝ (Fin dimension)) iteration → Parameter
  hmeasurableDeployed : ∀ iteration, Measurable (deployedOfHistory iteration)
  hempirical : IsHeterogeneousMeasureRepeatedEmpiricalRiskMinimizationTrajectoryOn model domain
    (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
      alpha gamma tailBound deviation scaledDeviation p headTolerance)
    (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff eta
      alpha gamma tailBound deviation scaledDeviation p headTolerance)
    deployedOfHistory
  populationUpdate : Parameter → Parameter
  hpopulation : IsMeasureRepeatedRiskMinimizationOn model domain populationUpdate
  stable : Parameter
  hstable : IsMeasurePerformativelyStableOn model domain stable
  sensitivity : ℝ
  radius : ℝ
  hsensitivityNonneg : 0 ≤ sensitivity
  hsmoothnessPos : 0 < (smoothness : ℝ)
  hsensitivitySmall : sensitivity < modulus / (2 * (smoothness : ℝ))
  hsensitive : IsMeasureWassersteinSensitiveOn model domain sensitivity
  hradius : 0 < radius
  hinitial : ∀ history : HeterogeneousBatchTrace
    (fun round => Fin
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance round))
    (EuclideanSpace ℝ (Fin dimension)) 0,
    deployedOfHistory 0 history ∈ domain
  hempiricalIntegrable : ∀ iteration
    (batch : Fin
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance iteration) →
      EuclideanSpace ℝ (Fin dimension))
    candidate, candidate ∈ domain →
    Integrable (fun datum => model.loss datum candidate)
      (empiricalSampleProbabilityMeasureOfPos
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
          eta alpha gamma tailBound deviation scaledDeviation p headTolerance iteration)
        batch : Measure (EuclideanSpace ℝ (Fin dimension)))
  entryIteration : ℕ
  hentry : ∀ trace : (i : ℕ) → HeterogeneousBatchTraceCoordinate
    (fun round => Fin
      (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
        alpha gamma tailBound deviation scaledDeviation p headTolerance round))
    (EuclideanSpace ℝ (Fin dimension)) i,
    Real.log
        (dist (deployedOfHistory 0
          (heterogeneousBatchTraceOfInfiniteTrace 0 trace)) stable / radius) /
      (1 - 2 * (sensitivity * (smoothness : ℝ) / modulus)) ≤
        (entryIteration : ℝ)
  hmoment : ∀ iteration history,
    Probability.HasBoundedExponentialRadialMoment
      (model.dataLaw (deployedOfHistory iteration history)) alpha gamma momentBound
  hbudget : Real.sqrt dimension * deviation +
    (2 * Real.sqrt dimension) *
      ((32 / 15 : ℝ) * tailBound / (16 : ℝ) ^ cutoff) + headTolerance ≤
        sensitivity * radius
  hevent : ∀ iteration, MeasurableSet
    (heterogeneousBatchTraceBadEventPair
      (fun round => Fin
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
          eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
      (pOneFournierGuillinAdaptiveEuclideanWassersteinOneBadEvent
        dimension cutoff alpha gamma momentBound deviation
        (pOneFournierGuillinTheorem310SupercriticalConfidenceSchedule p)
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff eta
          alpha gamma tailBound deviation scaledDeviation p headTolerance)
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule_pos dimension cutoff
          eta alpha gamma tailBound deviation scaledDeviation p headTolerance)
        (measurePerformativeDeployedLaw model
          (fun round => Fin
            (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule dimension cutoff
              eta alpha gamma tailBound deviation scaledDeviation p headTolerance round))
          deployedOfHistory)) iteration)

/-- The source-facing all-dimensional concrete-schedule raw-`W₁` conclusion
for the RERM branch of Theorem 3.10. -/
def theorem310RERMRawWassersteinAllDimensionalSamplingRecoverySpec
    {Parameter : Type*} [MeasurableSpace Parameter]
    [NormedAddCommGroup Parameter] [InnerProductSpace ℝ Parameter]
    [CompleteSpace Parameter]
    (data : Theorem310RERMRawWassersteinAllDimensionalSamplingRecoveryData Parameter) : Prop :=
    ∃ gateScale : ℕ,
      data.scaledDeviation ≤ Probability.pOneFournierGuillinHeadGateRadius data.eta gateScale →
      (measurePerformativeHeterogeneousBatchTraceInfiniteLaw data.model data.sampling
        (pOneFournierGuillinTheorem310AllDimensionalConstantHeadCountSchedule data.dimension data.cutoff
          data.eta data.alpha data.gamma data.tailBound data.deviation data.scaledDeviation data.p
          data.headTolerance)
        data.deployedOfHistory data.hmeasurableDeployed).real
        {trace | ∀ iteration, data.entryIteration ≤ iteration →
          dist (data.deployedOfHistory iteration
            (heterogeneousBatchTraceOfInfiniteTrace iteration trace)) data.stable ≤ data.radius} ≥
        1 - data.p

end PZMH20PerformativePrediction
