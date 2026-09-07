import MendelsonWhang1990PriorityPricing.MainTheorems
import MendelsonWhang1990PriorityPricing.Assumptions

/-!
# Human-Facing Paper Interface: Optimal Incentive-Compatible Priority Pricing for the M/M/1 Queue

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
- Run raw-source-to-expanded-Spec statement matching plus recursive
  premise/conclusion provenance on the skeleton. The semantic comparison uses
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

- Theorem 1: a stationary interior optimum decentralizes through its marginal
  delay-externality price.
- Appendix (A-1): the stationary nonpreemptive-priority queue realizes the
  paper's mean queueing-time formula.
- Theorem 2: the optimal homogeneous priority price is strictly
  incentive-compatible at positive class flows.
- Theorem 3: the priority- and time-dependent schedule implements an optimal
  arrival vector and is strictly incentive-compatible.
- Theorem 4: the cheating penalty increases strictly away from the assigned
  priority.
-/

namespace MendelsonWhang1990PriorityPricing

noncomputable section

local instance paperInterfaceClassicalDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

/-- Assumption A2: every class value is differentiable, nondecreasing, and
concave on the source's nonnegative flow domain. -/
def sourceValueFunctionConditions
    {Class : Type*} [Fintype Class] (value : Class → ℝ → ℝ) : Prop :=
  (∀ i, DifferentiableOn ℝ (value i) (Set.Ici 0)) ∧
    (∀ i, MonotoneOn (value i) (Set.Ici 0)) ∧
      ∀ i, ConcaveOn ℝ (Set.Ici 0) (value i)

/-- Assumption A3: each class has a nonnegative delay cost per unit time. -/
def sourceDelayCostConditions
    {Class : Type*} [Fintype Class] (delayCost : Class → ℝ) : Prop :=
  ∀ i, 0 ≤ delayCost i

/-- Equation (5) under Assumption A5's atomistic individual decision rule:
the class's marginal value equals its direct price plus expected delay cost. -/
def individualDemandCondition
    {Class : Type*} [Fintype Class]
    (value : Class → ℝ → ℝ) (delayCost flow price : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (i : Class) (marginalValue : ℝ) : Prop :=
  HasDerivAt (value i) marginalValue (flow i) ∧
    marginalValue =
      price i + delayCost i * waitingTime i flow

/--
Appendix (A-1): the literal stationary marked-Poisson nonpreemptive-priority
queue has the displayed mean time-in-system formula.  Its source population
notation is made explicit through Little's-law population and the displayed
population-to-arrival-rate ratio.  Lower `Fin` indices are the source's higher
priorities.
-/
def appendixPriorityQueueingTimeSpec : Prop :=
  ∀ {n : ℕ} (arrivalRate meanService : Fin n → ℝ),
    ∀ (harrivalRate : ∀ j, 0 < arrivalRate j),
    (∀ j, 0 < meanService j) →
    (∑ j, arrivalRate j * meanService j < 1) →
    ∀ i,
      (∫ z, AppliedModelingLib.Queueing.stationaryPriorityClassTaggedResponseTime
          meanService i z
        ∂AppliedModelingLib.Queueing.stationaryPriorityClassTaggedPalmMeasure
          arrivalRate harrivalRate i) =
        prioritySojournTime arrivalRate meanService i ∧
      priorityPopulation arrivalRate meanService i =
        arrivalRate i * prioritySojournTime arrivalRate meanService i ∧
      priorityPopulation arrivalRate meanService i / arrivalRate i =
        prioritySojournTime arrivalRate meanService i

/--
Theorem 1 (pp. 873--874), in the source's general finite-class waiting-time
model.  The positive-flow interior condition used by the printed first-order
calculation is explicit.  Equation (5)'s individual demand equality and the
waiting-time derivatives in Equation (6) identify the optimal price.
-/
def theoremOneExternalityPricingSpec : Prop :=
  ∀ {Class : Type*} [Fintype Class]
    (value : Class → ℝ → ℝ) (delayCost flow price : Class → ℝ)
    (waitingTime : Class → (Class → ℝ) → ℝ)
    (i : Class) (marginalValue : ℝ) (partialWaiting : Class → ℝ),
    sourceValueFunctionConditions value →
    sourceDelayCostConditions delayCost →
    (∀ j, 0 ≤ flow j) →
    0 < flow i →
    IsMaxOn
      (netValue value delayCost waitingTime)
      (Set.Ici (fun _ => 0)) flow →
    individualDemandCondition value delayCost flow price waitingTime i
      marginalValue →
    (∀ j,
      HasDerivAt
        (fun t => waitingTime j (Function.update flow i t))
        (partialWaiting j) (flow i)) →
    price i = externalityPrice delayCost flow partialWaiting

/-- The expected private cost of a class `i` customer that declares priority
`selectedPriority` in the homogeneous-service model of Section 2. -/
noncomputable def homogeneousPriorityExpectedCost
    {n : ℕ} (arrivalRate delayCost : Fin n → ℝ)
    (i selectedPriority : Fin n) : ℝ :=
  homogeneousPriorityPrice arrivalRate delayCost selectedPriority +
    delayCost i * homogeneousPrioritySojournTime arrivalRate selectedPriority

/--
Theorem 2 (pp. 876--877).  At a stable optimal flow with positive class rates,
the priority-dependent price in Equation (10) makes the assigned priority the
strict best response for every class.  Positivity is the interior-class
condition used by the source's printed strict comparisons.
-/
def theoremTwoPriorityIncentiveCompatibilitySpec : Prop :=
  ∀ {n : ℕ} (arrivalRate delayCost : Fin n → ℝ),
    (∀ j, 0 < arrivalRate j) →
    (∑ j, arrivalRate j < 1) →
    (∀ {i k : Fin n}, i < k → delayCost k < delayCost i) →
    ∀ i selectedPriority : Fin n,
      selectedPriority ≠ i →
        homogeneousPriorityExpectedCost arrivalRate delayCost i i <
          homogeneousPriorityExpectedCost arrivalRate delayCost i selectedPriority

/-- The stationary expected PTD charge paid by a class-`customer` job that
declares `declaredPriority`, with its service requirement sampled from the
source's class-specific exponential service law. -/
noncomputable def stationaryClassTaggedExpectedPriorityTimeDependentPrice
    {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ)
    (harrivalRate : ∀ j, 0 < arrivalRate j)
    (customer declaredPriority : Fin n) : ℝ :=
  ∫ omega, heterogeneousPriorityTimeDependentPrice arrivalRate delayCost
      meanService declaredPriority
      (AppliedModelingLib.Queueing.stationaryPriorityClassTaggedWorkRequirement
        meanService customer omega)
    ∂(AppliedModelingLib.Probability.Palm.targetPassiveTaggedArrivalAtZero
      (AppliedModelingLib.Probability.Queueing.stationaryPoissonWorkTaggedArrivalAtZero
        (harrivalRate customer))
      (AppliedModelingLib.Queueing.multiclassStationaryPoissonWorkRestLaw
        arrivalRate harrivalRate customer)).Ptag

/--
Equations (12)--(15), together with the source's preceding joint
priority-and-arrival comparison: a PTD schedule is optimal and
incentive-compatible when the induced flow and its displayed priority order
jointly maximize stationary net value, each class's assigned priority is its
expected-total-cost minimizer, its marginal-user demand equality holds at that
assigned priority, and the assignment is truthful.  Theorem 3 later supplies
the particular PTD schedule in Equation (19).
-/
def priorityTimeDependentPricingOptimalAndIncentiveCompatibleAt
    {n : ℕ} (value : Fin n → ℝ → ℝ)
    (arrivalRate delayCost meanService marginalValue : Fin n → ℝ)
    (hmeanService : ∀ j, 0 < meanService j)
    (pricing : Fin n → ℝ → ℝ) (assignedPriority : Fin n → Fin n) : Prop :=
  IsMaxOn
      (fun pair : (Fin n → ℝ) × Equiv.Perm (Fin n) =>
        priorityScheduleNetValue value pair.1 delayCost meanService pair.2)
      (Set.prod (stablePriorityFlowDomain meanService) Set.univ)
      (arrivalRate, Equiv.refl _) ∧
    (∀ i,
      HasDerivAt (value i) (marginalValue i) (arrivalRate i) ∧
        marginalValue i = priorityTimeDependentExpectedCost
          arrivalRate delayCost meanService pricing i (assignedPriority i)) ∧
    (∀ i selectedPriority : Fin n,
      priorityTimeDependentExpectedCost
          arrivalRate delayCost meanService pricing i (assignedPriority i) ≤
        priorityTimeDependentExpectedCost
          arrivalRate delayCost meanService pricing i selectedPriority) ∧
    (∀ i, assignedPriority i = i)

/--
Theorem 3 (pp. 879--880). At the stable welfare-maximizing flow, the PTD
schedule is optimal and incentive-compatible in the source's Equations
(12)--(15) sense;
the proof identifies its expected charge with the Theorem 1 externality price
and establishes a strict penalty for every distinct reported priority.  The
separate PTD definition remains the source's weak-best-response definition.
Positive equilibrium flows are explicit in this theorem's author-approved
interior target because they are needed for its strict conclusion.
-/
def theoremThreePriorityTimeDependentPricingSpec : Prop :=
  ∀ {n : ℕ} (value : Fin n → ℝ → ℝ)
    (arrivalRate delayCost meanService marginalValue : Fin n → ℝ),
    sourceValueFunctionConditions value →
    sourceDelayCostConditions delayCost →
    (harrivalRate : ∀ j, 0 < arrivalRate j) →
    (hmeanService : ∀ j, 0 < meanService j) →
    (htotalStable : ∑ j, arrivalRate j * meanService j < 1) →
    (hpriority : ∀ {i k : Fin n}, i < k →
      meanService i * delayCost k < meanService k * delayCost i) →
    (∀ i, HasDerivAt (value i) (marginalValue i) (arrivalRate i)) →
    IsMaxOn
      (fun flow => netValue value delayCost
        (fun k rates => prioritySojournTime rates meanService k) flow)
      (stablePriorityFlowDomain meanService) arrivalRate →
    priorityTimeDependentPricingOptimalAndIncentiveCompatibleAt
      value arrivalRate delayCost meanService marginalValue hmeanService
      (heterogeneousPriorityTimeDependentPrice arrivalRate delayCost meanService) id ∧
    (∀ i,
      stationaryClassTaggedExpectedPriorityTimeDependentPrice
        arrivalRate delayCost meanService harrivalRate i i =
        externalityPrice delayCost arrivalRate
          (prioritySojournDerivative arrivalRate meanService i)) ∧
    (∀ i selectedPriority : Fin n,
      selectedPriority ≠ i →
      0 < priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService)
        i selectedPriority)

/--
Theorem 4 (pp. 880--881), stated as the two strict monotonicity chains around
the assigned priority, together with the zero assigned-priority penalty.
-/
def theoremFourCheatingPenaltyMonotonicitySpec : Prop :=
  ∀ {n : ℕ} (arrivalRate delayCost meanService : Fin n → ℝ),
    (∀ j, 0 < arrivalRate j) →
    (∀ j, 0 < meanService j) →
    (∑ j, arrivalRate j * meanService j < 1) →
    (∀ {i k : Fin n}, i < k →
      meanService i * delayCost k < meanService k * delayCost i) →
    (∀ i,
      priorityCheatingPenalty meanService delayCost
        (priorityQueueingTime arrivalRate meanService)
        (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i i = 0) ∧
    (∀ {i j k : Fin n}, i < j → j < k →
      priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j <
        priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k) ∧
    (∀ {i j k : Fin n}, k < i → j < k →
      priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i k <
        priorityCheatingPenalty meanService delayCost
          (priorityQueueingTime arrivalRate meanService)
          (priorityTimeLinearCoefficient arrivalRate delayCost meanService) i j)

end

end MendelsonWhang1990PriorityPricing
