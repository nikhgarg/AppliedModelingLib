import Naor1969QueueTolls.Definitions
import Naor1969QueueTolls.Assumptions

/-!
# Human-Facing Paper Interface: The Regulation of Queue Size by Levying Tolls

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

- `finiteCapacityStationaryLawSpec` -> `finiteCapacityStationaryLaw`: Finite-capacity stationary law, p. 17, section 2, equations (3)–(4).
- `stationaryPerformanceSpec` -> `stationaryPerformance`: Stationary generating-function and flow identities, p. 18, section 2, equations (5)–(11).
- `selfOptimizingThresholdSpec` -> `selfOptimizingThreshold`: Self-optimizing admission threshold, p. 19, section 3, equations (12)–(16).
- `socialOptimalThresholdSpec` -> `socialOptimalThreshold`: Globally optimal social admission threshold, pp. 19–20, section 4, equations (17)–(25).
- `socialAndRevenueThresholdOrderSpec` -> `socialAndRevenueThresholdOrder`: Ordering of social and revenue thresholds and the associated revenue-maximizing toll, pp. 20–23, sections 4 and 6, equations (17)–(25) and (27)–(31).
- `socialTollImplementsOptimalThresholdSpec` -> `socialTollImplementsOptimalThreshold`: Socially implementing toll interval, p. 22, section 5, equation (26).
-/

namespace Naor1969QueueTolls

/--
Finite-capacity stationary law

Paper statement: The queue observed under an admission threshold has the normalized truncated geometric stationary law solving the birth–death balance equations.

Source location: p. 17, section 2, equations (3)–(4)
Source status: independently reviewed against the pinned source text

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def finiteCapacityStationaryLawSpec : Prop :=
  ∀ (rho serviceRate : ℝ) (capacity : ℕ), 0 < rho → 0 < serviceRate →
    ∃ law : AppliedModelingLib.Probability.Queueing.GeneratorStationaryLaw
      (AppliedModelingLib.Probability.Queueing.finiteCapacityBirthDeathRates
        (rho * serviceRate) serviceRate capacity),
      law.mass = stationaryProbability rho capacity

/--
Stationary generating-function and flow identities

Paper statement: The finite stationary law has the displayed generating
function, and admitted arrivals, rejected arrivals, and completed services
obey the stationary flow equalities.

Source location: p. 18, section 2, equations (5)–(11)
Source status: independently reviewed against the pinned source text
-/
def stationaryPerformanceSpec : Prop :=
  ∀ (rho serviceRate z : ℝ) (capacity : ℕ), 0 < rho → 0 < serviceRate →
    expectedQueueSize rho capacity =
        AppliedModelingLib.Probability.Queueing.finiteCapacityWeightedGeometricSum rho capacity /
          AppliedModelingLib.Probability.Queueing.finiteCapacityGeometricNormalizer rho capacity ∧
      stationaryGeneratingFunction rho z capacity =
        AppliedModelingLib.Probability.Queueing.finiteCapacityGeometricNormalizer (rho * z) capacity /
          AppliedModelingLib.Probability.Queueing.finiteCapacityGeometricNormalizer rho capacity ∧
      divertedArrivalRate (rho * serviceRate) rho capacity +
          admittedArrivalRate (rho * serviceRate) rho capacity = rho * serviceRate ∧
      admittedArrivalRate (rho * serviceRate) rho capacity =
        serviceRate * busyFraction rho capacity ∧
      (0 < capacity →
        busyFraction rho capacity /
            (1 - stationaryProbability rho capacity capacity) = rho)

/--
Self-optimizing admission threshold

Paper statement: A customer joins exactly below the integer threshold obtained by flooring reward times service rate divided by waiting cost.

Source location: p. 19, section 3, equations (12)–(16)
Source status: independently reviewed against the pinned source text

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def selfOptimizingThresholdSpec : Prop :=
  ∀ (reward queueCost serviceRate : ℝ),
    0 < queueCost → 0 < serviceRate → 1 < serviceValue reward queueCost serviceRate →
      (∀ queueLength : ℕ,
        queueLength < Nat.floor (serviceValue reward queueCost serviceRate) →
          0 ≤ joiningGain reward queueCost serviceRate queueLength) ∧
      (∀ queueLength : ℕ,
        Nat.floor (serviceValue reward queueCost serviceRate) ≤ queueLength →
          joiningGain reward queueCost serviceRate queueLength < 0)

/--
Socially optimal admission threshold

Paper statement: Aggregate reward less queueing cost has a globally optimal
finite admission threshold, which can be selected no higher than the
self-interested threshold. The source's discrete-unimodality sentence is
retained separately as proof support rather than being presented as this
endpoint.

Source location: pp. 19–20, section 4, equations (17)–(25)
Source status: independently reviewed against the pinned source text
-/
def socialOptimalThresholdSpec : Prop :=
  ∀ (rho reward queueCost serviceRate : ℝ),
    0 < rho → 0 < queueCost → 0 < serviceRate →
      1 < serviceValue reward queueCost serviceRate →
      ∃ socialCapacity : ℕ,
        (∀ capacity : ℕ,
          socialWelfare (rho * serviceRate) reward queueCost rho capacity ≤
            socialWelfare (rho * serviceRate) reward queueCost rho socialCapacity) ∧
        socialCapacity ≤ Nat.floor (serviceValue reward queueCost serviceRate)

/--
Ordering of social and revenue thresholds and the associated toll

Paper statement: There are welfare- and toll-revenue-maximizing finite admission
thresholds, ordered no higher than the selfish threshold and with the revenue
threshold no higher than the welfare threshold. The revenue objective uses the
paper's corresponding toll `R - C n_r / μ`.

Source location: pp. 20–23, sections 4 and 6, equations (17)–(25) and (27)–(31)
Source status: independently reviewed against the pinned source text

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def socialAndRevenueThresholdOrderSpec : Prop :=
  ∀ (rho reward queueCost serviceRate : ℝ),
    0 < rho → 0 < queueCost → 0 < serviceRate →
      1 < serviceValue reward queueCost serviceRate →
      ∃ revenueCapacity socialCapacity : ℕ,
        (∀ capacity : ℕ,
          (capacity : ℝ) ≤ serviceValue reward queueCost serviceRate →
            tollRevenue (rho * serviceRate) reward queueCost serviceRate rho capacity ≤
              tollRevenue (rho * serviceRate) reward queueCost serviceRate rho revenueCapacity) ∧
        (∀ capacity : ℕ,
          socialWelfare (rho * serviceRate) reward queueCost rho capacity ≤
            socialWelfare (rho * serviceRate) reward queueCost rho socialCapacity) ∧
        revenueCapacity ≤ socialCapacity ∧
        socialCapacity ≤ Nat.floor (serviceValue reward queueCost serviceRate)

/--
Socially implementing toll interval

Paper statement: Any toll in the stated interval changes individual joining incentives so that a selected welfare-maximizing threshold is chosen.

Source location: p. 22, section 5, equation (26)
Source status: independently reviewed against the pinned source text

This transparent proposition is the exact statement-audit target. It is not
proof evidence. Its exact-type proof endpoint is declared in
`ProofInterface.lean`, so this human-facing file presents the full semantic
proposition once. At closeout, source atoms must be independently inventoried
from pinned source quote bytes and bound to this elaborated proposition rather
than inferred from identifiers.
-/
def socialTollImplementsOptimalThresholdSpec : Prop :=
  ∀ (rho reward queueCost serviceRate toll : ℝ) (socialCapacity : ℕ),
    0 < rho → 0 < queueCost → 0 < serviceRate →
      1 < serviceValue reward queueCost serviceRate →
      (∀ capacity : ℕ,
        socialWelfare (rho * serviceRate) reward queueCost rho capacity ≤
          socialWelfare (rho * serviceRate) reward queueCost rho socialCapacity) →
      joiningGain reward queueCost serviceRate socialCapacity < toll →
      toll ≤ thresholdFee reward queueCost serviceRate socialCapacity →
      (∀ capacity : ℕ,
        combinedIncomeAfterToll (rho * serviceRate) reward queueCost toll rho capacity ≤
          combinedIncomeAfterToll (rho * serviceRate) reward queueCost toll rho
            socialCapacity) ∧
      Nat.floor ((reward - toll) * serviceRate / queueCost) = socialCapacity

end Naor1969QueueTolls
