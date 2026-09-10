# Final Validation Report: Monoculture in Matching Markets
Updated: 2026-09-08

## 1. Human Verdict

The named matching and welfare results are formalized on the domains below.

## 2. Closeout Status

- Completion status: formalized.
- The selected results have completed independent source review and strict closeout; see the [closure receipt](FINAL_CLOSURE_RECEIPT.md).
- Human review status: 0/13 reviewer annotations recorded.

## 3. Source and Scope

The source is [*Monoculture in Matching Markets*](https://arxiv.org/abs/2312.09841)
by Kenny Peng and Nikhil Garg. The formalized scope includes:

- the continuum applicant, score, ranking, mono/polyculture noise, matching,
  stability, demand, and clearing model;
- the source definitions of maximum order statistics and
  maximum-concentrating noise;
- the appendix support observations, cutoff-lattice proposition, and the
  paper's three-part threshold lemma;
- the Supply and Demand and Equal Cutoffs lemmas, probability formula, and
  Corollary 4;
- Theorems 1--3, including the differential-application-access model; and
- the finite no-profitable-deviation result for the prescribed application
  set.

Simulations, computational experiments, figures, and narrative conclusion
prose are outside the mathematical formalization scope.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Supply and Demand | **Exact.** |
| Clearing-cutoff lattice | **Exact.** |
| Equal Cutoffs | **Additional assumptions:** zero score-boundary mass and ranking/noise regularity; necessity for the full claim is unknown. [Conditions](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Probability formula | **Source clarification:** atomless noise identifies strict-tail formulas with literal weak matching events. [Identity](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Proposition 7 | **Exact.** |
| [Proposition 8](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments) | **Domain clarified:** positive mass is asserted for nonempty open intervals meeting the support interior. |
| Corollary 4 | **Current proof conditions:** zero score-boundary mass and nondegenerate noise for strict cutoff comparison. Necessity is unknown. [Conditions](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Theorem 1 | **Source clarification:** integrable values and atomless value/noise laws; the conclusions use literal weak matching events. [Welfare conditions](docs/SOURCE_CLARIFICATIONS.md#welfare-and-the-application-game); [cutoff regularity](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Theorem 2 | **Source clarification:** atomless noise identifies the literal matching events; eventual advantage also uses atomless values. The positive-mass comparison regions are retained. [Conditions](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Theorem 3 | **Source clarification:** atomless values connect market clearing to equality with unrestricted monoculture matching probability. Polyculture probability increases with applications, strictly on the [support interior](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Differential-access Equal Cutoffs | **Current proof conditions:** score-level nullity for unique equal cutoffs. [Conditions](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments). |
| Finite application game | **Restricted scope:** ex-ante, same-cardinality deviations; broader deviations remain unproved, and necessity of the restriction is unknown. [Game](docs/SOURCE_CLARIFICATIONS.md#welfare-and-the-application-game). |
| Lemma 10 | **Exact.** |
| Uniform maximum example | **Typos fixed:** mean and Chebyshev denominator. [Formulas](docs/SOURCE_CLARIFICATIONS.md#uniform-maximum-concentration-example). |

## 5. Remaining Boundaries and Gaps

The application-game scope is stated in [Section 6](#6-additional-assumptions-beyond-paper).

## 6. Additional Assumptions Beyond Paper

- [Equal Cutoffs and Corollary 4](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments): zero score-boundary mass; Corollary 4 also uses nondegenerate noise.
- [Application incentives](docs/SOURCE_CLARIFICATIONS.md#welfare-and-the-application-game): restrict the application game to ex-ante, same-cardinality deviations with the stated utility and success laws.

## 7. Proof-Strategy Deviations

None.

## 8. Proof Tricks Worth Reusing

- State strict interval facts on the interior of a distributional support; the
  same theorem then covers bounded and unbounded supports.
- Keep weak market clearing separate from the zero-boundary-mass lemma until a
  strict probability formula is actually needed.
- Use relabeling closure of the clearing-cutoff lattice to obtain a common
  coordinate before proving scalar uniqueness.
- Separate the finite application combinatorics from the probabilistic success
  law, so the no-deviation comparison becomes a reusable monotonicity argument.

## 9. Generalizations, Conjectures, and Extensions

The support-interior and strict-tail lemmas should transfer to other continuum
cutoff models. The finite application-set comparison may also admit a reusable
library abstraction once a second paper needs the same ex-ante success-law
semantics.

## 10. Source Clarifications and Exact Readings

The Probability Formula and Theorems 1--2 use atomless noise to identify strict
tails with weak matching events. Theorem 1 also uses integrable, atomless
values; Theorem 2's eventual-advantage branch and Theorem 3's market-clearing
bridge use atomless values. Necessity of the complete regularity package for the source conclusions is unresolved. [Clarification](docs/SOURCE_CLARIFICATIONS.md#welfare-and-the-application-game).

The appendix's unqualified interval and endpoint readings become open-interior
statements; singleton intervals and endpoint atoms explain why. The
[memo](docs/SOURCE_CLARIFICATIONS.md#cutoff-probabilities-and-support-arguments)
gives the exact probability identities and examples.

## 11. Paper Issues or Caveats

The qualifications are stated with their results above; necessity of every current-proof condition is not established.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) presents each of the 13 selected
results once as a transparent target, paired with a checked endpoint in
[ProofInterface.lean](ProofInterface.lean). The literal continuum market,
mono- and polyculture laws, rankings, scores, demand, matching, stability,
market clearing, cutoff characterization, and analytic theorem chain are
implemented in the paper-local files cited by that interface. Supply and Demand
and the coordinatewise cutoff lattice cover arbitrary applicant-type probability
laws under the cited Azevedo--Leshno market assumptions. Lemma 10 derives cutoff
convergence from weak market clearing, including atoms. Theorem 3 derives
equality of the baseline and differential monoculture cutoffs from clearing
at the same supply, then compares the literal iid choice-event probabilities.
With $k$ applications its polyculture probability is $1-\Pr[X<P-v]^k$, including boundary atoms.

## 13. Paper Assumption Provenance

[Assumptions.lean](Assumptions.lean) selects no standalone paper-facing
assumption. Source conditions and clarifications appear directly in the
expanded targets. The governing Azevedo--Leshno assumptions are separately
source-pinned. The current [paper prerequisite ledger](FINAL_CLOSURE_RECEIPT.md)
records the independent review of all 37 routed model and definition declarations.

## 14. Displayed Formula Provenance

The [statement map](audit/paper_statement_map.json) routes the market,
maximum-order-statistic, cutoff, probability, and differential-access
definitions and formulas. The corrected-target distinctions are explained in
the [source clarification memo](docs/SOURCE_CLARIFICATIONS.md) and recorded in
the [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md).

## 15. Library Lift Pass

The formalization reuses the Azevedo--Leshno cutoff-market layer and general
probability infrastructure. PG23-specific value and noise laws,
differential-access semantics, and theorem routes remain paper-local. No
paper-numbered conclusion is exported as a reusable assumption or certificate.

## 16. DAG Audit

[DependencyDAG.tex](docs/DependencyDAG.tex) presents the source-facing
definitions and results in dependency order, including the Appendix
observations, Theorems 1--3, differential-access Equal Cutoffs, and the finite
no-deviation result. The [PDF](docs/DependencyDAG.pdf) was compiled and visually
inspected on 2026-09-06: the coordinatewise lattice conclusion and Theorem 3
matching probabilities are legible, with separated nodes and visible arrowheads.

## 17. Validation Checks

The selected source comparisons, complete tracked-paper build, final independent
audit, and strict closeout pass. This includes coordinatewise lattice closure,
Theorem 3's choice-event comparisons, and the literal weak-event Theorems 1--2.
The [closure receipt](FINAL_CLOSURE_RECEIPT.md) identifies the accepted evidence.

## 18. Paper Definitions Checked

The checked source definitions are the concrete type-law market, maximum order
statistics, and maximum concentration, together with the paper-local cutoff,
ranking, matching, stability, market-clearing, and differential-access
objects used in the expanded targets. Exact routes appear in the
[statement map](audit/paper_statement_map.json).

## 19. Named Theorem Statements Checked

The 13 selected results comprise two Appendix support observations, the
cutoff-lattice proposition, the three-part threshold lemma, Supply and Demand,
Equal Cutoffs, the probability formula, Corollary 4, Theorems 1--3,
differential-access Equal Cutoffs, and the finite application-game proposition.
The maximum-order-statistic and maximum-concentration definitions remain
reviewed model inputs.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records 13 result comparisons. The two changed Theorem 1--2 endpoints require
successor review. The [source clarification memo](docs/SOURCE_CLARIFICATIONS.md)
explains the qualified targets.

## 21. Source-Coverage Audit Ledger

The current [statement map](audit/paper_statement_map.json) records 13 selected
results and 15 governing prerequisite items routed to 37 Lean declarations.
It distinguishes result claims from source definitions and cited model assumptions.
