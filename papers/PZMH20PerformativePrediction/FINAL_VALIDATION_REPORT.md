# Final Validation Report: Performative Prediction

Updated: 2026-09-28

## 1. Human Verdict

The population convergence, stability, comparison, and counterexample results
are proved on the domains summarized below. The finite-sample RERM and REGD
results prove an all-round neighborhood guarantee under their stated inputs.

**Source-domain clarification:** Theorems 3.5 and 3.8, Proposition 4.1, and
Corollary 5.1 use the paper's closed convex finite-dimensional parameter domain
$\Theta$ directly. Theorems 3.5 and 3.8 and Corollary 5.1 retain their stated
conclusions; the Proposition 4.1 target explicitly records the on-domain joint
continuity of expected decoupled risk needed for its best-response argument.
See [the population results](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope),
[Proposition 4.1](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence),
and [Corollary 5.1](docs/SOURCE_CLARIFICATIONS.md#corollary-51-recovered-strategic-source-domain-scope).

**Theorem 3.10 source clarification:** Direct raw-Wasserstein RERM is proved
in every positive data dimension, with regime-specific schedules; REGD is
proved for data dimension greater than two. Both use an explicit uniform
adaptive moment condition, global regularity, and numerical conditions. The
source-style logarithmic entry threshold is proved, and the schedules state the
applicable dimension-specific sample counts. [Details](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity).

## 2. Closeout Status

- Completion status: formalized, for the selected statements described below.

All eleven selected results have completed independent source review and
strict closeout on the domains described below. The [closure receipt](FINAL_CLOSURE_RECEIPT.md)
identifies the accepted evidence. Human review annotations remain separate.

## 3. Source and Scope

Juan C. Perdomo, Tijana Zrnic, Celestine Mendler-Dünner, and Moritz Hardt,
*Performative Prediction*, ICML 2020 / PMLR 119. The
[official paper and supplement](https://proceedings.mlr.press/v119/perdomo20a.html)
are the primary source. The selected results are Theorems 3.5, 3.8 and 3.10,
Proposition 3.6(a--c), Propositions 4.1--4.2, Theorem 4.3 and Corollary 5.1.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 3.5 | **Exact under the source-domain reading.** The finite-dimensional closed convex domain $\Theta$ is the parameter carrier; the contraction, stability, convergence, and entry bound are unchanged. [Scope](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope). |
| Proposition 3.6(a) | **Exact.** The formal statement proves the stated smooth convex counterexample and its nonconvergent RRM orbit. |
| Proposition 3.6(b) | **Exact.** The formal statement proves the stated strongly convex nonsmooth counterexample and its two-cycle. |
| Proposition 3.6(c) | **Exact under clarified regularity conditions.** The compatible range $0<\gamma\leq\beta$ supports the stated counterexample for $\epsilon\geq\gamma/\beta$. [Compatibility](docs/SOURCE_CLARIFICATIONS.md#proposition-36c-compatible-regularity-constants). |
| Theorem 3.8 | **Exact under the source-domain reading.** Its projected expected-gradient update is defined on $\Theta$; $\gamma\leq\beta$ is derived on non-singleton domains and the singleton case is direct. [Scope](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope). |
| Theorem 3.10, RERM | **Exact with source clarifications.** The all-round guarantee holds in every positive data dimension with a regime-specific selected-shell schedule, a uniform adaptive moment envelope, numerical slack, and the source-style logarithmic entry threshold. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity). |
| Theorem 3.10, empirical gradient descent | **Exact with source clarifications.** The all-round guarantee holds for dimension > 2 with a uniform adaptive moment envelope, global regularity, numerical slack, and the source-style logarithmic entry threshold. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity). |
| Proposition 4.1 | **Exact with domain and continuity clarifications.** On a nonempty compact convex $\Theta$, on-domain joint continuity of expected decoupled risk and pointwise convexity yield a domain-stable parameter. [Condition](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence) and [model scope](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope). |
| Proposition 4.2 | **Exact with a source clarification.** Both Bernoulli endpoint bounds are imposed. [Valid example](docs/SOURCE_CLARIFICATIONS.md#proposition-42-valid-bernoulli-probabilities). |
| Theorem 4.3 | **Exact.** The formal statement proves the domain-relative optimum--stable distance bound. |
| Corollary 5.1 | **Exact under the source-domain reading.** The strategic domain profile and Stackelberg comparator yield the stated objective-gap bound. [Scope](docs/SOURCE_CLARIFICATIONS.md#corollary-51-recovered-strategic-source-domain-scope) and [model scope](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope). |

## 5. Clarified Conditions and Source Clarifications

There is no remaining formalization gap in the selected results. Theorem 3.10
uses two source clarifications: the formal statements make the uniform adaptive
moment condition explicit and state the applicable dimension-specific sample
schedules. Its direct RERM route covers every positive data dimension with
separate dimension-one, dimension-two, and supercritical schedules; its REGD
route is proved in data dimension greater than two. Both have the source-style
logarithmic entry threshold. Proposition 3.6(c) makes the compatible regularity
range explicit, Proposition 4.1 states the domain and continuity conditions,
and Proposition 4.2 states both Bernoulli endpoint bounds. The
[memo](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity)
gives the precise RERM/RGD distinction.

## 6. Additional Assumptions Beyond Paper

The [source-domain clarification](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-recovered-source-domain-scope)
records why the population results use the paper's finite-dimensional parameter
domain rather than an arbitrary ambient extension. Proposition 4.1's formalized
compact-domain target states the on-domain joint expected-risk continuity required
by its best-response proof. The finite-sample source clarifications are in
[Section 5](#5-remaining-boundaries-and-gaps). Counterexample parameter choices
in the memo are constructions, not population-model assumptions.

## 7. Proof-Strategy Deviations

Proposition 3.6(b) uses an explicit hinge penalty and interval to obtain the
stated two-cycle; the [construction](docs/SOURCE_CLARIFICATIONS.md#proposition-36ab-concrete-counterexample-models) retains the source assumptions and conclusion.

## 8. Proof Structure Worth Reusing

Population contraction and sampling perturbation can be analyzed separately:
a one-step perturbation smaller than the contraction's slack preserves a
neighborhood of the stable point. The memo states the required inequalities.

## 9. Generalizations, Conjectures, and Extensions

The documented source clarifications are identified in
[Section 5](#5-remaining-boundaries-and-gaps).

## 10. Source Clarifications and Exact Readings

The memo gives the
[compatible-constant clarification](docs/SOURCE_CLARIFICATIONS.md#proposition-36c-compatible-regularity-constants),
[explicit cycling witnesses](docs/SOURCE_CLARIFICATIONS.md#proposition-36ab-concrete-counterexample-models),
and [Bernoulli endpoint clarification](docs/SOURCE_CLARIFICATIONS.md#proposition-42-valid-bernoulli-probabilities).
Theorem 3.10's source clarifications are described in
[Section 5](#5-remaining-boundaries-and-gaps), and population analytic premises
to [Section 6](#6-additional-assumptions-beyond-paper).

## 11. Paper Issues or Caveats

The material source clarifications are stated in
[Section 5](#5-remaining-boundaries-and-gaps) and
[Section 6](#6-additional-assumptions-beyond-paper), with exact comparisons
linked from the result table.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes the performative model,
population contraction and stability statements, explicit counterexamples,
finite/measure bridges, and eleven selected result targets. [ProofInterface.lean](ProofInterface.lean)
contains their proof endpoints, including Theorem 3.10 trajectory results with
an internally capped batch schedule and a derived finite entry iteration.
Section 5 states the source clarifications and their proved formal statements.

## 13. Paper Assumption Provenance

The [source map](audit/paper_statement_map.json) routes performative
optimality/stability, update rules, sensitivity, and Theorem 3.10 carriers.
It now also routes Theorem 4.3's domain-relative model, risks, A2 witness, and
data-Lipschitz condition as reusable source predicates. The map exposes the
ambient model and global regularity predicates used by the population and
Theorem 3.10 targets, bringing the routed surface to six paper-local and fourteen
shared-library declarations. The current [paper](FINAL_CLOSURE_RECEIPT.md)
and [library](FINAL_CLOSURE_RECEIPT.md) ledgers record the independent
source comparisons. Sections 5–6 state the source clarifications and
mathematical conditions.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds contraction factors,
stability thresholds, counterexample losses, stable-point and optimum-distance
bounds, risk gaps, and finite-sample expressions. The
[clarification memo](docs/SOURCE_CLARIFICATIONS.md) records the compatible
constants, Bernoulli endpoint clarification, analytic domains, and Theorem 3.10
source clarifications.

## 15. Library Lift Pass

Reusable definitions include decoupled performative risk and Theorem 4.3's
domain-relative model, risks, solution concepts, A2 witness, data-Lipschitz
condition, and Wasserstein sensitivity. Population contraction, explicit
counterexamples, stable-point arguments, and clarified Theorem 3.10
trajectories remain paper-local.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) shows the paper's definitions and
named results. Its Theorem 3.10 nodes state the proved all-round containment
and the dimension-regime replacement for the printed common all-dimension
sample formula.
The updated PDF was compiled and visually inspected on 2026-09-27; labels,
node separation, and arrowheads are legible.

## 17. Validation Checks

The selected source comparisons, complete tracked-paper build, final independent
audit, and strict closeout pass, including Proposition 3.6(c)'s full threshold
and the domain-relative Theorem 4.3 statement. The
[closure receipt](FINAL_CLOSURE_RECEIPT.md) identifies the accepted evidence.

## 18. Paper Definitions Checked

The source map includes performative optimality and stability, repeated risk
minimization and gradient descent, distribution sensitivity, decoupled risk,
finite and measure-valued Wasserstein comparison, stable points, and the
RERM/RGD sampling trajectories. The domain-relative Theorem 4.3 definitions
now have current independent source comparisons.

## 19. Named Theorem Statements Checked

- Theorems 3.5 and 3.8; Proposition 3.6(a--c): population contraction and the
  three explicit failure examples on their documented domains.
- Theorem 3.10: RERM has an all-round neighborhood guarantee in every positive
  dimension with separate dimension-one, dimension-two, and supercritical
  schedules; REGD has the corresponding checked supercritical guarantee. Both
  retain the source-style logarithmic entry threshold. The printed common
  all-dimension sample formula is replaced by those proved schedules.
- Propositions 4.1--4.2, Theorem 4.3, and Corollary 5.1: stable-point existence,
  the Bernoulli concavity witness, distance, convergence, and risk-gap results.

## 20. Paper-Facing Statement Validator Ledger

The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md) records
seven ordinary matches and four matches to documented source-clarification
targets across the eleven selected results. Theorems 3.5 and 3.8 and Corollary
5.1 have fresh source-domain matches; Proposition 4.1 and the two Theorem 3.10
routes retain their documented source-clarification targets. The provenance is in
[source-proof fidelity](FINAL_CLOSURE_RECEIPT.md).

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) records the eleven selected
result targets and their governing definitions. The Theorem 3.10 statements
use the checked dimension-specific schedules; the population results are
recorded on the paper's source domain $\Theta$.
