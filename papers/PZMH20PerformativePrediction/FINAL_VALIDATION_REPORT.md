# Final Validation Report: Performative Prediction

Updated: 2026-09-06

## 1. Human Verdict

The population convergence, stability, comparison, and counterexample results
are proved on the domains summarized below. The finite-sample RERM and REGD
results prove an all-round neighborhood guarantee under their stated inputs.

**Formalization gap:** Theorems 3.5 and 3.8 assume A1, A2, Wasserstein sensitivity,
and analytic regularity over the ambient parameter space while stating their
conclusions on the source domain. Proposition 4.1 assumes global expected-risk
continuity, and Corollary 5.1 takes the parameter domain to be the entire
ambient space. Necessity of these stronger current-proof conditions is
unresolved. See the comparisons for
[Theorems 3.5 and 3.8](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-population-scope),
[Proposition 4.1](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence),
and [Corollary 5.1](docs/SOURCE_CLARIFICATIONS.md#corollary-51-whole-space-population-scope).

**Formalization gap:** Theorem 3.10 is proved for data dimension greater than two
with uniform moments, global regularity, and explicit numerical conditions;
the printed all-dimension sample budget and logarithmic burn-in bound remain
unproved. [Details](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity).

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
| Theorem 3.5 | **Formalization gap:** A1, A2, Wasserstein sensitivity, expected-loss/gradient integrability, measurability and differentiation hold for every ambient parameter; the conclusion remains on $\Theta$. Necessity is unresolved. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-population-scope). |
| Proposition 3.6(a) | **Exact.** |
| Proposition 3.6(b) | **Exact.** |
| Proposition 3.6(c) | **Source clarification:** $0<\gamma\leq\beta$ is required by the regularity constants; the counterexample covers $\epsilon\geq\gamma/\beta$. [Compatibility](docs/SOURCE_CLARIFICATIONS.md#proposition-36c-compatible-regularity-constants). |
| Theorem 3.8 | **Formalization gap:** A1, A2, Wasserstein sensitivity, expected-loss/gradient integrability, measurability and differentiation hold for every ambient parameter; the conclusion remains on $\Theta$. Necessity is unresolved. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-population-scope). |
| Theorem 3.10, RERM | **Formalization gap:** all-round probability guarantee for dimension > 2, with uniform moments, global regularity, data-Lipschitz loss and numerical slack (necessity unresolved); printed sample/burn-in bounds remain unproved. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity). |
| Theorem 3.10, empirical gradient descent | **Formalization gap:** all-round guarantee for dimension > 2, with uniform moments, global regularity and numerical slack (necessity unresolved); printed sample/burn-in bounds remain unproved. [Conditions](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity). |
| Proposition 4.1 | **Formalization gap:** expected-loss integrability and joint continuity of expected decoupled risk hold on the full ambient parameter product; stability remains domain-relative. Necessity of the global scope is unresolved. [Condition](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence). |
| Proposition 4.2 | **Exact claim; witness domain clarified:** both Bernoulli endpoint bounds are imposed. [Valid example](docs/SOURCE_CLARIFICATIONS.md#proposition-42-valid-bernoulli-probabilities). |
| Theorem 4.3 | **Exact.** |
| Corollary 5.1 | **Formalization gap:** whole-space RRM and optimum assumptions; the strategic-classification Stackelberg interpretation is not formalized. [Conditions](docs/SOURCE_CLARIFICATIONS.md#corollary-51-whole-space-population-scope). |

## 5. Remaining Boundaries and Gaps

Theorems 3.5 and 3.8 retain ambient-global regularity while proving domain-level
conclusions; Proposition 4.1 retains global expected-risk continuity; and
Corollary 5.1 is a whole-space result. The exact differences are in the
[Theorems 3.5 and 3.8](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-population-scope),
[Proposition 4.1](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence),
and [Corollary 5.1](docs/SOURCE_CLARIFICATIONS.md#corollary-51-whole-space-population-scope)
memo entries.
Their necessity under the source hypotheses is unresolved.

Theorem 3.10 proves the all-round probability guarantee with an explicit
sufficient batch schedule for data dimension greater than two. The printed
all-dimension sample-count and logarithmic burn-in bounds remain unproved.
The current proof uses a common moment bound across adaptive histories and
global regularity and numerical conditions; their necessity under the full
source hypotheses is unresolved. The [memo](docs/SOURCE_CLARIFICATIONS.md#theorem-310-dimension-and-adaptive-uniformity)
gives the exact differences.

## 6. Additional Assumptions Beyond Paper

The [population comparison](docs/SOURCE_CLARIFICATIONS.md#theorems-35-and-38-population-scope)
states the ambient-global regularity and analytic premises for Theorems 3.5
and 3.8, and the [Corollary 5.1 comparison](docs/SOURCE_CLARIFICATIONS.md#corollary-51-whole-space-population-scope)
states its whole-space domain. The
[stable-point existence argument](docs/SOURCE_CLARIFICATIONS.md#proposition-41-stable-point-existence)
uses expected-loss integrability and joint continuity of expected risk over the
full ambient parameter product for Proposition 4.1. Necessity of these exact
premises has not been established. The finite-sample conditions are in
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

The remaining source-coverage work is identified in
[Section 5](#5-remaining-boundaries-and-gaps).

## 10. Source Clarifications and Exact Readings

The memo gives the
[compatible-constant correction](docs/SOURCE_CLARIFICATIONS.md#proposition-36c-compatible-regularity-constants),
[explicit cycling witnesses](docs/SOURCE_CLARIFICATIONS.md#proposition-36ab-concrete-counterexample-models),
and [Bernoulli endpoint correction](docs/SOURCE_CLARIFICATIONS.md#proposition-42-valid-bernoulli-probabilities).
Theorem 3.10's substantive formalization boundary belongs to
[Section 5](#5-remaining-boundaries-and-gaps), and population analytic premises
to [Section 6](#6-additional-assumptions-beyond-paper).

## 11. Paper Issues or Caveats

The material qualifications are stated in
[Section 5](#5-remaining-boundaries-and-gaps) and
[Section 6](#6-additional-assumptions-beyond-paper), with exact comparisons
linked from the result table.

## 12. Detailed Formalization Evidence

[PaperInterface.lean](PaperInterface.lean) exposes the performative model,
population contraction and stability statements, explicit counterexamples,
finite/measure bridges, and eleven selected result targets. [ProofInterface.lean](ProofInterface.lean)
contains their proof endpoints, including Theorem 3.10 trajectory results with
an internally capped batch schedule and a derived finite entry iteration.
Section 5 states the remaining source-coverage boundaries.

## 13. Paper Assumption Provenance

The [source map](audit/paper_statement_map.json) routes performative
optimality/stability, update rules, sensitivity, and Theorem 3.10 carriers.
It now also routes Theorem 4.3's domain-relative model, risks, A2 witness, and
data-Lipschitz condition as reusable source predicates. The map exposes the
ambient model and global regularity predicates used by the population and
Theorem 3.10 targets, bringing the routed surface to six paper-local and fourteen
shared-library declarations. The current [paper](FINAL_CLOSURE_RECEIPT.md)
and [library](FINAL_CLOSURE_RECEIPT.md) ledgers record the prior
independent source comparisons; Section 20 identifies the changed rows that
require refreshed review. Sections 5–6 state the mathematical boundaries.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds contraction factors,
stability thresholds, counterexample losses, stable-point and optimum-distance
bounds, risk gaps, and finite-sample expressions. The
[clarification memo](docs/SOURCE_CLARIFICATIONS.md) records the compatible
constants, Bernoulli endpoint correction, analytic domains, and Theorem 3.10
boundary.

## 15. Library Lift Pass

Reusable definitions include decoupled performative risk and Theorem 4.3's
domain-relative model, risks, solution concepts, A2 witness, data-Lipschitz
condition, and Wasserstein sensitivity. Population contraction, explicit
counterexamples, stable-point arguments, and corrected Theorem 3.10
trajectories remain paper-local.

## 16. DAG Audit

The [dependency DAG](docs/DependencyDAG.pdf) shows the paper's definitions and
named results. Its Theorem 3.10 nodes state the proved all-round containment
for dimension greater than two and the unproved printed sample/burn-in bounds.
The updated PDF was compiled and visually inspected on 2026-09-06; labels,
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
  three explicit failure examples on their corrected domains.
- Theorem 3.10: RERM and REGD all-round neighborhood guarantees for dimension
  greater than two, with the stated uniform-moment, analytic and numerical
  inputs. The printed all-dimension sample and burn-in bounds remain unproved.
- Propositions 4.1--4.2, Theorem 4.3, and Corollary 5.1: stable-point existence,
  the corrected concavity witness, distance, convergence, and risk-gap results.

## 20. Paper-Facing Statement Validator Ledger

The existing [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
records four ordinary matches and seven matches to documented formalized
targets across eleven results. The changed target descriptions for Theorems
3.5 and 3.8, Proposition 4.1, and Corollary 5.1 require refreshed comparison.
Theorem 4.3 and Proposition 4.2 remain ordinary source matches; the two
Theorem 3.10 results retain the limited targets described in Section 5.
Correction and boundary provenance is in
[source-proof fidelity](FINAL_CLOSURE_RECEIPT.md).

## 21. Source-Coverage Audit Ledger

[The source map](audit/paper_statement_map.json) records the eleven selected
result targets and their governing definitions. This selected coverage does
not establish the printed Theorem 3.10 quantitative bounds, derive the
population results' ambient-global premises from the source-domain conditions,
or turn Corollary 5.1's whole-space target into a result on arbitrary closed
convex $\Theta$.
