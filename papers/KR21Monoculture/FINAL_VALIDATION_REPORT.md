# Final Validation Report: KR21 Monoculture
Updated: 2026-09-07

## 1. Human Verdict

The population ranking and welfare results are checked with the source
clarifications below, including the source's standing strict candidate-value
order in Theorem 1.

## 2. Closeout Status

- Completion status: `formalized`.
- Scope: Definitions 1--4, Theorems 1--9, and Lemmas 1--8, with Appendix C
  Lemma 1 represented by its correct weak-global and strict-overlap forms; the selected
  unnumbered Appendix B and Plackett–Luce claims are listed in Section 4.
- Human review: not yet recorded.

## 3. Source and Scope

The source is [arXiv:2101.05853](https://arxiv.org/abs/2101.05853).
The selected surface includes its named definitions, Theorems 1--9, and lemmas,
plus the selected Appendix B and Plackett–Luce claims in Section 4.
Computational illustrations, numerical and figure observations, and the
source's stated open observation are not claimed as proved theorems. The
[scope note](docs/SOURCE_CLARIFICATIONS.md#representation-boundaries) also
separates the finite-support and simulation remarks from the checked results.

## 4. Researcher Summary of Checked Results

| Result | Comparison with source |
| --- | --- |
| Theorem 1 | **Exact.** The strict full-set comparison is evaluated on the source's standing strictly ordered candidate-value domain. [Source reading](docs/SOURCE_CLARIFICATIONS.md#theorem-1-strict-improvement-domain). |
| Theorem 2 | **Formalized under explicit outer-$D$ regularity:** the candidate-value law has ordered support, finite first moments, measurable ranking probabilities, and well-defined conditional and payoff expectations. [Conditions](docs/SOURCE_CLARIFICATIONS.md#representation-boundaries). |
| Theorem 3 | **Corrected domain:** at least three candidates; with two, total hiring welfare is constant. [Example](docs/SOURCE_CLARIFICATIONS.md#strictness-and-candidate-domain-readings). |
| Theorem 4 | **Exact.** |
| Theorem 5 | **Density condition clarified:** global absolute continuity and an integrable derivative suffice; smooth full support alone does not. Necessity of this sufficient condition is unresolved. [Counterexample and condition](docs/SOURCE_CLARIFICATIONS.md#strictness-and-candidate-domain-readings). |
| Theorem 6 | **Exact.** |
| Theorem 7 (Laplace) | **Exact.** |
| Theorem 8 (Gaussian) | **Exact.** |
| Theorem 9 | **Exact.** |
| Appendix C Lemma 1 | **Changed inequality:** weak globally, strict on overlap. [Exact comparison](docs/LAPLACIAN_SOURCE_CLARIFICATION.md#appendix-c-lemma-1-laplacian-clarification). |
| Lemma 4 | **Strictness clarified:** a strict likelihood-ratio witness for the strict expectation comparison. [Condition](docs/SOURCE_CLARIFICATIONS.md#strictness-and-candidate-domain-readings). |
| Lemmas 2–3, 5–8 | **Exact.** |
| Appendix B counterexamples and smoothing | **Exact.** |
| Gumbel RUM / Plackett–Luce identification | **Scale clarified:** unit-variance noise rescales accuracy by $\pi/\sqrt6$. The specialization uses the standard Gumbel variance identity as an analytic premise. [Details](docs/SOURCE_CLARIFICATIONS.md#noise-normalizations-and-ranking-laws). |
| Plackett–Luce strategy comparison and zero monoculture effect | **Exact.** |

## 5. Remaining Boundaries and Gaps

No selected named theorem remains uncredited. The source's broad finite-support
and simulation remarks are not stated as unrestricted theorem claims; their
scope is described in the [source note](docs/SOURCE_CLARIFICATIONS.md#representation-boundaries).

## 6. Additional Assumptions Beyond Paper

- **Equation (6) regularity:** the current crossing endpoint states ranking-atom
  continuity, differentiability, and convergence for every value profile,
  whereas the source model uses its ordered support. Necessity of this
  total-family extension is unresolved. [Details](docs/SOURCE_CLARIFICATIONS.md#representation-boundaries).
- **Theorem 2 outer-$D$ regularity:** the source states the result for any
  candidate distribution, while the checked endpoint requires ordered support,
  finite first moments, measurable ranking probabilities, and well-defined
  conditional and payoff expectations. [Details](docs/SOURCE_CLARIFICATIONS.md#representation-boundaries).

## 7. Proof-Strategy Deviations

Appendix C.1's derivative-to-limit step is replaced by direct strict comparisons
for Laplace and Gaussian noise. The Gaussian and Mallows proofs also use local
algebra fixes; see the [precise changes](docs/SOURCE_CLARIFICATIONS.md#appendix-algebra-and-sequential-experiments).

## 8. Proof Tricks Worth Reusing

None.

## 9. Generalizations, Conjectures, and Extensions

No additional generalization is established here.

## 10. Source Clarifications and Exact Readings

The table links the density, cardinality, strictness, Gumbel-scale, and
Theorem 1 source-domain readings.
The [sequential-experiment note](docs/SOURCE_CLARIFICATIONS.md#appendix-algebra-and-sequential-experiments)
states Theorem 4's source-domain reading. Proof-only changes are in Section 7.


## 11. Paper Issues or Caveats

See the result-specific clarifications in Section 4 and the explicit
Equation (6) regularity extension in Section 6.

## 12. Detailed Formalization Evidence

The source map retains 49 selected result routes and nine source-model rows,
including Definitions 1--4, Theorems 1--9, Lemmas 1--8, and the corrected
Appendix-C comparison. The current source-to-Spec ledger reuses the unchanged
routes and includes the direct outer-law Theorem 1 endpoint.
Supporting formulas and experiments are not counted as extra named theorems.

## 13. Paper Assumption Provenance

Section 6 records the total-family Equation (6) extension and Theorem 2's
outer-$D$ regularity. The density and candidate-count clarifications are
distinguished from ordinary source-model conditions in Section 4. The current
scoped graph records its paper-local and library prerequisites in the
[paper](FINAL_CLOSURE_RECEIPT.md) and
[library](FINAL_CLOSURE_RECEIPT.md) ledgers.

## 14. Displayed Formula Provenance

[The source map](audit/paper_statement_map.json) binds the ranking laws,
expected welfare comparisons, sequential experiments, Laplace and Gaussian
likelihood calculations, and Mallows normalization. The
[source memo](docs/SOURCE_CLARIFICATIONS.md) and
[Laplace note](docs/LAPLACIAN_SOURCE_CLARIFICATION.md) give the corrected local
formulas and inequality domains.

## 15. Library Lift Pass

The selected reusable surface consists of finite ranking, probability,
expectation, and order-comparison infrastructure. Paper-specific hiring
experiments, noise families, theorem numbering, and corrected formula bundles
remain paper-local.

## 16. DAG Audit

[The dependency DAG](docs/DependencyDAG.pdf) groups the population-ranking,
welfare, sequential-experiment, Laplace, Gaussian, and Mallows routes. Theorem 1
is a formalized consequence of the source model and Definitions 1--3. The
current one-page rendering has readable labels and arrows and no page clipping.

## 17. Validation Checks

An independent source-to-Spec review checks the direct Theorem 1 route together
with the unchanged selected routes. The focused build and final closure receipt
record the corresponding proof and import-closure checks.

## 18. Paper Definitions Checked

Checked definitions include the source ranking systems and quality/noise
models, candidate pools, fresh-ranking hiring experiment, welfare and
selection probabilities, and the Laplace, Gaussian, and Mallows families.

## 19. Named Theorem Statements Checked

- Theorems 1--6: the monoculture paradox, welfare examples, strict loss for at
  least three candidates,
  sequential experiments, and the density-regularity result.
- Theorems 7--9: Laplace, Gaussian, and Mallows comparisons with the exact
  formula readings in Section 4.
- Lemmas 1--8 and Appendix C Lemma 1: the supporting probability, derivative,
  strictness, and weak-global/strict-overlap comparisons.

- Selected unnumbered claims: Appendix B counterexamples and smoothing,
  Gumbel–Plackett–Luce identification, and the Plackett–Luce strategic comparisons.

## 20. Paper-Facing Statement Validator Ledger

Direct comparisons are in the [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md),
row-level checks in the [statement ledger](FINAL_CLOSURE_RECEIPT.md), and
correction provenance in [source-proof fidelity](FINAL_CLOSURE_RECEIPT.md).

## 21. Source-Coverage Audit Ledger

The [source map](audit/paper_statement_map.json) retains 49 selected result
routes and nine source-model rows, including the direct outer-law Theorem 1
route. The [source-to-Spec ledger](FINAL_CLOSURE_RECEIPT.md)
binds that current surface. These are structural scope records; the closure
receipt supplies the separate accepted proof basis.
